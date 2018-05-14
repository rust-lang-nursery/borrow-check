// Copyright 2017 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Timely dataflow runs on its own thread.

use crate::facts::{AllFacts, Loan, Point, Region};
use crate::output::{Output, OutputStatsLevel};
use differential_dataflow::collection::Collection;
use differential_dataflow::operators::arrange::{ArrangeByKey, ArrangeBySelf};
use differential_dataflow::operators::iterate::Variable;
use differential_dataflow::operators::*;
use std::collections::{BTreeMap, BTreeSet};
use std::mem;
use std::sync::mpsc;
use std::sync::Arc;
use std::sync::Mutex;
use timely;
use timely::dataflow::operators::*;
use timely::dataflow::Scope;

pub(super) fn compute(dump_enabled: bool, stats_level: Option<OutputStatsLevel>, mut all_facts: AllFacts) -> Output {
    // Declare that each universal region is live at every point.
    let all_points: BTreeSet<Point> = all_facts
        .cfg_edge
        .iter()
        .map(|&(p, _)| p)
        .chain(all_facts.cfg_edge.iter().map(|&(_, q)| q))
        .collect();

    for &r in &all_facts.universal_region {
        for &p in &all_points {
            all_facts.region_live_at.push((r, p));
        }
    }

    let result = Arc::new(Mutex::new(Output::new(dump_enabled)));

    // Use a channel to send `all_facts` to one worker (and only one)
    let (tx, rx) = mpsc::channel();
    tx.send(all_facts).unwrap();
    mem::drop(tx);
    let rx = Mutex::new(rx);

    let stats_enabled = stats_level.is_some();

    timely::execute_from_args(vec![].into_iter(), {
        let result = result.clone();
        move |worker| {
            // First come, first serve: one worker gets all the facts;
            // the others get empty vectors.
            let my_facts = rx.lock()
                .unwrap()
                .recv()
                .unwrap_or_else(|_| AllFacts::default());

            worker.dataflow::<(), _, _>(|scope| {
                macro_rules! let_collections {
                    (let ($($facts:ident,)*) = ..$base:expr;) => {
                        let ($($facts),*) = (
                            $(Collection::<_, _, isize>::new(
                                $base.$facts
                                    .to_stream(scope)
                                    .map(|datum| (datum, Default::default(), 1)),
                            ),)*
                        );
                    }
                }

                let verbose_stats_enabled = match stats_level {
                    Some(OutputStatsLevel::Precise) => true,
                    _ => false,
                };

                if stats_enabled {
                    println!("--------------------------------------------------");
                    println!("Input relations stats:");
                    println!("Point count: {}", all_points.len());
                    println!("Region count (incl. universal regions): {}\n",
                        my_facts.borrow_region.len() + my_facts.universal_region.len());

                    println!("'cfg_edge' tuple count: {}", my_facts.cfg_edge.len());
                    println!("'killed' tuple count: {}", my_facts.killed.len());
                    println!("'outlives' tuple count: {}", my_facts.outlives.len());
                    println!("'region_live_at' tuple count: {}", my_facts.region_live_at.len());
                    println!("'universal_region' tuple count: {}", my_facts.universal_region.len());

                    if verbose_stats_enabled {
                        println!("--------------------------------------------------");
                        println!("Timely computation stats:");
                    }
                }

                let_collections! {
                    let (
                        borrow_region,
                        cfg_edge,
                        killed,
                        outlives,
                        region_live_at,
                    ) = ..my_facts;
                }

                let cfg_edge = cfg_edge.arrange_by_key();
                let region_live_at_by_self = region_live_at.arrange_by_self();

                let (subset, requires) = scope.scoped(|subscope| {
                    macro_rules! dump_timely_stats {
                        ($e:ident) => {
                            $e
                                .map(|_| ())
                                .consolidate()
                                .inspect(|x| println!("'{}' - round {}, new facts: {:?}", stringify!($e), x.1.inner, x.2));
                        };
                    }

                    let outlives = outlives.enter(&subscope);
                    let cfg_edge = cfg_edge.enter(&subscope);
                    let region_live_at = region_live_at.enter(&subscope);
                    let region_live_at_by_self = region_live_at_by_self.enter(&subscope);
                    let borrow_region = borrow_region.enter(&subscope);
                    let killed = killed.enter(&subscope);

                    // .decl subset(R1, R2, P)
                    //
                    // At the point P, R1 <= R2.
                    //
                    // subset(R1, R2, P) :- outlives(R1, R2, P).
                    let subset = Variable::from(Collection::new(
                        None::<((Region, Region, Point), _, _)>
                            .into_iter()
                            .to_stream(subscope),
                    ));
                    let subset0 = outlives.clone();

                    // .decl requires(R, B, P) -- at the point, things with region R
                    // may depend on data from borrow B
                    //
                    // requires(R, B, P) :- borrow_region(R, B, P).
                    let requires = Variable::from(Collection::new(
                        None::<((Region, Loan, Point), _, _)>
                            .into_iter()
                            .to_stream(subscope),
                    ));
                    let requires0 = borrow_region.clone();

                    // .decl live_to_dead_regions(R1, R2, P, Q)
                    //
                    // The regions `R1` and `R2` are "live to dead"
                    // on the edge `P -> Q` if:
                    //
                    // - In P, `R1` <= `R2`
                    // - In Q, `R1` is live but `R2` is dead.
                    //
                    // In that case, `Q` would like to add all the
                    // live things reachable from `R2` to `R1`.
                    //
                    // live_to_dead_regions(R1, R2, P, Q) :-
                    //   subset(R1, R2, P),
                    //   cfg_edge(P, Q),
                    //   region_live_at(R1, Q),
                    //   !region_live_at(R2, Q).
                    let live_to_dead_regions = {
                        subset
                            .map(|(r1, r2, p)| (p, (r1, r2)))
                            .join_core(&cfg_edge, |&p, &(r1, r2), &q| Some(((r1, q), (r2, p))))
                            .join_core(&region_live_at_by_self, |&k, &v, _| Some((k, v)))
                            .map(|((r1, q), (r2, p))| ((r2, q), (r1, p)))
                            .antijoin(&region_live_at)
                            .map(|((r2, q), (r1, p))| (r1, r2, p, q))
                    };

                    if verbose_stats_enabled {
                        dump_timely_stats!(live_to_dead_regions);
                    }

                    // .decl dead_region_requires(R, B, P, Q)
                    //
                    // The region `R` requires the borrow `B`, but the
                    // region `R` goes dead along the edge `P -> Q`
                    //
                    // dead_region_requires(R, B, P, Q) :-
                    //   requires(R, B, P),
                    //   !killed(B, P),
                    //   cfg_edge(P, Q),
                    //   !region_live_at(R, Q).
                    let dead_region_requires = {
                        requires
                            .map(|(r, b, p)| ((b, p), r))
                            .antijoin(&killed)
                            .map(|((b, p), r)| (p, (r, b)))
                            .join_core(&cfg_edge, |&p, &(r, b), &q| Some(((r, q), (b, p))))
                            .antijoin(&region_live_at)
                            .map(|((r, q), (b, p))| (r, b, p, q))
                    };

                    if verbose_stats_enabled {
                        dump_timely_stats!(dead_region_requires);
                    }

                    // .decl dead_can_reach_origins(R, P, Q)
                    //
                    // Contains dead regions where we are interested
                    // in computing the transitive closure of things they
                    // can reach.
                    let dead_can_reach_origins = {
                        let dead_can_reach_origins0 =
                            { live_to_dead_regions.map(|(_r1, r2, p, q)| ((r2, p), q)) };
                        let dead_can_reach_origins1 =
                            { dead_region_requires.map(|(r, _b, p, q)| ((r, p), q)) };
                        dead_can_reach_origins0
                            .concat(&dead_can_reach_origins1)
                            .distinct_total()
                    };

                    if verbose_stats_enabled {
                        dump_timely_stats!(dead_can_reach_origins);
                    }

                    // .decl dead_can_reach(R1, R2, P, Q)
                    //
                    // Indicates that the region `R1`, which is dead
                    // in `Q`, can reach the region `R2` in P.
                    //
                    // This is effectively the transitive subset
                    // relation, but we try to limit it to regions
                    // that are dying on the edge P -> Q.
                    //
                    // NB. As a micro-optimization, `dead_can_reach`
                    // is stored as `dead_can_reach((R2, Q), (R1,
                    // P))`, since that happens to be the ordering
                    // that is required for the joins it participates
                    // in.
                    let dead_can_reach = {
                        let dead_can_reach = Variable::from(Collection::new(
                            None::<(((Region, Point), (Region, Point)), _, _)>
                                .into_iter()
                                .to_stream(subscope),
                        ));

                        // dead_can_reach(R1, R2, P, Q) :-
                        //   dead_can_reach_origins(R1, P, Q),
                        //   subset(R1, R2, P).
                        let dead_can_reach0 = {
                            dead_can_reach_origins.join_map(
                                &subset.map(|(r1, r2, p)| ((r1, p), r2)),
                                |&(r1, p), &q, &r2| ((r2, q), (r1, p)),
                            )
                        };

                        // dead_can_reach(R1, R3, P, Q) :-
                        //   dead_can_reach(R1, R2, P, Q),
                        //   !region_live_at(R2, Q),
                        //   subset(R2, R3, P).
                        //
                        // This is the "transitive closure" rule, but
                        // note that we only apply it with the
                        // "intermediate" region R2 is dead at Q.
                        let dead_can_reach1 = {
                            dead_can_reach
                                .antijoin(&region_live_at)
                                .map(|((r2, q), (r1, p))| ((r2, p), (r1, q)))
                                .join_map(
                                    &subset.map(|(r2, r3, p)| ((r2, p), r3)),
                                    |&(_r2, p), &(r1, q), &r3| ((r3, q), (r1, p)),
                                )
                        };

                        dead_can_reach
                            .set(&dead_can_reach0.concat(&dead_can_reach1).distinct_total())
                    };

                    if verbose_stats_enabled {
                        dump_timely_stats!(dead_can_reach);
                    }

                    // .decl dead_can_reach_live(R1, R2, P, Q)
                    //
                    // Indicates that, along the edge `P -> Q`, the
                    // dead (in Q) region R1 can reach the live (in Q)
                    // region R2 via a subset relation. This is a
                    // subset of the full `dead_can_reach` relation
                    // where we filter down to those cases where R2 is
                    // live in Q.
                    //
                    // NB. As a micro-optimization,
                    // `dead_can_reach_live` is stored as `((r1, p,
                    // q), r2)` since that happens to be the ordering
                    // required for the joins that it participates in.
                    let dead_can_reach_live = {
                        let dead_can_reach_live = dead_can_reach
                            .join_core(&region_live_at_by_self, |&k, &v, _| Some((k, v)))
                            .map(|((r2, q), (r1, p))| ((r1, p, q), r2));

                        if verbose_stats_enabled {
                            dump_timely_stats!(dead_can_reach_live);
                        }

                        dead_can_reach_live.arrange_by_key()
                    };

                    // subset(R1, R2, Q) :-
                    //   subset(R1, R2, P) :-
                    //   cfg_edge(P, Q),
                    //   region_live_at(R1, Q),
                    //   region_live_at(R2, Q).
                    //
                    // Carry `R1 <= R2` from P into Q if both `R1` and
                    // `R2` are live in Q.
                    let subset1 = subset
                        .map(|(r1, r2, p)| (p, (r1, r2)))
                        .join_core(&cfg_edge, |_p, &(r1, r2), &q| Some(((r1, q), r2)))
                        .join_core(&region_live_at_by_self, |&k, &v, _| Some((k, v)))
                        .map(|((r1, q), r2)| ((r2, q), r1))
                        .join_core(&region_live_at_by_self, |&k, &v, _| Some((k, v)))
                        .map(|((r2, q), r1)| (r1, r2, q));

                    // subset(R1, R3, Q) :-
                    //   live_to_dead_regions(R1, R2, P, Q),
                    //   dead_can_reach_live(R2, R3, P, Q).
                    let subset2 = {
                        live_to_dead_regions
                            .map(|(r1, r2, p, q)| ((r2, p, q), r1))
                            .join_core(&dead_can_reach_live, |&(_r2, _p, q), &r1, &r3| {
                                Some((r1, r3, q))
                            })
                    };

                    // requires(R2, B, Q) :-
                    //   dead_region_requires(R1, B, P, Q),
                    //   dead_can_reach_live(R1, R2, P, Q).
                    //
                    // Communicate a `R1 requires B` relation across
                    // an edge `P -> Q` where `R1` is dead in Q; in
                    // that case, for each region `R2` live in `Q`
                    // where `R1 <= R2` in P, we add `R2 requires B`
                    // to `Q`.
                    let requires1 = dead_region_requires
                        .map(|(r1, b, p, q)| ((r1, p, q), b))
                        .join_core(&dead_can_reach_live, |&(_r1, _p, q), &b, &r2| {
                            Some((r2, b, q))
                        });

                    // requires(R, B, Q) :-
                    //   requires(R, B, P),
                    //   !killed(B, P),
                    //   cfg_edge(P, Q),
                    //   region_live_at(R, Q).
                    let requires2 = requires
                        .map(|(r, b, p)| ((b, p), r))
                        .antijoin(&killed)
                        .map(|((b, p), r)| (p, (r, b)))
                        .join_core(&cfg_edge, |&_p, &(r, b), &q| Some(((r, q), b)))
                        .join_core(&region_live_at_by_self, |&k, &v, _| Some((k, v)))
                        .map(|((r, q), b)| (r, b, q));

                    let requires = requires.set(&requires0
                        .concat(&requires1)
                        .concat(&requires2)
                        .distinct_total());

                    let subset_before_distinct = subset0.concat(&subset1).concat(&subset2);
                    if verbose_stats_enabled {
                        dump_timely_stats!(subset_before_distinct);
                    }

                    let subset =
                        subset.set(&subset_before_distinct.distinct_total());
                    if verbose_stats_enabled {
                        dump_timely_stats!(subset);
                    }

                    (subset.leave(), requires.leave())
                });

                // .decl borrow_live_at(B, P) -- true if the restrictions of the borrow B
                // need to be enforced at the point P
                let borrow_live_at = {
                    // borrow_live_at(B, P) :- requires(R, B, P), region_live_at(R, P)
                    let borrow_live_at1 = requires
                        .map(|(r, b, p)| ((r, p), b))
                        .join_core(&region_live_at_by_self, |&k, &v, _| Some((k, v)))
                        .map(|((_r, p), b)| (b, p));

                    borrow_live_at1.distinct_total()
                };

                if stats_enabled {
                    subset
                        .map(|_| ())
                        .consolidate()
                        .inspect(|x| {
                            println!("--------------------------------------------------");
                            println!("Main relations stats:");
                            println!("'subset' final tuple count: {:?}", x.2);
                        });

                    requires
                        .map(|_| ())
                        .consolidate()
                        .inspect(|x| println!("'requires' final tuple count: {:?}", x.2));

                    borrow_live_at
                        .map(|_| ())
                        .consolidate()
                        .inspect(|x| {
                            println!("--------------------------------------------------");
                            println!("Output stats:");
                            println!("'borrow_live_at' final tuple count: {:?}", x.2);
                        });
                }

                if dump_enabled {
                    region_live_at.inspect_batch({
                        let result = result.clone();
                        move |_timestamp, facts| {
                            let mut result = result.lock().unwrap();
                            for ((region, location), _timestamp, multiplicity) in facts {
                                assert_eq!(*multiplicity, 1);
                                result
                                    .region_live_at
                                    .entry(*location)
                                    .or_insert(vec![])
                                    .push(*region);
                            }
                        }
                    });

                    subset.inspect_batch({
                        let result = result.clone();
                        move |_timestamp, facts| {
                            let mut result = result.lock().unwrap();
                            for ((r1, r2, location), _timestamp, multiplicity) in facts {
                                assert_eq!(*multiplicity, 1);
                                result
                                    .subset
                                    .entry(*location)
                                    .or_insert(BTreeMap::new())
                                    .entry(*r1)
                                    .or_insert(BTreeSet::new())
                                    .insert(*r2);
                                result.region_degrees.update_degrees(*r1, *r2, *location);
                            }
                        }
                    });

                    requires.inspect_batch({
                        let result = result.clone();
                        move |_timestamp, facts| {
                            let mut result = result.lock().unwrap();
                            for ((region, borrow, location), _timestamp, multiplicity) in facts {
                                assert_eq!(*multiplicity, 1);
                                result
                                    .restricts
                                    .entry(*location)
                                    .or_insert(BTreeMap::new())
                                    .entry(*region)
                                    .or_insert(BTreeSet::new())
                                    .insert(*borrow);
                            }
                        }
                    });
                }

                borrow_live_at.inspect_batch({
                    let result = result.clone();
                    move |_timestamp, facts| {
                        let mut result = result.lock().unwrap();
                        for ((borrow, location), _timestamp, multiplicity) in facts {
                            assert_eq!(*multiplicity, 1);
                            result
                                .borrow_live_at
                                .entry(*location)
                                .or_insert(Vec::new())
                                .push(*borrow);
                        }
                    }
                });
            });
        }
    }).unwrap();

    // Remove from the Arc and Mutex, since it is fully populated now.
    Arc::try_unwrap(result)
        .unwrap_or_else(|_| panic!("somebody still has a handle to this arc"))
        .into_inner()
        .unwrap()
}
