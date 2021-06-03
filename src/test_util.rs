#![cfg(test)]

use polonius_engine::{Algorithm, AllFacts, Output};
use std::fmt::Debug;

use crate::facts::LocalFacts;
use crate::intern::InternerTables;
use crate::program::parse_from_program;

/// Test that two values are equal, with a better error than `assert_eq`
pub fn assert_equal<A>(expected_value: &A, actual_value: &A)
where
    A: ?Sized + Debug + Eq,
{
    // First check that they have the same debug text. This produces a better error.
    let expected_text = format!("{:#?}", expected_value);
    assert_expected_debug(&expected_text, actual_value);

    // Then check that they are `eq` too, for good measure.
    assert_eq!(expected_value, actual_value);
}

/// Test that the debug output of `actual_value` is as expected. Gives
/// a nice diff if things fail.
pub fn assert_expected_debug<A>(expected_text: &str, actual_value: &A)
where
    A: ?Sized + Debug,
{
    let actual_text = format!("{:#?}", actual_value);

    if expected_text == actual_text {
        return;
    }

    println!("# expected_text");
    println!("{}", expected_text);

    println!("# actual_text");
    println!("{}", actual_text);

    println!("# diff");
    for diff in diff::lines(&expected_text, &actual_text) {
        match diff {
            diff::Result::Left(l) => println!("-{}", l),
            diff::Result::Both(l, _) => println!(" {}", l),
            diff::Result::Right(r) => println!("+{}", r),
        }
    }

    panic!("debug comparison failed");
}

/// Builder for fact checking assertions
pub(crate) struct FactChecker {
    pub facts: AllFacts<LocalFacts>,
    pub output: Output<LocalFacts>,
    pub tables: InternerTables,
}

/// Will create a `FactChecker` fact-checking builder, containing methods for checking
/// the atoms contained in the `Output` relations.
pub(crate) fn check_program(
    program: &str,
    algorithm: Algorithm,
    dump_enabled: bool,
) -> FactChecker {
    let mut tables = InternerTables::new();
    let facts = parse_from_program(program, &mut tables).expect("Parsing failure");

    let output = Output::compute(&facts, algorithm, dump_enabled);
    FactChecker {
        facts,
        output,
        tables,
    }
}

pub(crate) fn naive_checker_for(program: &str) -> FactChecker {
    check_program(program, Algorithm::Naive, true)
}

pub(crate) fn location_insensitive_checker_for(program: &str) -> FactChecker {
    check_program(program, Algorithm::LocationInsensitive, true)
}

pub(crate) fn opt_checker_for(program: &str) -> FactChecker {
    check_program(program, Algorithm::DatafrogOpt, true)
}

pub(crate) fn assert_checkers_match(checker_a: &FactChecker, checker_b: &FactChecker) {
    assert_outputs_match(&checker_a.output, &checker_b.output);
}

pub(crate) fn assert_outputs_match(output_a: &Output<LocalFacts>, output_b: &Output<LocalFacts>) {
    assert_equal(&output_a.errors, &output_b.errors);
    assert_equal(&output_a.subset_errors, &output_b.subset_errors);
    assert_equal(&output_a.move_errors, &output_b.move_errors);
}

impl FactChecker {
    /// Asserts that there is a `subset_error` `origin1: origin2` at the specified `point`.
    pub fn subset_error_exists(&mut self, origin1: &str, origin2: &str, point: &str) -> bool {
        let point = self.tables.points.intern(point);
        let subset_errors = self
            .output
            .subset_errors
            .get(&point)
            .expect("No subset errors found at this point");

        let origin1 = self.tables.origins.intern(origin1);
        let origin2 = self.tables.origins.intern(origin2);
        subset_errors.contains(&(origin1, origin2))
    }

    /// Asserts that there is a `subset_error` `origin1: origin2`.
    /// The location of the subset error is ignored.
    pub fn location_insensitive_subset_error_exists(
        &mut self,
        origin1: &str,
        origin2: &str,
    ) -> bool {
        // Location-insensitive subset errors are wrapped at a single meaningless point
        assert_eq!(self.output.subset_errors.len(), 1);

        let subset_errors = self
            .output
            .subset_errors
            .values()
            .next()
            .expect("No subset errors found");

        let origin1 = self.tables.origins.intern(origin1);
        let origin2 = self.tables.origins.intern(origin2);
        subset_errors.contains(&(origin1, origin2))
    }

    /// The number of undeclared relationships causing subset errors.
    /// Note that this is different from checking `output.subset_errors.len()` as subset errors are
    /// grouped by the location where they are detected.
    pub fn subset_errors_count(&self) -> usize {
        self.output
            .subset_errors
            .values()
            .map(|origins| origins.len())
            .sum()
    }
}
