use crate::facts::AllFacts;
use crate::intern::{InternTo, InternerTables};
use log::error;
use std::fs::File;
use std::io::{self, prelude::*};
use std::path::Path;
use std::process;

trait FromTabDelimited<'input>: Sized {
    fn parse(
        tables: &mut InternerTables,
        inputs: &mut dyn Iterator<Item = &'input str>,
    ) -> Option<Self>;
}

pub(crate) fn load_tab_delimited_facts(
    tables: &mut InternerTables,
    facts_dir: &Path,
) -> io::Result<AllFacts> {
    macro_rules! load_facts {
        (from ($tables:expr, $facts_dir:expr) load AllFacts { $($t:ident,)* }) => {
            Ok(AllFacts {
                $(
                    $t: {
                        let filename = format!("{}.facts", stringify!($t));
                        let facts_file = $facts_dir.join(&filename);
                        load_tab_delimited_file($tables, &facts_file)?
                    },
                )*
            })
        }
    }

    load_facts! {
        from (tables, facts_dir) load AllFacts {
            loan_issued_at,
            universal_region,
            cfg_edge,
            loan_killed_at,
            subset_base,
            loan_invalidated_at,
            var_defined_at,
            var_used_at,
            var_dropped_at,
            use_of_var_derefs_origin,
            drop_of_var_derefs_origin,
            child_path,
            path_is_var,
            path_assigned_at_base,
            path_moved_at_base,
            path_accessed_at_base,
            known_placeholder_subset,
            placeholder,
        }
    }
}

fn load_tab_delimited_file<Row>(tables: &mut InternerTables, path: &Path) -> io::Result<Vec<Row>>
where
    Row: for<'input> FromTabDelimited<'input>,
{
    match File::open(path) {
        Ok(file) => io::BufReader::new(file)
            .lines()
            .enumerate()
            .map(|(index, line)| {
                let line = line?;
                let mut columns = line.split('\t');
                let row = match FromTabDelimited::parse(tables, &mut columns) {
                    None => {
                        error!("error parsing line {} of `{}`", index + 1, path.display());
                        process::exit(1);
                    }

                    Some(v) => v,
                };

                if columns.next().is_some() {
                    error!("extra data on line {} of `{}`", index + 1, path.display());
                    process::exit(1);
                }

                Ok(row)
            })
            .collect(),

        Err(e) => {
            panic!("Error opening file '{}': {}", path.display(), e);
        }
    }
}

impl<'input, T> FromTabDelimited<'input> for T
where
    &'input str: InternTo<T>,
{
    fn parse(
        tables: &mut InternerTables,
        inputs: &mut dyn Iterator<Item = &'input str>,
    ) -> Option<Self> {
        let input = inputs.next()?;
        Some(InternTo::intern(tables, input))
    }
}

impl<'input, A, B> FromTabDelimited<'input> for (A, B)
where
    A: FromTabDelimited<'input>,
    B: FromTabDelimited<'input>,
{
    fn parse(
        tables: &mut InternerTables,
        inputs: &mut dyn Iterator<Item = &'input str>,
    ) -> Option<Self> {
        let a = A::parse(tables, inputs)?;
        let b = B::parse(tables, inputs)?;
        Some((a, b))
    }
}

impl<'input, A, B, C> FromTabDelimited<'input> for (A, B, C)
where
    A: FromTabDelimited<'input>,
    B: FromTabDelimited<'input>,
    C: FromTabDelimited<'input>,
{
    fn parse(
        tables: &mut InternerTables,
        inputs: &mut dyn Iterator<Item = &'input str>,
    ) -> Option<Self> {
        let a = A::parse(tables, inputs)?;
        let b = B::parse(tables, inputs)?;
        let c = C::parse(tables, inputs)?;
        Some((a, b, c))
    }
}

impl<'input, A, B, C, D> FromTabDelimited<'input> for (A, B, C, D)
where
    A: FromTabDelimited<'input>,
    B: FromTabDelimited<'input>,
    C: FromTabDelimited<'input>,
    D: FromTabDelimited<'input>,
{
    fn parse(
        tables: &mut InternerTables,
        inputs: &mut dyn Iterator<Item = &'input str>,
    ) -> Option<Self> {
        let a = A::parse(tables, inputs)?;
        let b = B::parse(tables, inputs)?;
        let c = C::parse(tables, inputs)?;
        let d = D::parse(tables, inputs)?;
        Some((a, b, c, d))
    }
}
