//! Contains core MAL functions to be used by an interpreter, REPL, etc...

use crate::types::{Atom, Error, Expr, HashMapKey as HMK};
use lazy_static::lazy_static;

/// This generates a function that tells you if a `Expr` is a certain type.
/// You give it a pattern to match, and the closure will return true if the `Expr`
/// matches the pattern.
#[macro_export]
macro_rules! mal_expr_is_type {
    ($($patterns:pat),* $(,)?) => {{
        use $crate::types::{Expr, Atom};

        |args: Vec<Expr>| {
            let arg0 = args.get(0).unwrap_or(&Expr::Constant(Atom::Nil));
            Ok(Expr::Constant(Atom::Bool(match arg0 {
                $($patterns => true,)*
                _ => false,
            })))
        }
    }};

    ($pattern:pat if $condition:expr) => {{
        use $crate::types::{Expr, Atom};

        |args: Vec<Expr>| {
            let arg0 = args.get(0).unwrap_or(&Expr::Constant(Atom::Nil));
            Ok(Expr::Constant(Atom::Bool(match arg0 {
                $pattern if $condition => true,
                _ => false,
            })))
        }
    }};

    ($pattern:pat if $condition:expr, $($additional_patterns:pat),* $(,)?) => {{
        use $crate::types::{Expr, Atom};

        |args: Vec<Expr>| {
            let arg0 = args.get(0).unwrap_or(&Expr::Constant(Atom::Nil));
            Ok(Expr::Constant(Atom::Bool(match arg0 {
                $pattern if $condition => true,
                $($additional_patterns => true,)*
                _ => false,
            })))
        }
    }};
}

/// This represents a two-argument `Expr::Constant(Atom::Int)` **OR**
/// `Expr::Constant(Atom::Float)` operation.
///
/// `int_op` and `float_op` will usually do the same thing, but for typing
/// reasons you may have to explicitly rewrite them twice.
pub fn binary_num_op(
    int_op: impl Fn(i64, i64) -> i64,
    float_op: impl Fn(f64, f64) -> f64,
    args: Vec<Expr>,
) -> Result<Expr, Error> {
    if args.len() != 2 {
        return Err(Error::Str(format!(
            "Wrong number of arguments given to binary integer operator.\n\
             Expected 2 arguments, found {}.",
            args.len()
        )));
    }

    match (&args[0], &args[1]) {
        (Expr::Constant(Atom::Int(a)), Expr::Constant(Atom::Int(b))) => {
            Ok(Expr::Constant(Atom::Int(int_op(*a, *b))))
        }

        (Expr::Constant(Atom::Float(a)), Expr::Constant(Atom::Float(b))) => {
            Ok(Expr::Constant(Atom::Float(float_op(*a, *b))))
        }

        _ => Err(Error::Str(
            "Arguments passed to binary numeric operator are of invalid type.".to_string(),
        )),
    }
}

/// A binary operator. Checks for the existance of two parameters, and no more,
/// and errors out if there are more.
///
/// - `$fn_name` should be something that implements `ToString`.
/// - `$fn` should implement `Fn(&Expr, &Expr) -> Result<Expr, Error>`.
#[macro_export]
macro_rules! mal_bin_op {
    ($fn_name:expr, $fn:expr $(,)?) => {{
        use $crate::types::{Error, Expr, HashMapKey};

        (
            HashMapKey::Sym($fn_name.to_string()),
            Expr::func(|args: Vec<Expr>| -> Result<Expr, Error> {
                if args.len() != 2 {
                    return Err(Error::Str(format!(
                        "{}: Expected 2 arguments, found {}",
                        $fn_name,
                        args.len(),
                    )));
                }

                $fn(&args[0], &args[1])
            }),
        )
    }};
}

/// This is a convenience macro for using `crate::core::binary_num_op`.
///
/// It returns a closure that implements
///
/// ```ignore
/// Fn(Vec<Expr>) -> Result<Expr, Error>
/// ```
///
/// The passed-in closure is copied to both the `int_op` and `float_op`
/// arguments of `binary_num_op`. So, the below two closures should be equivalent:
///
/// ```
/// # #[macro_use] extern crate mal_rust_jo12bar;
/// # use mal_rust_jo12bar::core::binary_num_op;
/// # use mal_rust_jo12bar::types::{Expr, Error};
/// # fn main() {
/// let closure_1 = |args: Vec<Expr>| -> Result<Expr, Error> {
///     binary_num_op(|a, b| a + b, |a, b| a + b, args)
/// };
///
/// let closure_2 = mal_bin_num_op!(|a, b| a + b);
/// # }
/// ```
///
/// It also support a second form which is basically `mal_bin_op!` except that
/// it also checks that the two arguments are numeric and of the same type.
#[macro_export]
macro_rules! mal_bin_num_op {
    ($func:expr) => {
        |args: Vec<$crate::types::Expr>| -> Result<$crate::types::Expr, $crate::types::Error> {
            $crate::core::binary_num_op($func, $func, args)
        }
    };

    ($fn_name:expr, $fn:expr $(,)?) => {{
        use $crate::types::Atom;

        $crate::mal_bin_op!($fn_name, |a, b| {
            match (a, b) {
                (&Expr::Constant(Atom::Int(a)), &Expr::Constant(Atom::Int(b))) => $fn(a, b),
                (&Expr::Constant(Atom::Float(a)), &Expr::Constant(Atom::Float(b))) => $fn(a, b),

                (&Expr::Constant(Atom::Float(_)), &Expr::Constant(Atom::Int(_)))
                | (&Expr::Constant(Atom::Int(_)), &Expr::Constant(Atom::Float(_))) => {
                    Err(Error::Str(format!(
                        "{}: {} and {} have incompatible types with each other",
                        $fn_name, a, b,
                    )))
                }

                _ => Err(Error::Str(format!(
                    "{}: Expected two floats or two ints, found {} and {}",
                    $fn_name, a, b,
                ))),
            }
        })
    }};
}

/// Call `pr_str` on each argument with `print_readably` set to true.
/// Join them together with a space.
/// Return the new `Atom::Str`.
fn pr_str(args: Vec<Expr>) -> Result<Expr, Error> {
    Ok(Expr::Constant(Atom::Str(
        args.into_iter()
            .map(|arg| arg.pr_str(true))
            .collect::<Vec<_>>()
            .join(" "),
    )))
}

/// Calls `pr_str` on each argument with `print_readably` set to false,
/// concatenates the results together, and returns the new `Atom::Str`.
///
/// This should be called `str`, but it's called `str_fn` for name-conflict
/// reasons :-)
fn str_fn(args: Vec<Expr>) -> Result<Expr, Error> {
    Ok(Expr::Constant(Atom::Str(
        args.into_iter()
            .map(|arg| arg.pr_str(false))
            .collect::<Vec<_>>()
            .join(""),
    )))
}

/// Call `pr_str` on each argument with `print_readably` set to true.
/// Join them together with a space.
/// Print the result to the screen, and then return `Stom::Nil`.
fn prn(args: Vec<Expr>) -> Result<Expr, Error> {
    println!(
        "{}",
        args.into_iter()
            .map(|arg| arg.pr_str(true))
            .collect::<Vec<_>>()
            .join(" ")
    );

    Ok(Expr::Constant(Atom::Nil))
}

/// Calls `pr_str` on each argument with `print_readably` set to false, joins
/// the results with a space, prints the string to the screen, and then returns
/// `Atom::Nil`.
///
/// Should be called `println`, but naming conflicts are a thing :-)
fn println_fn(args: Vec<Expr>) -> Result<Expr, Error> {
    println!(
        "{}",
        args.into_iter()
            .map(|arg| arg.pr_str(false))
            .collect::<Vec<_>>()
            .join(" ")
    );

    Ok(Expr::Constant(Atom::Nil))
}

/// Just a convenience function for making a `HashMapKey::Sym(String)`.
macro_rules! hkm {
    ($string:expr) => {
        HMK::Sym($string.to_string())
    };
}

lazy_static! {
    /// The core MAL namespace. Includes all the symbols and their bindings that
    /// should be added to the root `Env` (i.e. via `env_from_iterator(..)`).
    pub static ref NS: Vec<(HMK, Expr)> = vec![
        // Binary numerical operators:
        (hkm!("+"), Expr::func(mal_bin_num_op!(|a, b| a + b))),
        (hkm!("-"), Expr::func(mal_bin_num_op!(|a, b| a - b))),
        (hkm!("*"), Expr::func(mal_bin_num_op!(|a, b| a * b))),
        (hkm!("/"), Expr::func(mal_bin_num_op!(|a, b| a / b))),

        // Type-checking functions:
        (hkm!("num?"), Expr::func(mal_expr_is_type!(
            Expr::Constant(Atom::Int(..)),
            Expr::Constant(Atom::Float(..)),
        ))),
        (hkm!("int?"), Expr::func(mal_expr_is_type!(Expr::Constant(Atom::Int(..))))),
        (hkm!("float?"), Expr::func(mal_expr_is_type!(Expr::Constant(Atom::Float(..))))),
        (hkm!("nil?"), Expr::func(mal_expr_is_type!(Expr::Constant(Atom::Nil)))),
        (hkm!("symbol?"), Expr::func(mal_expr_is_type!(Expr::Constant(Atom::Sym(..))))),
        (hkm!("keyword?"), Expr::func(mal_expr_is_type!(Expr::Constant(Atom::Keyword(..))))),
        (hkm!("str?"), Expr::func(mal_expr_is_type!(Expr::Constant(Atom::Str(..))))),
        (hkm!("fn?"), Expr::func(mal_expr_is_type!(Expr::Constant(Atom::Func(..))))),
        (hkm!("constant?"), Expr::func(mal_expr_is_type!(Expr::Constant(..)))),
        (hkm!("list?"), Expr::func(mal_expr_is_type!(Expr::List(..)))),
        (hkm!("vec?"), Expr::func(mal_expr_is_type!(Expr::Vec(..)))),
        (hkm!("hash?"), Expr::func(mal_expr_is_type!(Expr::HashMap(..)))),

        // Printing functions:
        (hkm!("pr-str"), Expr::func(pr_str)),
        (hkm!("str"), Expr::func(str_fn)),
        (hkm!("prn"), Expr::func(prn)),
        (hkm!("println"), Expr::func(println_fn)),

        // List functions:
        (hkm!("list"), Expr::func(|args| Ok(Expr::List(args)))),

        // Collection functions (i.e. lists, vecs, and hashmaps)
        (hkm!("empty?"), Expr::func(|args| {
            args.get(0).unwrap_or(&Expr::Constant(Atom::Nil)).is_empty()
        })),
        (hkm!("count"), Expr::func(|args| {
            args.get(0).unwrap_or(&Expr::Constant(Atom::Nil)).count()
        })),

        // Comparison functions:
        mal_bin_op!("=", |a, b| Ok(Expr::Constant(Atom::Bool(a == b)))),
        mal_bin_num_op!("<", |a, b| Ok(Expr::Constant(Atom::Bool(a < b)))),
        mal_bin_num_op!(">", |a, b| Ok(Expr::Constant(Atom::Bool(a > b)))),
        mal_bin_num_op!("<=", |a, b| Ok(Expr::Constant(Atom::Bool(a <= b)))),
        mal_bin_num_op!(">=", |a, b| Ok(Expr::Constant(Atom::Bool(a >= b)))),
    ];
}
