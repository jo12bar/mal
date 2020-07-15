//! Contains core MAL functions to be used by an interpreter, REPL, etc...

use crate::{
    reader,
    types::{Atom, Error, Expr, ExprResult, HashMapKey as HMK},
};
use std::{fs::File, io::prelude::*, path::Path};

/// Allows you to check that a function call receives some fixed number of
/// arguments. Returns an error if it doesn't.
#[macro_export]
macro_rules! mal_arg_length_check {
    ($fn_name:expr, $num_args:expr, $args:expr $(,)?) => {{
        use $crate::types::Error;

        if $args.len() != $num_args {
            return Err(Error::s(format!(
                "{}: Expected {} arguments, found {}",
                $fn_name,
                $num_args,
                $args.len(),
            )));
        }
    }};
}

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
) -> ExprResult {
    if args.len() != 2 {
        return Err(Error::s(format!(
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

        _ => Err(Error::s(
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
        use $crate::types::{Error, Expr, ExprResult, HashMapKey};

        (
            HashMapKey::Sym($fn_name.to_string()),
            Expr::func(|args: Vec<Expr>| -> ExprResult {
                if args.len() != 2 {
                    return Err(Error::s(format!(
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
/// # use mal_rust_jo12bar::types::{Expr, ExprResult};
/// # fn main() {
/// let closure_1 = |args: Vec<Expr>| -> ExprResult {
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
        |args: Vec<$crate::types::Expr>| -> $crate::types::ExprResult {
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
                    Err(Error::s(format!(
                        "{}: {} and {} have incompatible types with each other",
                        $fn_name, a, b,
                    )))
                }

                _ => Err(Error::s(format!(
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
fn pr_str(args: Vec<Expr>) -> ExprResult {
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
fn str_fn(args: Vec<Expr>) -> ExprResult {
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
fn prn(args: Vec<Expr>) -> ExprResult {
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
fn println_fn(args: Vec<Expr>) -> ExprResult {
    println!(
        "{}",
        args.into_iter()
            .map(|arg| arg.pr_str(false))
            .collect::<Vec<_>>()
            .join(" ")
    );

    Ok(Expr::Constant(Atom::Nil))
}

/// Just exposes the `reader::read_str` function.
fn read_string(args: Vec<Expr>) -> ExprResult {
    mal_arg_length_check!("read-str", 1, args);

    match &args[0] {
        Expr::Constant(Atom::Str(s)) => reader::read_str(s),

        e => {
            return Err(Error::s(format!(
                "read-str: Expected string paramter, found {}",
                e
            )))
        }
    }
}

/// Takes a file name (string) and returns the contents of the file as a string.
fn slurp(args: Vec<Expr>) -> ExprResult {
    mal_arg_length_check!("slurp", 1, args);

    if let Expr::Constant(Atom::Str(s)) = &args[0] {
        let path = Path::new(s);
        let display = path.display();

        // Open file:
        let mut file = match File::open(&path) {
            Ok(file) => file,
            Err(why) => {
                return Err(Error::s(format!(
                    "slurp: Could not open {}: {}",
                    display, why,
                )));
            }
        };

        // Read into String buffer:
        let mut buf = String::new();
        match file.read_to_string(&mut buf) {
            Ok(_) => {}
            Err(why) => {
                return Err(Error::s(format!(
                    "slurp: Could not read {}: {}",
                    display, why
                )))
            }
        }

        // Return it!
        Ok(Expr::Constant(Atom::Str(buf)))
    } else {
        return Err(Error::s(format!(
            "read-str: Expected string parameter, found {}",
            &args[0],
        )));
    }
}

/// Wraps an Expr in a Atom::Atom.
fn atom(args: Vec<Expr>) -> ExprResult {
    mal_arg_length_check!("atom", 1, args);
    Ok(Expr::atom(&args[0]))
}

/// Attempts to deref a Atom::Atom.
fn deref(args: Vec<Expr>) -> ExprResult {
    mal_arg_length_check!("deref", 1, args);
    args[0].deref()
}

/// Sets a Atom::Atom to point to some other expression.
fn reset_bang(args: Vec<Expr>) -> ExprResult {
    mal_arg_length_check!("reset!", 2, args);

    let atom = &args[0];
    let expr = &args[1];

    atom.atom_reset(expr.clone())
}

/// Maps a Atom::Atom to a new Atom::Atom given a function, and returns the value.
fn swap_bang(args: Vec<Expr>) -> ExprResult {
    // There should be *at least* two args: the atom and the function. Anything
    // after that will be extra arguments passed to the function.
    if args.len() < 2 {
        return Err(Error::s(format!(
            "swap!: Expected at least 2 arguments, found {}",
            args.len()
        )));
    }

    let atom = &args[0];
    let func = &args[1];
    let func_args = &args[2..];

    atom.atom_swap(func, func_args)
}

/// Prepends a list with some value.
fn cons(args: Vec<Expr>) -> ExprResult {
    // Expect 2 args:
    mal_arg_length_check!("cons", 2, args);

    match &args[1] {
        Expr::List(v) | Expr::Vec(v) => {
            let mut new_vec = vec![args[0].clone()];
            new_vec.extend_from_slice(v);
            Ok(Expr::List(new_vec))
        }

        e => Err(Error::s(format!(
            "cons: Expected list or vector, found {}",
            e
        ))),
    }
}

/// Concatenates together a bunch of lists and vectors into a single list.
fn concat(args: Vec<Expr>) -> ExprResult {
    let mut new_vec = vec![];

    for arg in args.iter() {
        match arg {
            Expr::List(v) | Expr::Vec(v) => {
                new_vec.extend_from_slice(v);
            }

            e => {
                return Err(Error::s(format!(
                    "concat: Expected list or vector, found {}",
                    e
                )));
            }
        }
    }

    Ok(Expr::List(new_vec))
}

/// Returns the element of a list at a given index.
///
/// # Usage:
///
/// ```ignore
/// (nth [1 2 3] 1)
/// ; => 2
/// ```
fn nth(args: Vec<Expr>) -> ExprResult {
    // Need 2 args:
    mal_arg_length_check!("nth", 2, args);

    match &args[0] {
        Expr::List(v) | Expr::Vec(v) => match &args[1] {
            Expr::Constant(Atom::Int(i)) => match v.get(*i as usize) {
                Some(el) => Ok(el.clone()),

                None => Err(Error::s(format!(
                    "nth: Index out of bounds. {} items, but index {} was requested.",
                    v.len(),
                    i,
                ))),
            },

            e => Err(Error::s(format!("nth: Expected integer, found {}", e))),
        },

        e => Err(Error::s(format!(
            "nth: Expected list or vector, found {}",
            e
        ))),
    }
}

/// Returns the first element in a list or vector. Returns `nil` if the list/
/// vector is empty.
///
/// # Usage
///
/// ```ignore
/// (first [1 2 3])
/// ; => 1
/// ```
fn first(args: Vec<Expr>) -> ExprResult {
    mal_arg_length_check!("first", 1, args);

    match &args[0] {
        Expr::List(v) | Expr::Vec(v) => match v.first() {
            Some(expr) => Ok(expr.clone()),
            None => Ok(Expr::Constant(Atom::Nil)),
        },

        Expr::Constant(Atom::Nil) => Ok(Expr::Constant(Atom::Nil)),

        e => Err(Error::s(format!(
            "first: Expected list or vector or nil, found {}",
            e
        ))),
    }
}

/// Returns a new list containing all elements *except* the first one in a list
/// or vector. Returns `()` if the list/ vector is empty, or if `nil` is passed in.
///
/// # Usage
///
/// ```ignore
/// (first [1 2 3])
/// ; => (2 3)
/// ```
fn rest(args: Vec<Expr>) -> ExprResult {
    mal_arg_length_check!("rest", 1, args);

    match &args[0] {
        Expr::List(v) | Expr::Vec(v) => {
            if v.is_empty() {
                Ok(Expr::List(vec![]))
            } else {
                Ok(Expr::List(v[1..].to_vec()))
            }
        }

        Expr::Constant(Atom::Nil) => Ok(Expr::List(vec![])),

        e => Err(Error::s(format!(
            "rest: Expected list or vector or nil, found {}",
            e
        ))),
    }
}

/// Just a convenience function for making a `HashMapKey::Sym(String)`.
macro_rules! hkm {
    ($string:expr) => {
        HMK::Sym($string.to_string())
    };
}

/// The core MAL namespace. Includes all the symbols and their bindings that
/// should be added to the root `Env` (i.e. via `env_from_iterator(..)`).
///
/// If you're only loading this namespace once, then this function should be
/// preferred over the lazy static `NS` that also exists in this module.
pub fn get_ns() -> Vec<(HMK, Expr)> {
    vec![
        // Binary numerical operators:
        (hkm!("+"), Expr::func(mal_bin_num_op!(|a, b| a + b))),
        (hkm!("-"), Expr::func(mal_bin_num_op!(|a, b| a - b))),
        (hkm!("*"), Expr::func(mal_bin_num_op!(|a, b| a * b))),
        (hkm!("/"), Expr::func(mal_bin_num_op!(|a, b| a / b))),
        // Type-checking functions:
        (
            hkm!("num?"),
            Expr::func(mal_expr_is_type!(
                Expr::Constant(Atom::Int(..)),
                Expr::Constant(Atom::Float(..)),
            )),
        ),
        (
            hkm!("int?"),
            Expr::func(mal_expr_is_type!(Expr::Constant(Atom::Int(..)))),
        ),
        (
            hkm!("float?"),
            Expr::func(mal_expr_is_type!(Expr::Constant(Atom::Float(..)))),
        ),
        (
            hkm!("nil?"),
            Expr::func(mal_expr_is_type!(Expr::Constant(Atom::Nil))),
        ),
        (
            hkm!("symbol?"),
            Expr::func(mal_expr_is_type!(Expr::Constant(Atom::Sym(..)))),
        ),
        (
            hkm!("keyword?"),
            Expr::func(mal_expr_is_type!(Expr::Constant(Atom::Keyword(..)))),
        ),
        (
            hkm!("str?"),
            Expr::func(mal_expr_is_type!(Expr::Constant(Atom::Str(..)))),
        ),
        (
            hkm!("fn?"),
            Expr::func(mal_expr_is_type!(
                Expr::Constant(Atom::Func(..)),
                Expr::Constant(Atom::FnStar { .. })
            )),
        ),
        (
            hkm!("constant?"),
            Expr::func(mal_expr_is_type!(Expr::Constant(..))),
        ),
        (hkm!("list?"), Expr::func(mal_expr_is_type!(Expr::List(..)))),
        (hkm!("vec?"), Expr::func(mal_expr_is_type!(Expr::Vec(..)))),
        (
            hkm!("hash?"),
            Expr::func(mal_expr_is_type!(Expr::HashMap(..))),
        ),
        (
            hkm!("atom?"),
            Expr::func(mal_expr_is_type!(Expr::Constant(Atom::Atom(..)))),
        ),
        // Printing functions:
        (hkm!("pr-str"), Expr::func(pr_str)),
        (hkm!("str"), Expr::func(str_fn)),
        (hkm!("prn"), Expr::func(prn)),
        (hkm!("println"), Expr::func(println_fn)),
        // List functions:
        (hkm!("list"), Expr::func(|args| Ok(Expr::List(args)))),
        (hkm!("cons"), Expr::func(cons)),
        (hkm!("concat"), Expr::func(concat)),
        (hkm!("nth"), Expr::func(nth)),
        (hkm!("first"), Expr::func(first)),
        (hkm!("rest"), Expr::func(rest)),
        // Collection functions (i.e. lists, vecs, and hashmaps)
        (
            hkm!("empty?"),
            Expr::func(|args| args.get(0).unwrap_or(&Expr::Constant(Atom::Nil)).is_empty()),
        ),
        (
            hkm!("count"),
            Expr::func(|args| args.get(0).unwrap_or(&Expr::Constant(Atom::Nil)).count()),
        ),
        // Atom-related functions:
        (hkm!("atom"), Expr::func(atom)),
        (hkm!("deref"), Expr::func(deref)),
        (hkm!("reset!"), Expr::func(reset_bang)),
        (hkm!("swap!"), Expr::func(swap_bang)),
        // Comparison functions:
        mal_bin_op!("=", |a, b| Ok(Expr::Constant(Atom::Bool(a == b)))),
        mal_bin_num_op!("<", |a, b| Ok(Expr::Constant(Atom::Bool(a < b)))),
        mal_bin_num_op!(">", |a, b| Ok(Expr::Constant(Atom::Bool(a > b)))),
        mal_bin_num_op!("<=", |a, b| Ok(Expr::Constant(Atom::Bool(a <= b)))),
        mal_bin_num_op!(">=", |a, b| Ok(Expr::Constant(Atom::Bool(a >= b)))),
        // Evalutation-related functions:
        (hkm!("read-string"), Expr::func(read_string)),
        (hkm!("slurp"), Expr::func(slurp)),
    ]
}
