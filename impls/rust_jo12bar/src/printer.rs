//! Methods for outputting stuff.

use crate::types::Expr;

/// Prints an AST (i.e. an `Expr`) using its default `std::fmt::Display` impl.
pub fn pr_str(expr: Expr) {
    println!("{}", expr);
}
