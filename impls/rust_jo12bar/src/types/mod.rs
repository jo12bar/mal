//! MAL types.

pub mod atom;
pub mod error;
pub mod expr;
pub mod hashmapkey;

pub use atom::Atom;
pub use error::Error;
pub use expr::Expr;
pub use hashmapkey::HashMapKey;

/// A convenience type for expressing `Result<Expr, Box<dyn std::error::Error>>`.
///
/// Note that the `Error` enum in this module *happens* to implement `std::error::Error`.
pub type ExprResult = Result<Expr, Box<dyn std::error::Error>>;
