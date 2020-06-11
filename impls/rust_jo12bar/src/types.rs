//! MAL types.

use std::collections::HashMap;
use std::sync::Arc;

/// Some error types.
#[derive(PartialEq, Clone, Debug)]
pub enum Error {
    /// For errors where the message is some arbritrary `String`.
    Str(String),
    /// For errors where the message is to involve an `Atom`.
    Atom(Atom),
}

impl Error {
    /// Create a `Box<Error>` with some arbritrary string.
    pub fn s<T: ToString>(message: T) -> Box<dyn std::error::Error> {
        Box::new(Self::Str(message.to_string()))
    }
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Self::Str(s) => s.fmt(f),
            Self::Atom(a) => a.fmt(f),
        }
    }
}

impl std::error::Error for Error {}

/// A convenience type for expressing `Result<Expr, Box<dyn std::error::Error>>`.
///
/// Note that the `Error` enum in this module *happens* to implement `std::error::Error`.
pub type ExprResult = Result<Expr, Box<dyn std::error::Error>>;

/// Primitive values.
#[derive(Clone)]
pub enum Atom {
    Nil,
    Str(String),
    Bool(bool),
    Int(i64),
    Float(f64),
    Sym(String),
    Keyword(String),

    /// First field is the function itself, while the second field can be used
    /// for its name.
    Func(Arc<dyn Fn(Vec<Expr>) -> ExprResult + Send + Sync>),
}

impl PartialEq for Atom {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Nil, Self::Nil) => true,
            (Self::Str(ref a), Self::Str(ref b)) => a == b,
            (Self::Bool(ref a), Self::Bool(ref b)) => a == b,
            (Self::Int(ref a), Self::Int(ref b)) => a == b,
            (Self::Float(ref a), Self::Float(ref b)) => a == b,
            (Self::Sym(ref a), Self::Sym(ref b)) => a == b,
            (Self::Keyword(ref a), Self::Keyword(ref b)) => a == b,

            // Two functions can never equal each other.
            (Self::Func(..), Self::Func(..)) => false,

            // Two atoms of differing typw cannot equal each other.
            _ => false,
        }
    }
}

impl std::fmt::Display for Atom {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Nil => write!(f, "nil"),
            Self::Str(s) => write!(f, "\"{}\"", s),
            Self::Bool(b) => b.fmt(f),
            Self::Int(i) => i.fmt(f),
            Self::Float(fl) => fl.fmt(f),
            Self::Sym(sym) => sym.fmt(f),
            Self::Keyword(kwd) => write!(f, ":{}", kwd),
            Self::Func(func) => write!(f, "#<function at {:p}>", *func),
        }
    }
}

impl std::fmt::Debug for Atom {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Nil => write!(f, "Nil"),
            Self::Str(s) => write!(f, "Str({:?})", s),
            Self::Bool(b) => write!(f, "Bool({:?})", b),
            Self::Int(i) => write!(f, "Int({:?})", i),
            Self::Float(fl) => write!(f, "Float({:?})", fl),
            Self::Sym(sym) => write!(f, "Sym({:?})", sym),
            Self::Keyword(kwd) => write!(f, "Keyword({:?})", kwd),
            Self::Func(func) => write!(
                f,
                "Func(Rc<dyn Fn(Vec<Expr>) -> Result<Expr, Error>> at {:p})",
                *func
            ),
        }
    }
}

impl std::convert::From<HashMapKey> for Atom {
    fn from(hmk: HashMapKey) -> Self {
        match hmk {
            HashMapKey::Str(s) => Self::Str(s),
            HashMapKey::Keyword(kwd) => Self::Keyword(kwd),
            HashMapKey::Int(i) => Self::Int(i),
            HashMapKey::Sym(sym) => Self::Sym(sym),
        }
    }
}

/// The possible types that can be used for `Expr::HashMap` keys.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum HashMapKey {
    Str(String),
    Keyword(String),
    Int(i64),
    /// Symbols as `HashMapKey`s should be for internal, non-user-accessible use
    /// only (i.e. not part of MAL itself).
    Sym(String),
}

impl std::convert::TryFrom<Atom> for HashMapKey {
    type Error = String;

    fn try_from(atom: Atom) -> Result<Self, Self::Error> {
        match atom {
            Atom::Str(s) => Ok(Self::Str(s)),
            Atom::Keyword(k) => Ok(Self::Keyword(k)),
            Atom::Int(i) => Ok(Self::Int(i)),
            Atom::Sym(s) => Ok(Self::Sym(s)),
            other_atom_type => Err(format!(
                "Cannot use {:?} as a hash-map key!",
                other_atom_type
            )),
        }
    }
}

impl std::fmt::Display for HashMapKey {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Str(s) => write!(f, "\"{}\"", s),
            Self::Keyword(k) => write!(f, ":{}", k),
            Self::Int(i) => i.fmt(f),
            Self::Sym(sym) => write!(f, "{}", sym),
        }
    }
}

/// An expression. Could just be a single `Atom`, or it could be something like
/// a list or a function invocation.
#[derive(Debug, Clone)]
pub enum Expr {
    Comment,
    Constant(Atom),
    List(Vec<Expr>),
    Vec(Vec<Expr>),
    HashMap(HashMap<HashMapKey, Expr>),
}

impl Expr {
    /// A "reader macro." Wraps an `Expr` like this:
    ///
    /// | Input   | Output         |
    /// |:------- |:-------------- |
    /// | `'EXPR` | `(quote EXPR)` |
    pub fn reader_macro_quote(expr: Self) -> Self {
        Self::List(vec![Self::Constant(Atom::Sym("quote".to_string())), expr])
    }

    /// A "reader macro." Wraps an `Expr` like this:
    ///
    /// | Input       | Output              |
    /// |:----------- |:------------------- |
    /// | `` `EXPR `` | `(quasiquote EXPR)` |
    pub fn reader_macro_quasiquote(expr: Self) -> Self {
        Self::List(vec![
            Self::Constant(Atom::Sym("quasiquote".to_string())),
            expr,
        ])
    }

    /// A "reader macro." Wraps an `Expr` like this:
    ///
    /// | Input   | Output           |
    /// |:------- |:---------------- |
    /// | `~EXPR` | `(unquote EXPR)` |
    pub fn reader_macro_unquote(expr: Self) -> Self {
        Self::List(vec![Self::Constant(Atom::Sym("unquote".to_string())), expr])
    }

    /// A "reader macro." Wraps an `Expr` like this:
    ///
    /// | Input    | Output                  |
    /// |:-------- |:----------------------- |
    /// | `~@EXPR` | `(splice-unquote EXPR)` |
    pub fn reader_macro_splice_unquote(expr: Self) -> Self {
        Self::List(vec![
            Self::Constant(Atom::Sym("splice-unquote".to_string())),
            expr,
        ])
    }

    /// A "reader macro." Wraps an `Expr` like this:
    ///
    /// | Input   | Output         |
    /// |:------- |:-------------- |
    /// | `@EXPR` | `(deref EXPR)` |
    pub fn reader_macro_deref(expr: Self) -> Self {
        Self::List(vec![Self::Constant(Atom::Sym("deref".to_string())), expr])
    }

    /// A "reader macro." Wraps an `Expr` like this:
    ///
    /// | Input | Output |
    /// |:--- |:--- |
    /// | `^EXPR1 EXPR2` | `(with-meta EXPR2 EXPR1)` |
    pub fn reader_macro_with_meta(expr1: Self, expr2: Self) -> Self {
        Self::List(vec![
            Self::Constant(Atom::Sym("with-meta".to_string())),
            expr2,
            expr1,
        ])
    }

    /// Creates a new `Atom::Func` wrapped in a `Expr::Constant`.
    pub fn func(f: impl Fn(Vec<Expr>) -> ExprResult + Send + Sync + 'static) -> Self {
        Self::Constant(Atom::Func(Arc::new(f)))
    }

    /// Apply arguments to a function. Will return an `Error` if you attempt to
    /// call a non-function `Expr`.
    pub fn apply(&self, args: Vec<Expr>) -> ExprResult {
        match self {
            Self::Constant(Atom::Func(f)) => f(args),

            _ => Err(Error::s("Attempt to call a non-function!")),
        }
    }

    /// Returns the count of items if this is a `Expr::List` or `Expr::Vec` or `Expr::HashMap`, `0`
    /// if this is a `Expr::Constant(Atom::Nil)`, and an error otherwise.
    pub fn count(&self) -> ExprResult {
        match self {
            Self::List(v) | Self::Vec(v) => Ok(Expr::Constant(Atom::Int(v.len() as i64))),
            Self::HashMap(hm) => Ok(Expr::Constant(Atom::Int(hm.len() as i64))),
            Self::Constant(Atom::Nil) => Ok(Expr::Constant(Atom::Int(0))),
            _ => Err(Error::s(format!(
                "count: invalid expression type; got {}",
                self
            ))),
        }
    }

    /// - If this is a `Expr::List` or a `Expr::Vec`, returns true if the underlying
    ///   vector is empty, and false otherwise.
    /// - If this is a `Expr::HashMap`, returns true if the underlying `HashMap`
    ///   is empty, and false otherwise.
    /// - If this is a `Expr::Constant(Atom::Nil)`, returns true.
    /// - Returns an error otherwise.
    pub fn is_empty(&self) -> ExprResult {
        match self {
            Self::List(v) | Self::Vec(v) => Ok(Expr::Constant(Atom::Bool(v.is_empty()))),
            Self::HashMap(hm) => Ok(Expr::Constant(Atom::Bool(hm.is_empty()))),
            Self::Constant(Atom::Nil) => Ok(Expr::Constant(Atom::Bool(true))),
            _ => Err(Error::s(format!(
                "empty?: invalid expression type; got {}",
                self
            ))),
        }
    }
}

impl std::cmp::PartialEq for Expr {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Comment, Self::Comment) => false,
            (Self::Constant(a), Self::Constant(b)) => a == b,
            (Self::HashMap(a), Self::HashMap(b)) => a == b,

            (Self::List(a), Self::List(b))
            | (Self::List(a), Self::Vec(b))
            | (Self::Vec(a), Self::List(b))
            | (Self::Vec(a), Self::Vec(b)) => a == b,

            _ => false,
        }
    }
}

impl std::fmt::Display for Expr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Comment => write!(f, ""),

            Self::Constant(atom) => atom.fmt(f),

            Self::List(list) => write!(
                f,
                "({})",
                list.iter()
                    .map(|expr| format!("{}", expr))
                    .collect::<Vec<_>>()
                    .join(" ")
            ),

            Self::Vec(v) => write!(
                f,
                "[{}]",
                v.iter()
                    .map(|expr| format!("{}", expr))
                    .collect::<Vec<_>>()
                    .join(" ")
            ),

            Self::HashMap(hmap) => write!(
                f,
                "{{{}}}",
                hmap.iter()
                    .map(|(key, value)| format!("{} {}", key, value))
                    .collect::<Vec<_>>()
                    .join(" ")
            ),
        }
    }
}
