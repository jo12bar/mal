use super::{Atom, Error, ExprResult, HashMapKey};
use std::{cmp::PartialEq, collections::HashMap, convert::From, fmt, sync::Arc};

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

impl PartialEq for Expr {
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

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
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

impl From<HashMapKey> for Expr {
    fn from(hmk: HashMapKey) -> Self {
        match hmk {
            HashMapKey::Int(i) => Self::Constant(Atom::Int(i)),
            HashMapKey::Keyword(k) => Self::Constant(Atom::Keyword(k)),
            HashMapKey::Str(s) => Self::Constant(Atom::Str(s)),
            HashMapKey::Sym(s) => Self::Constant(Atom::Sym(s)),
        }
    }
}
