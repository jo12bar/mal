//! MAL types.

use std::collections::HashMap;
use std::rc::Rc;

/// Some error types.
#[derive(PartialEq, Clone, Debug)]
pub enum Error<'a> {
    /// For errors where the message is some arbritrary `String`.
    Str(String),
    /// For errors where the message is to involve an `Atom`.
    Atom(Atom<'a>),
}

impl std::fmt::Display for Error<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Str(s) => s.fmt(f),
            Self::Atom(a) => a.fmt(f),
        }
    }
}

/// Primitive values.
#[derive(Clone)]
pub enum Atom<'a> {
    Nil,
    Str(String),
    Bool(bool),
    Int(i64),
    Float(f64),
    Sym(String),
    Keyword(String),

    /// First field is the function itself, while the second field can be used
    /// for its name.
    Func(Rc<dyn Fn(Vec<Expr>) -> Result<Expr, Error> + 'a>),
}

impl PartialEq for Atom<'_> {
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

impl std::fmt::Display for Atom<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Nil => write!(f, "nil"),
            Self::Str(s) => write!(f, "\"{}\"", s),
            Self::Bool(b) => b.fmt(f),
            Self::Int(i) => i.fmt(f),
            Self::Float(fl) => fl.fmt(f),
            Self::Sym(sym) => sym.fmt(f),
            Self::Keyword(kwd) => write!(f, ":{}", kwd),
            Self::Func(func) => write!(f, "#<fn at {:p}>", func),
        }
    }
}

impl std::fmt::Debug for Atom<'_> {
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
                func
            ),
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

impl std::convert::TryFrom<Atom<'_>> for HashMapKey {
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
#[derive(Debug, PartialEq, Clone)]
pub enum Expr<'a> {
    Comment,
    Constant(Atom<'a>),
    List(Vec<Expr<'a>>),
    Vec(Vec<Expr<'a>>),
    HashMap(HashMap<HashMapKey, Expr<'a>>),
}

impl<'a> Expr<'a> {
    /// A "reader macro." Wraps an `Expr` like this:
    ///
    /// | Input   | Output         |
    /// |:------- |:-------------- |
    /// | `'EXPR` | `(quote EXPR)` |
    pub fn quote(expr: Self) -> Self {
        Self::List(vec![Self::Constant(Atom::Sym("quote".to_string())), expr])
    }

    /// A "reader macro." Wraps an `Expr` like this:
    ///
    /// | Input       | Output              |
    /// |:----------- |:------------------- |
    /// | `` `EXPR `` | `(quasiquote EXPR)` |
    pub fn quasiquote(expr: Self) -> Self {
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
    pub fn unquote(expr: Self) -> Self {
        Self::List(vec![Self::Constant(Atom::Sym("unquote".to_string())), expr])
    }

    /// A "reader macro." Wraps an `Expr` like this:
    ///
    /// | Input    | Output                  |
    /// |:-------- |:----------------------- |
    /// | `~@EXPR` | `(splice-unquote EXPR)` |
    pub fn splice_unquote(expr: Self) -> Self {
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
    pub fn deref(expr: Self) -> Self {
        Self::List(vec![Self::Constant(Atom::Sym("deref".to_string())), expr])
    }

    /// A "reader macro." Wraps an `Expr` like this:
    ///
    /// | Input | Output |
    /// |:--- |:--- |
    /// | `^EXPR1 EXPR2` | `(with-meta EXPR2 EXPR1)` |
    pub fn with_meta(expr1: Self, expr2: Self) -> Self {
        Self::List(vec![
            Self::Constant(Atom::Sym("with-meta".to_string())),
            expr2,
            expr1,
        ])
    }

    /// Creates a new `Atom::Func` wrapped in a `Expr::Constant`.
    pub fn func<F>(f: F) -> Self
    where
        F: Fn(Vec<Expr>) -> Result<Expr, Error> + 'a,
    {
        Self::Constant(Atom::Func(Rc::new(f)))
    }

    /// Apply arguments to a function. Will return an `Error` if you attempt to
    /// call a non-function `Expr`.
    pub fn apply<'b>(&'a self, args: Vec<Expr<'b>>) -> Result<Expr<'b>, Error<'b>> {
        match self {
            Self::Constant(Atom::Func(f)) => f(args),

            _ => Err(Error::Str("Attempt to call a non-function!".to_string())),
        }
    }
}

impl std::fmt::Display for Expr<'_> {
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
