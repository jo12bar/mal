use super::{Expr, ExprResult, HashMapKey};
use std::{convert::From, fmt, sync::Arc};

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

impl fmt::Display for Atom {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
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

impl fmt::Debug for Atom {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
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
                "Func(Rc<dyn Fn(Vec<Expr>) -> ExprResult> at {:p})",
                *func
            ),
        }
    }
}

impl From<HashMapKey> for Atom {
    fn from(hmk: HashMapKey) -> Self {
        match hmk {
            HashMapKey::Str(s) => Self::Str(s),
            HashMapKey::Keyword(kwd) => Self::Keyword(kwd),
            HashMapKey::Int(i) => Self::Int(i),
            HashMapKey::Sym(sym) => Self::Sym(sym),
        }
    }
}
