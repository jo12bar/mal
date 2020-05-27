//! MAL types.

use std::collections::HashMap;

/// Primitive values.
#[derive(Debug, PartialEq, Clone)]
pub enum Atom {
    Nil,
    Str(String),
    Bool(bool),
    Int(i64),
    Float(f64),
    Sym(String),
    Keyword(String),
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
        }
    }
}

/// The possible types that can be used for `Expr::HashMap` keys.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum HashMapKey {
    Str(String),
    Keyword(String),
    Int(i64),
}

impl std::convert::TryFrom<Atom> for HashMapKey {
    type Error = String;

    fn try_from(atom: Atom) -> Result<Self, Self::Error> {
        match atom {
            Atom::Str(s) => Ok(Self::Str(s)),
            Atom::Keyword(k) => Ok(Self::Keyword(k)),
            Atom::Int(i) => Ok(Self::Int(i)),
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
        }
    }
}

/// An expression. Could just be a single `Atom`, or it could be something like
/// a list or a function invocation.
#[derive(Debug, PartialEq, Clone)]
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
