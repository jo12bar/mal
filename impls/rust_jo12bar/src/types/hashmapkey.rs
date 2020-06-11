use super::{Atom, Error, Expr};
use std::{
    convert::{TryFrom, TryInto},
    fmt,
};

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

impl TryFrom<Atom> for HashMapKey {
    type Error = Error;

    fn try_from(atom: Atom) -> Result<Self, Self::Error> {
        match atom {
            Atom::Str(s) => Ok(Self::Str(s)),
            Atom::Keyword(k) => Ok(Self::Keyword(k)),
            Atom::Int(i) => Ok(Self::Int(i)),
            Atom::Sym(s) => Ok(Self::Sym(s)),
            other_atom_type => Err(Error::Str(format!(
                "Cannot use {:?} as a hash-map key!",
                other_atom_type
            ))),
        }
    }
}

impl TryFrom<Expr> for HashMapKey {
    type Error = Error;

    fn try_from(expr: Expr) -> Result<Self, Self::Error> {
        match expr {
            Expr::Constant(atom) => atom.try_into(),
            other_expr_type => Err(Error::Str(format!(
                "Cannot use {:?} as a hash-map key!",
                other_expr_type,
            ))),
        }
    }
}

impl fmt::Display for HashMapKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Str(s) => write!(f, "\"{}\"", s),
            Self::Keyword(k) => write!(f, ":{}", k),
            Self::Int(i) => i.fmt(f),
            Self::Sym(sym) => write!(f, "{}", sym),
        }
    }
}
