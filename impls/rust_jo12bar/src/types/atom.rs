use super::{Expr, ExprResult, HashMapKey};
use crate::env::Env;
use std::{
    convert::From,
    fmt,
    sync::{Arc, RwLock, Weak},
};

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

    /// A simple function. Does not support tail call optimization.
    /// Mainly for internal use.
    Func(Arc<dyn Fn(Vec<Expr>) -> ExprResult + Send + Sync>),

    /// A function that supports tail call optimization.
    ///
    /// Named `FnStar` because it is mainly meant to be generated by users
    /// through the `(fn* (<PARAMETERS>) <BODY>)` syntax.
    FnStar {
        /// The body of the `fn*`.
        ///
        /// NOTE: This is called `ast` in the MAL process guide.
        body: Arc<Expr>,

        /// A vector of `HashMapKey::Sym(..)`'s to be used as the `fn*`'s
        /// parameter names.
        params: Vec<HashMapKey>,

        /// > `env`: The current value of the `env` parameter of `EVAL`.
        env: Weak<Env>,

        /// Whether or not the `fn*` is variadic.
        is_variadic: bool,

        /// Whether or not the function is a macro. Macros have the ability to
        /// modify MAL AST.
        is_macro: bool,

        /// The function to evaluate the function body with.
        /// The first parameter will be `body`, and the second will be `env`.
        eval: Arc<dyn Fn(Expr, &Arc<Env>) -> ExprResult + Send + Sync>,
    },

    /// Yes, the naming is kinda bad, but this is a MAL Atom, which is a way to
    /// represent *state*. It is heavily inspired by
    /// [Clojure's Atoms](https://clojure.org/about/state).
    ///
    /// An atom holds a mutable shared reference to an `Expr` of any type. The
    /// reference can be cloned, read, or modified to point at another `Expr`,
    /// but (importantly!) the underlying `Expr` is immutable.
    Atom(Arc<RwLock<Expr>>),
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
            (Self::FnStar { .. }, Self::FnStar { .. }) => false,

            // Two references to expressions cannot equal each other. This is
            // is mostly a limitation of using a RwLock, but the MAL spec also
            // doesn't make any gaurantees about reference equality.
            (Self::Atom(..), Self::Atom(..)) => false,

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

            Self::FnStar { params, body, .. } => write!(
                f,
                "(fn* ({}) {})",
                params
                    .iter()
                    .map(|hmk| format!("{}", hmk))
                    .collect::<Vec<_>>()
                    .join(" "),
                body
            ),

            Self::Atom(a) => write!(
                f,
                "(atom {})",
                a.read()
                    .expect("Failed to read from Atom::Atom; RwLock poisoned.")
            ),
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
                "Func(Arc<dyn Fn(Vec<Expr>) -> ExprResult + Send + Sync> at {:p})",
                *func
            ),

            Self::FnStar {
                body,
                params,
                eval,
                env,
                is_variadic,
                is_macro,
            } => f
                .debug_struct("FnStar")
                .field("body", body)
                .field("params", params)
                .field("is_variadic", is_variadic)
                .field("is_macro", is_macro)
                .field("env", env)
                .field(
                    "eval",
                    &format!(
                        "Arc<dyn Fn(Expr, Env) -> ExprResult + Send + Sync> at {:p}",
                        *eval
                    ),
                )
                .finish(),

            Self::Atom(a) => write!(f, "Atom({:?})", a),
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
