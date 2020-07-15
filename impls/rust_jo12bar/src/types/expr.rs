use super::{Atom, Error, ExprResult, HashMapKey};
use crate::env::Env;
use std::{
    cmp::PartialEq,
    collections::HashMap,
    convert::{From, TryFrom},
    fmt,
    sync::{Arc, RwLock, Weak},
};

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

    /// Creates a new `Atom::FnStar` wrapped in a `Expr::Constant`.
    pub fn fn_star(
        exprs: Vec<Self>,
        parent_env: &Arc<Env>,
        eval: impl Fn(Self, &Arc<Env>) -> ExprResult + Send + Sync + 'static,
    ) -> ExprResult {
        use HashMapKey as HMK;

        // There should be two expressions after a "fn*": the arguments list and the
        // function body.
        if exprs.len() != 3 {
            return Err(Error::s(format!(
                "fn*: Expected 2 expressions after a \'fn*\': the arguments list and the function body.\n\
                 Found {}",
                exprs.len() - 1,
            )));
        }

        // Double check that `exprs` starts with the symbol `fn*`:
        if !matches!(&exprs[0], Self::Constant(Atom::Sym(s)) if s == "fn*") {
            return Err(Error::s(
                "fn*: Expected a fn* definition to start with the symbol fn*.".to_string(),
            ));
        }

        let fn_argument_list = &exprs[1];
        let fn_body = exprs[2].clone();

        // fn_argument_list should literally be a `Expr::List` of symbols.
        let fn_argument_vec = match fn_argument_list {
            Expr::Vec(exprs) | Expr::List(exprs) => exprs,

            _ => {
                return Err(Error::s(format!(
                    "fn*: Expected a list of symbols as an argument list after a \'fn*\'.\n\
                     Found {}",
                    fn_argument_list,
                )));
            }
        };

        let fn_arg_names = fn_argument_vec
            .iter()
            // Each expression should be a Expr::Constant(Atom::Sym):
            .map(|expr| match expr {
                Expr::Constant(sym @ Atom::Sym(..)) => Ok(sym),
                _ => Err(format!(
                    "fn*: Expected a symbol in a fn* argument list, found {}",
                    expr
                )),
            });

        // If there were any non-symbols in the argument list, error out.
        if fn_arg_names.clone().any(|name| name.is_err()) {
            return Err(Error::s(
                fn_arg_names
                    .filter_map(|name| name.err())
                    .collect::<Vec<String>>()
                    .join("\n"),
            ));
        }

        // If there is a `&` symbol, then:
        // - There should only be one symbol after it
        // - That one symbol will be bound to all the rest of the arguments passed
        //   to the function that don't match up with preceding symbols.
        let has_var_arg = fn_arg_names
            .clone()
            .filter_map(|name| name.ok())
            .any(|name| name == &Atom::Sym("&".to_string()));

        // Pre-convert argument names to `HashMapKey`'s.
        let fn_arg_keys: Vec<HMK> = fn_arg_names
            .filter_map(|name| name.ok())
            .map(|sym| HMK::try_from(sym.clone()).unwrap())
            .collect();

        if has_var_arg {
            // There must only be one item after the '&':
            let ampersand_index = fn_arg_keys
                .iter()
                .position(|r| r == &HMK::Sym("&".to_string()))
                .unwrap();

            if fn_arg_keys[fn_arg_keys.len() - 2] != fn_arg_keys[ampersand_index] {
                return Err(Error::s(format!(
                    "fn*: Expected one symbol after the & in a fn* argument list, found {}",
                    fn_arg_keys[(ampersand_index)..].len() - 1
                )));
            }
        }

        // Create a new `Env` just for this function, so that the function can
        // keep a reference to the parent `Env` without creating a Arc-loop
        // (i.e. memory leak!).
        let fenv = Arc::new(Env::new());
        Env::add_child(parent_env, &fenv);

        // The parent `env` will keep an Arc<Env> for `fenv` alive for as long
        // as `env` is alive. So, it is safe for us to downgrade `fenv` into a
        // `Weak<Env>`.
        let fenv = Arc::downgrade(&fenv);

        // Return the final FnStar!
        Ok(Expr::Constant(Atom::FnStar {
            body: Arc::new(fn_body),
            params: fn_arg_keys,
            env: fenv,
            is_variadic: has_var_arg,
            is_macro: false,
            eval: Arc::new(eval),
        }))
    }

    /// Create a new `Expr::Constant(Atom::Atom(..))``.
    pub fn atom(expr: &Self) -> Self {
        Expr::Constant(Atom::Atom(Arc::new(RwLock::new(expr.clone()))))
    }

    /// Apply arguments to a function. Will return an `Error` if you attempt to
    /// call a non-function `Expr`.
    ///
    /// Note that tail-call optimization is not supported by this method.
    pub fn apply(&self, args: Vec<Expr>) -> ExprResult {
        match self {
            // Simple functions:
            Self::Constant(Atom::Func(f)) => f(args),

            // Functions that support tail-call optimization (though we don't do
            // that here):
            Self::Constant(Atom::FnStar {
                body,
                params,
                env,
                eval,
                is_variadic,
                ..
            }) => {
                let env =
                    Weak::upgrade(env).expect("apply: Could not upgrade weak reference to fn* env");

                // Drop any children that already exist in the envto avoid
                // accumulating a bunch of Arc's. This is fine as the children
                // can still access their parents, and will be kept alive by
                // Rust's call stack for as long as needed.
                while let Some(_) = env.pop_child() {}

                let func_env = Arc::new(Env::bind(params.clone(), args, *is_variadic)?);

                Env::add_child(&env, &func_env);

                eval(body.as_ref().clone(), &func_env)
            }

            _ => Err(Error::s("apply: Attempt to call a non-function!")),
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

    /// Attempts to dereference a `Atom::Atom`, copying and returning its data.
    pub fn deref(&self) -> ExprResult {
        match self {
            Self::Constant(Atom::Atom(a)) => Ok(a
                .read()
                .expect("deref: Could not read atom; Poisoned RwLock.")
                .clone()),

            _ => Err(Error::s(format!(
                "deref: invalid expression type; expected atom, got {}",
                self
            ))),
        }
    }

    /// Sets the `Expr` that a `Atom::Atom` points at to something else, and
    /// returns it.
    pub fn atom_reset(&self, expr: Self) -> ExprResult {
        if let Self::Constant(Atom::Atom(a)) = self {
            let mut internal_expr = a
                .write()
                .expect("reset!: Could not write to atom; Poisoned RwLock.");

            *internal_expr = expr.clone();

            Ok(expr)
        } else {
            Err(Error::s(format!(
                "reset!: invalid expression type; expected atom, got {}",
                self
            )))
        }
    }

    /// Applies a function, with optional arguments, to an `Atom::Atom`, and returns
    /// a new Atom containing the result.
    pub fn atom_swap(&self, func: &Self, func_args: &[Self]) -> ExprResult {
        if !matches!(self, Expr::Constant(Atom::Atom(..))) {
            return Err(Error::s(format!(
                "swap!: invalid expression type; expected atom, got {}",
                self
            )));
        }

        if !matches!(func, Expr::Constant(Atom::Func(..)) | Expr::Constant(Atom::FnStar { .. })) {
            return Err(Error::s(format!(
                "swap!: invalid expression type; expected func or fn*, got {}",
                func
            )));
        }

        // Pull the current value out of the Atom:
        let curr_val = self
            .deref()
            .map_err(|e| Error::s(format!("swap!: {}", e)))?;

        // Prepend it to the function arguments list:
        let func_args: Vec<_> = [curr_val].iter().chain(func_args).cloned().collect();

        // Apply the function to get the new value:
        let new_val = func
            .apply(func_args)
            .map_err(|e| Error::s(format!("swap!: {}", e)))?;

        // Set the Atom's value to the new value, and return the new value.
        self.atom_reset(new_val)
            .map_err(|e| Error::s(format!("swap!: {}", e)))
    }

    /// Returns `true` if this is a `Expr::Constant(Atom::FnStar { is_macro, .. })`,
    /// where `is_macro` is `true`. Returns `false` otherwise.
    pub fn is_macro_call(&self) -> bool {
        match self {
            Self::Constant(Atom::FnStar { is_macro, .. }) if *is_macro => true,

            _ => false,
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
