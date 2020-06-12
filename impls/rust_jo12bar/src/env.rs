//! Contains structs and methods and types for working with MAL environments.

use crate::types::{Error, Expr, HashMapKey};
use std::collections::HashMap;
use std::sync::{Arc, RwLock, Weak};

/// A Lisp (or MAL) environment. Contains a `HashMap<HashMapKey, Expr>` for
/// mapping things to values, and a way to get to the parent `Env`.
///
/// This is just the underlying struct. You should usually call `env_new()` to
/// get an `Env`, not a `EnvStruct`.
#[derive(Debug)]
pub struct EnvStruct {
    /// A `HashMap` from `HashMapKey`s (usually `HashMapKey::Sym`s) to `Expr`s.
    /// Holds the data present in the MAL environment.
    data: RwLock<HashMap<HashMapKey, Expr>>,

    /// The `Env` that this `Env` exists within. Set to `None` if this is a
    /// top-level `Env`.
    pub outer: Option<Weak<EnvStruct>>,
}

/// A MAL environment. Basically just a `EnvStruct` wrapped in a `Rc`.
/// Use the `env_new()` function to create a new one.
pub type Env = Arc<EnvStruct>;

/// Create a new, empty MAL environment.
pub fn env_new(outer: Option<Env>) -> Env {
    Arc::new(EnvStruct {
        data: RwLock::new(HashMap::default()),
        outer: outer.map(|e| Arc::downgrade(&e)),
    })
}

/// Create a new, empty MAL environment with an initial capacity for its
/// underlying `HashMap`. This helps avoid some allocations if you know from the
/// beginning how many items you need in the environment.
pub fn env_with_capacity(capacity: usize, outer: Option<Env>) -> Env {
    Arc::new(EnvStruct {
        data: RwLock::new(HashMap::with_capacity(capacity)),
        outer: outer.map(|e| Arc::downgrade(&e)),
    })
}

/// Creates a new MAL environment from an iterator.
pub fn env_from_iter<T: IntoIterator<Item = (HashMapKey, Expr)>>(
    iter: T,
    outer: Option<Env>,
) -> Env {
    use std::iter::FromIterator;

    Arc::new(EnvStruct {
        data: RwLock::new(HashMap::from_iter(iter)),
        outer: outer.map(|e| Arc::downgrade(&e)),
    })
}

/// Creates a new Env.
/// Binds a list of HashMapKey's to corresponding Expr's.
/// Meant to be used for things like binding function arguments during the apply
/// stage.
///
/// `is_variadic` should only be true if the second-to-last param is the symbol
/// `&`. This makes it so that the final symbol in the list will be a `List(..)`
/// of all the `args` that don't match up with named params. Useful for variadic
/// functions.
pub fn env_bind(
    params: Vec<HashMapKey>,
    args: Vec<Expr>,
    is_variadic: bool,
    outer: Option<Env>,
) -> Result<Env, Box<dyn std::error::Error>> {
    let n_positional_args = if is_variadic {
        params.len() - 2
    } else {
        params.len()
    };

    // First, argument length check.
    if !is_variadic && (args.len() != n_positional_args) {
        return Err(Error::s(format!(
            "env_bind: Expected {} arguments to be bound to parameters, found {}",
            n_positional_args,
            args.len(),
        )));
    } else if is_variadic && (args.len() < n_positional_args) {
        return Err(Error::s(format!(
            "env_bind: Expected at least {} arguments to be bound to parameters, found {}",
            n_positional_args,
            args.len(),
        )));
    }

    // Then, create a new `Env` with `outer` as the parent:
    let env = env_new(outer);

    // We loop through the non-var_args first:
    // Bind each non-var_arg argument in `args` to each key in `params`,
    // in succession:
    for i in 0..n_positional_args {
        env_set(&env, params[i].clone(), args[i].clone());
    }

    // If this param list has a final var_arg:
    if is_variadic {
        // ...then bind all the rest of the args to it in a Expr::List.
        env_set(
            &env,
            params.last().unwrap().clone(),
            Expr::List(args[n_positional_args..].to_vec()),
        );
    }

    // Return the new Env:
    Ok(env)
}

/// Sets a key in the underlying `data` hash-map to some `Expr`. The reference
/// to the passed-in `Env` is returned, for convenience.
pub fn env_set(env: &Env, k: HashMapKey, v: Expr) -> &Env {
    {
        let mut data = env.data.write().unwrap();
        data.insert(k, v);
    }
    env
}

/// Gets a key from the `Env`'s underlying `data` hash-map. If the key is
/// not found, and the `Env`'s `outer` reference is not `None`, then
/// `outer.get()` will be called and returned. If `outer` **is** `None`,
/// then `None` will be returned.
pub fn env_get(env: &Env, k: &HashMapKey) -> Option<Expr> {
    if let Some(expr) = env.data.read().unwrap().get(k) {
        Some(expr.clone())
    } else if let Some(outer_env) = &env.outer {
        env_get(&outer_env.upgrade().unwrap(), k)
    } else {
        None
    }
}

/// Finds the environment that contains a key, and returns a reference to it.
/// If no environment contains the key, then `None` is returned.
pub fn env_find(env: &Env, k: &HashMapKey) -> Option<Env> {
    if env.data.read().unwrap().contains_key(k) {
        Some(env.clone())
    } else if let Some(outer_env) = &env.outer {
        env_find(&outer_env.upgrade().unwrap(), k)
    } else {
        None
    }
}
