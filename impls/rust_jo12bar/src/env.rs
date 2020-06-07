//! Contains structs and methods and types for working with MAL environments.

use crate::types::{Expr, HashMapKey};
use std::collections::HashMap;
use std::sync::{Arc, RwLock};

/// A Lisp (or MAL) environment. Contains a `HashMap<HashMapKey, Expr>` for
/// mapping things to values, and a way to get to the parent `Env`.
///
/// This is just the underlying struct. You should usually call `env_new()` to
/// get an `Env`, not a `EnvStruct`.
#[derive(Debug, Clone)]
pub struct EnvStruct {
    /// A `HashMap` from `HashMapKey`s (usually `HashMapKey::Sym`s) to `Expr`s.
    /// Holds the data present in the MAL environment.
    data: Arc<RwLock<HashMap<HashMapKey, Expr>>>,

    /// The `Env` that this `Env` exists within. Set to `None` if this is a
    /// top-level `Env`.
    pub outer: Option<Env>,
}

/// A MAL environment. Basically just a `EnvStruct` wrapped in a `Rc`.
/// Use the `env_new()` function to create a new one.
pub type Env = Arc<EnvStruct>;

/// Create a new, empty MAL environment.
pub fn env_new(outer: Option<Env>) -> Env {
    Arc::new(EnvStruct {
        data: Arc::new(RwLock::new(HashMap::default())),
        outer,
    })
}

/// Create a new, empty MAL environment with an initial capacity for its
/// underlying `HashMap`. This helps avoid some allocations if you know from the
/// beginning how many items you need in the environment.
pub fn env_with_capacity(capacity: usize, outer: Option<Env>) -> Env {
    Arc::new(EnvStruct {
        data: Arc::new(RwLock::new(HashMap::with_capacity(capacity))),
        outer,
    })
}

/// Creates a new MAL environment from an iterator.
pub fn env_from_iter<T: IntoIterator<Item = (HashMapKey, Expr)>>(
    iter: T,
    outer: Option<Env>,
) -> Env {
    use std::iter::FromIterator;

    Arc::new(EnvStruct {
        data: Arc::new(RwLock::new(HashMap::from_iter(iter))),
        outer,
    })
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
    } else if let Some(outer_env) = env.outer.clone() {
        env_get(&outer_env, k)
    } else {
        None
    }
}

/// Finds the environment that contains a key, and returns a reference to it.
/// If no environment contains the key, then `None` is returned.
pub fn env_find(env: &Env, k: &HashMapKey) -> Option<Env> {
    if env.data.read().unwrap().contains_key(k) {
        Some(env.clone())
    } else if let Some(outer_env) = env.outer.clone() {
        env_find(&outer_env, k)
    } else {
        None
    }
}
