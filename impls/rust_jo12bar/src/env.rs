//! Contains structs and methods and types for working with MAL environments.

use crate::types::{Error, Expr, HashMapKey};
use dashmap::DashMap;
use std::{
    iter::{Extend, FromIterator},
    sync::{Arc, RwLock, Weak},
};

/// A Lisp (or MAL) environment. Contains a `DashMap<HashMapKey, Expr>` for
/// mapping things to values, and a way to get to the parent `Env`.
///
/// Note that [`DashMap`](https://docs.rs/dashmap/3.11.4/dashmap/struct.DashMap.html)
/// is just a convenient, fast, concurrent version of a `RwLock<HashMap<..>>`.
///
/// Use the `Env::add_child(&parent_env, &child_env)` to add a child `Env` to a
/// parent. Note that this is an associated function, not a regular method.
#[derive(Debug, Clone)]
pub struct Env {
    /// A `HashMap` from `HashMapKey`s (usually `HashMapKey::Sym`s) to `Arc<Expr>`s.
    /// Holds the data present in the MAL environment.
    data: Arc<DashMap<HashMapKey, Arc<Expr>>>,

    /// The `Env` that this `Env` exists within.
    parent: Arc<RwLock<Weak<Env>>>,

    /// `Env`'s contained in this `Env`. Note that you can't actually search into
    /// inner `Env`'s to find some key - this is just for reference-counting's
    /// sake.
    children: Arc<RwLock<Vec<Arc<Env>>>>,
}

impl Env {
    /// Create a new, empty MAL environment.
    pub fn new() -> Self {
        Self {
            data: Arc::new(DashMap::new()),
            parent: Arc::new(RwLock::new(Weak::new())),
            children: Arc::new(RwLock::new(vec![])),
        }
    }

    /// Create a new, empty MAL environment with an initial capacity for its
    /// underlying `HashMap`. This helps avoid some allocations if you know from the
    /// beginning how many items you need in the environment.
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            data: Arc::new(DashMap::with_capacity(capacity)),
            parent: Arc::new(RwLock::new(Weak::new())),
            children: Arc::new(RwLock::new(vec![])),
        }
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
    pub fn bind(
        params: Vec<HashMapKey>,
        args: Vec<Expr>,
        is_variadic: bool,
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

        // Then, create a new `Env`.
        let env = Self::with_capacity(if is_variadic {
            n_positional_args + 1
        } else {
            n_positional_args
        });

        // We loop through the non-var_args first:
        // Bind each non-var_arg argument in `args` to each key in `params`,
        // in succession:
        for i in 0..n_positional_args {
            env.insert(params[i].clone(), Arc::new(args[i].clone()));
        }

        // If this param list has a final var_arg:
        if is_variadic {
            // ...then bind all the rest of the args to it in a Expr::List.
            env.insert(
                params.last().unwrap().clone(),
                Arc::new(Expr::List(args[n_positional_args..].to_vec())),
            );
        }

        // Return the new `Env`:
        Ok(env)
    }

    /// Sets a key in the underlying `data` hash-map to some `Expr`.
    pub fn insert(&self, key: HashMapKey, value: Arc<Expr>) -> Option<Arc<Expr>> {
        self.data.insert(key, value)
    }

    /// Gets a value from the underlying `data` hash-map, clones its `Arc`, and
    /// returns it.
    pub fn get(&self, key: &HashMapKey) -> Option<Arc<Expr>> {
        if let Some(v) = self.data.get(key) {
            Some(Arc::clone(&*v))
        } else if let Some(parent) = self.get_parent() {
            parent.get(key)
        } else {
            None
        }
    }

    /// Trys to get an `Arc` to the `Env`'s parent. Will return `None` if the
    /// parent `Arc<Env>` has a strong reference count of 0.
    pub fn get_parent(&self) -> Option<Arc<Self>> {
        Weak::upgrade(&self.parent.read().unwrap())
    }

    /// Returns `true` if the `Env` contains the key, and `false` if it doesn't.
    /// Doesn't check the `Env`'s parent, if it has one.
    pub fn contains_key(&self, key: &HashMapKey) -> bool {
        self.data.contains_key(key)
    }

    /// Returns `true` if this `Env`, **or any of its parent `Env`'s`**, contains
    /// the key. Returns `false` otherwise.
    pub fn contains_key_any(&self, key: &HashMapKey) -> bool {
        if self.contains_key(key) {
            true
        } else if let Some(parent) = self.get_parent() {
            parent.contains_key_any(key)
        } else {
            false
        }
    }

    /// Traverses the chain of `Env` and parent `Env`'s, and returns the one that
    /// contains the key. Returns `None` if the key is not found anywhere.
    pub fn find(starting_env: &Arc<Self>, key: &HashMapKey) -> Option<Arc<Self>> {
        if starting_env.contains_key(key) {
            Some(starting_env.clone())
        } else if let Some(parent) = starting_env.get_parent() {
            Self::find(&parent, key)
        } else {
            None
        }
    }

    /// Adds a `child` `Env` to a `parent` `Env`.
    pub fn add_child(parent: &Arc<Env>, child: &Arc<Env>) {
        // Add child to children vector:
        parent.children.write().unwrap().push(Arc::clone(child));

        // Link child to parent with a Weak ref:
        let mut child_parent = child.parent.write().unwrap();
        *child_parent = Arc::downgrade(parent);
    }

    /// Pops the last child that was added to this `Env`, and returns it.
    /// Returns `None` if there are no children.
    pub fn pop_child(&self) -> Option<Arc<Self>> {
        self.children.write().unwrap().pop()
    }
}

impl Extend<(HashMapKey, Expr)> for Env {
    fn extend<I: IntoIterator<Item = (HashMapKey, Expr)>>(&mut self, iter: I) {
        for (k, v) in iter {
            self.insert(k, Arc::new(v));
        }
    }
}

impl Extend<(HashMapKey, Arc<Expr>)> for Env {
    fn extend<I: IntoIterator<Item = (HashMapKey, Arc<Expr>)>>(&mut self, iter: I) {
        for (k, v) in iter {
            self.insert(k, v);
        }
    }
}

impl FromIterator<(HashMapKey, Expr)> for Env {
    fn from_iter<I: IntoIterator<Item = (HashMapKey, Expr)>>(iter: I) -> Self {
        let mut env = Env::new();
        env.extend(iter);
        env
    }
}

impl FromIterator<(HashMapKey, Arc<Expr>)> for Env {
    fn from_iter<I: IntoIterator<Item = (HashMapKey, Arc<Expr>)>>(iter: I) -> Self {
        let mut env = Env::new();
        env.extend(iter);
        env
    }
}
