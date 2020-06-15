use dashmap::DashMap;
use std::{
    hash::Hash,
    iter::FromIterator,
    sync::{Arc, RwLock, Weak},
};

#[derive(Debug, Clone)]
struct Node<S: ToString + Eq + Hash> {
    data: Arc<DashMap<S, Arc<i32>>>,
    children: Arc<RwLock<Vec<Arc<Node<S>>>>>,
    parent: Arc<RwLock<Weak<Node<S>>>>,
}

impl<S: ToString + Eq + Hash> Node<S> {
    fn new() -> Self {
        Self {
            data: Arc::new(DashMap::new()),
            children: Arc::new(RwLock::new(vec![])),
            parent: Arc::new(RwLock::new(Weak::new())),
        }
    }

    fn insert(&self, k: S, v: Arc<i32>) -> Option<Arc<i32>> {
        self.data.insert(k, v)
    }

    fn add_child(parent: &Arc<Self>, child: &Arc<Self>) {
        // Add child to children array:
        parent.children.write().unwrap().push(Arc::clone(child));

        // Link child to parent with a Weak ref:
        let mut child_parent = child.parent.write().unwrap();
        *child_parent = Arc::downgrade(parent);
    }

    fn parent(&self) -> Option<Arc<Self>> {
        Weak::upgrade(&self.parent.read().unwrap())
    }

    fn get(&self, k: &S) -> Option<Arc<i32>> {
        if let Some(v) = self.data.get(k) {
            Some(v.clone())
        } else if let Some(parent) = Weak::upgrade(&self.parent.read().unwrap()) {
            parent.get(k)
        } else {
            None
        }
    }
}

impl<S: ToString + Eq + Hash> FromIterator<(S, i32)> for Node<S> {
    fn from_iter<I: IntoIterator<Item = (S, i32)>>(iter: I) -> Self {
        let node = Node::new();

        for (k, v) in iter {
            node.insert(k, Arc::new(v));
        }

        node
    }
}

impl<S: ToString + Eq + Hash> FromIterator<(S, Arc<i32>)> for Node<S> {
    fn from_iter<I: IntoIterator<Item = (S, Arc<i32>)>>(iter: I) -> Self {
        Self {
            data: Arc::new(DashMap::from_iter(iter)),
            children: Arc::new(RwLock::new(vec![])),
            parent: Arc::new(RwLock::new(Weak::new())),
        }
    }
}

fn main() {
    let leaf = Arc::new(Node::from_iter(vec![("a", 1), ("b", 2)]));

    let branch = Arc::new(Node::from_iter(vec![("foo", -42)]));

    Node::add_child(&branch, &leaf);

    println!(
        "leaf.parent()   = {:?}\n\
         branch.parent() = {:?}\n",
        leaf.parent(),
        branch.parent(),
    );

    println!(
        "leaf.get(\"a\")   = {:?}\n\
         leaf.get(\"foo\") = {:?}\n\
         branch.get(\"b\") = {:?}\n",
        leaf.get(&"a"),
        leaf.get(&"foo"),
        branch.get(&"b"),
    );

    let mut foo = Arc::new(Node::from_iter(vec![("foo", 42)]));
    let bar = Arc::new(Node::new());
    Node::add_child(&foo, &bar);
    dbg!(&foo);

    let mut arc_keeper = vec![];

    {
        let baz = Arc::new(Node::new());
        Node::add_child(&foo, &baz);
        baz.insert("baz", Arc::new(58));
        dbg!(&foo);
        arc_keeper.push(foo.clone());
        foo = baz;
    }

    dbg!(&foo);
    dbg!(foo.get(&"baz"));
    dbg!(foo.get(&"foo"));
}
