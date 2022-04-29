use std::cell::Cell;

use super::Leaf;
use crate::BoxedNode;

// #[derive(Debug)]
pub enum Tree<K, V> {
    /// Branch node contains links to leaf and interim nodes on next level of tree.
    BoxedNode(BoxedNode<Tree<K, V>>),
    /// Leaf node inside Art contains 1 key value pair.
    Leaf(Leaf<K, V>),
    /// Node which contains leaf and interim pointers at the same time.
    /// This can happen when last byte of leaf key is same as byte which points to interim.
    /// For instance, we have root with prefix "a" which points to interim node using byte
    /// representations of char "b". Such interim will point to keys like "abc", "abb", "aba", etc.
    /// Now we try to insert new key "ab" to the tree. Root node has same prefix as key(i.e, "a")
    /// and hence we try to insert leaf node as root child. Because root already have pointer "b"
    /// to existing interim, we can't simply insert our key into tree. We should "enhance" interim
    /// node by new key by replacing interim node by special combined node.
    Combined(Box<Tree<K, V>>, Leaf<K, V>),
}

impl<K, V> Tree<K, V> {
    #[inline]
    pub fn new_combined(boxed_node: BoxedNode<Tree<K, V>>, leaf: Leaf<K, V>) -> Tree<K, V> {
        Tree::Combined(Box::new(Tree::BoxedNode(boxed_node)), leaf)
    }

    pub fn as_leaf_mut(&mut self) -> &mut Leaf<K, V> {
        match self {
            Tree::Leaf(node) => node,
            _ => panic!("Only leaf can be retrieved"),
        }
    }

    pub fn take_leaf(self) -> Leaf<K, V> {
        match self {
            Tree::Leaf(node) => node,
            _ => panic!("Only leaf can be retrieved"),
        }
    }

    pub fn as_interim_mut(&mut self) -> &mut BoxedNode<Tree<K, V>> {
        match self {
            Tree::BoxedNode(interim) => interim,
            _ => panic!("Only interim can be retrieved"),
        }
    }
}

#[cfg(test)]
impl<K, V> Tree<K, V> {
    pub fn leaf(&self) -> &Leaf<K, V> {
        match self {
            Tree::Leaf(node) => node,
            _ => panic!("Only leaf can be retrieved"),
        }
    }

    pub fn is_leaf(&self) -> bool {
        match self {
            Tree::Leaf(_) => true,
            _ => false,
        }
    }

    pub fn is_interim(&self) -> bool {
        match self {
            Tree::BoxedNode(_) => true,
            _ => false,
        }
    }

    pub fn interim(&self) -> &BoxedNode<Tree<K, V>> {
        match self {
            Tree::BoxedNode(inter) => inter,
            _ => panic!("not an interim"),
        }
    }
}

#[test]
fn sizeof_k_v_typenode() {
    let size = std::mem::size_of::<Tree<u8, ()>>();
    assert_eq!(size, 24);
}
