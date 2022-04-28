use crate::{BoxedNode, NodeIter};

use super::Tree;

pub struct Branch<K, V>(BoxedNode<Tree<K, V>>);

impl<K, V> Branch<K, V> {
    // #[cfg(test)]
    // pub(crate) fn node_size(&self) -> usize {
    //     self.node().node_size()
    // }

    pub(crate) fn new(node: BoxedNode<Tree<K, V>>) -> Branch<K, V> {
        Branch(node)
    }

    pub(crate) fn node(&self) -> &BoxedNode<Tree<K, V>> {
        &self.0
    }

    pub(crate) fn node_mut(&mut self) -> &mut BoxedNode<Tree<K, V>> {
        &mut self.0
    }

    // pub fn prefix(&self) -> &[u8] {
    //     self.node().prefix()
    // }

    // pub fn insert(
    //     &mut self,
    //     key: u8,
    //     typed_node: Tree<K, V>,
    // ) -> InsertStatus<Tree<K, V>> {
    //     self.node_mut().insert(key, typed_node)
    // }

    // pub fn remove(&mut self, key: u8) -> Option<Tree<K, V>> {
    //     self.node_mut().remove(key)
    // }

    // pub fn set_prefix(&mut self, prefix: &[u8]) {
    //     self.node_mut().set_prefix(prefix)
    // }

    // pub fn expand(self) -> BoxedNode<Tree<K, V>> {
    //     self.0.expand()
    // }

    // pub fn should_shrink(&self) -> bool {
    //     self.node().should_shrink()
    // }

    // pub fn shrink(self) -> BoxedNode<Tree<K, V>> {
    //     self.0.shrink()
    // }

    // pub fn get_mut(&mut self, key: u8) -> Option<&mut Tree<K, V>> {
    //     self.node_mut().get_mut(key)
    // }

    pub fn iter<'a>(&'a self) -> NodeIter<'a, Tree<K, V>> {
        self.node().iter()
    }
}
