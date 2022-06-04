// use std::arch::x86_64::*;

mod flat_node;
pub use flat_node::{FlatNode, FlatNodeIter};

mod node48;
pub use node48::{Node48, Node48Iter};

mod node256;
pub use node256::{Node256, Node256Iter};

mod node_ops;
pub use node_ops::{InsertStatus, NodeOps};

pub enum NodeIter<'a, V> {
    Node4(FlatNodeIter<'a, V, 4>),
    Node16(FlatNodeIter<'a, V, 16>),
    Node48(Node48Iter<'a, V>),
    Node256(Node256Iter<'a, V>),
}
// impl<'a, V> NodeIter<'a, V>
// {
//     fn new(it: I) -> Self {
//         Self { it }
//     }
// }

impl<'a, V> DoubleEndedIterator for NodeIter<'a, V> {
    fn next_back(&mut self) -> Option<Self::Item> {
        match self {
            NodeIter::Node4(it) => it.next_back(),
            NodeIter::Node16(it) => it.next_back(),
            NodeIter::Node48(it) => it.next_back(),
            NodeIter::Node256(it) => it.next_back(),
        }
    }
}

impl<'a, V> Iterator for NodeIter<'a, V> {
    type Item = &'a V;

    fn next(&mut self) -> Option<Self::Item> {
        match self {
            NodeIter::Node4(it) => it.next(),
            NodeIter::Node16(it) => it.next(),
            NodeIter::Node48(it) => it.next(),
            NodeIter::Node256(it) => it.next(),
        }
    }
}

pub enum BoxedNode<V> {
    Size4(Box<FlatNode<V, 4>>),
    Size16(Box<FlatNode<V, 16>>),
    Size48(Box<Node48<V>>),
    Size256(Box<Node256<V>>),
}

impl<V> BoxedNode<V> {
    #[cfg(test)]
    pub(crate) fn node_size(&self) -> usize {
        match self {
            BoxedNode::Size4(_) => 4,
            BoxedNode::Size16(_) => 16,
            BoxedNode::Size48(_) => 48,
            BoxedNode::Size256(_) => 256,
        }
    }

    pub fn prefix(&self) -> &[u8] {
        match self {
            BoxedNode::Size4(node) => &node.prefix,
            BoxedNode::Size16(node) => &node.prefix,
            BoxedNode::Size48(node) => &node.prefix,
            BoxedNode::Size256(node) => &node.prefix,
        }
    }

    pub fn insert(&mut self, key: u8, value: V) -> InsertStatus<V> {
        match self {
            BoxedNode::Size4(node) => node.insert(key, value),
            BoxedNode::Size16(node) => node.insert(key, value),
            BoxedNode::Size48(node) => node.insert(key, value),
            BoxedNode::Size256(node) => node.insert(key, value),
        }
    }

    pub fn remove(&mut self, key: u8) -> Option<V> {
        match self {
            BoxedNode::Size4(node) => node.remove(key),
            BoxedNode::Size16(node) => node.remove(key),
            BoxedNode::Size48(node) => node.remove(key),
            BoxedNode::Size256(node) => node.remove(key),
        }
    }

    pub fn set_prefix(&mut self, prefix: &[u8]) {
        match self {
            BoxedNode::Size4(node) => node.prefix = prefix.to_vec(),
            BoxedNode::Size16(node) => node.prefix = prefix.to_vec(),
            BoxedNode::Size48(node) => node.prefix = prefix.to_vec(),
            BoxedNode::Size256(node) => node.prefix = prefix.to_vec(),
        }
    }

    pub fn expand(self) -> BoxedNode<V> {
        match self {
            BoxedNode::Size4(node) => BoxedNode::Size16(Box::new(node.resize())),
            BoxedNode::Size16(node) => BoxedNode::Size48(Box::new(Node48::from(*node))),
            BoxedNode::Size48(node) => BoxedNode::Size256(Box::new(Node256::from(*node))),
            BoxedNode::Size256(_) => self,
        }
    }

    pub fn should_shrink(&self) -> bool {
        match self {
            BoxedNode::Size4(_) => false,
            BoxedNode::Size16(node) => node.len <= 4,
            BoxedNode::Size48(node) => node.len <= 16,
            BoxedNode::Size256(node) => node.len <= 48,
        }
    }

    pub fn shrink(self) -> BoxedNode<V> {
        match self {
            BoxedNode::Size4(_) => self,
            BoxedNode::Size16(node) => BoxedNode::Size4(Box::new(node.resize())),
            BoxedNode::Size48(node) => BoxedNode::Size16(Box::new(FlatNode::from(*node))),
            BoxedNode::Size256(node) => BoxedNode::Size48(Box::new(Node48::from(*node))),
        }
    }

    pub fn get_mut(&mut self, key: u8) -> Option<&mut V> {
        match self {
            BoxedNode::Size4(node) => node.get_mut(key),
            BoxedNode::Size16(node) => node.get_mut(key),
            BoxedNode::Size48(node) => node.get_mut(key),
            BoxedNode::Size256(node) => node.get_mut(key),
        }
    }

    pub fn iter<'a>(&'a self) -> NodeIter<'a, V> {
        match self {
            BoxedNode::Size4(node) => NodeIter::Node4(node.iter()),
            BoxedNode::Size16(node) => NodeIter::Node16(node.iter()),
            BoxedNode::Size48(node) => NodeIter::Node48(node.iter()),
            BoxedNode::Size256(node) => NodeIter::Node256(node.iter()),
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::node::{FlatNode, InsertStatus, Node256, Node48, NodeOps};

    #[test]
    fn test_flat_node_node_ops_impl() {
        node_test(FlatNode::<usize, 4>::new(&[]), 4);
        node_test(FlatNode::<usize, 16>::new(&[]), 16);
        node_test(FlatNode::<usize, 32>::new(&[]), 32);
        node_test(FlatNode::<usize, 48>::new(&[]), 48);
        node_test(FlatNode::<usize, 64>::new(&[]), 64);

        // resize from 16 to 4
        let mut node = FlatNode::<usize, 16>::new(&[]);
        for i in 0..4 {
            node.insert(i as u8, i).unwrap();
        }
        let mut resized: FlatNode<usize, 4> = node.resize();
        assert_eq!(resized.len, 4);
        for i in 0..4 {
            assert!(matches!(resized.get_mut(i as u8), Some(v) if *v == i));
        }

        // resize from 4 to 16
        let mut node = FlatNode::<usize, 4>::new(&[]);
        for i in 0..4 {
            node.insert(i as u8, i).unwrap();
        }
        let mut resized: FlatNode<usize, 16> = node.resize();
        assert_eq!(resized.len, 4);
        for i in 4..16 {
            resized.insert(i as u8, i).unwrap();
        }
        assert_eq!(resized.len, 16);
        for i in 0..16 {
            assert!(matches!(resized.get_mut(i as u8), Some(v) if *v == i));
        }
    }

    #[test]
    fn test_node48_node_ops_impl() {
        node_test(Node48::<usize>::new(&[]), 48);

        // resize from 48 to 16
        let mut node = Node48::<usize>::new(&[]);
        for i in 0..16 {
            node.insert(i as u8, i).unwrap();
        }
        let mut resized: FlatNode<usize, 16> = FlatNode::from(node);
        assert_eq!(resized.len, 16);
        for i in 0..16 {
            assert!(matches!(resized.get_mut(i as u8), Some(v) if *v == i));
        }

        // resize from 48 to 4
        let mut node = Node48::<usize>::new(&[]);
        for i in 0..4 {
            node.insert(i as u8, i).unwrap();
        }
        let mut resized: FlatNode<usize, 4> = FlatNode::from(node);
        assert_eq!(resized.len, 4);
        for i in 0..4 {
            assert!(matches!(resized.get_mut(i as u8), Some(v) if *v == i));
        }
    }

    #[test]
    fn test_node256_node_ops_impl() {
        node_test(Node256::<usize>::new(&[]), 256);

        // resize from 48 to 256
        let mut node = Node48::<usize>::new(&[]);
        for i in 0..48 {
            node.insert(i as u8, i).unwrap();
        }
        let mut resized = Node256::from(node);
        assert_eq!(resized.len, 48);
        for i in 0..48 {
            assert!(matches!(resized.get_mut(i as u8), Some(v) if *v == i));
        }
    }

    fn node_test(mut node: impl NodeOps<usize>, size: usize) {
        // testing for duplicate key
        for i in 0..size {
            assert!(node.insert(i as u8, i).is_ok());
            assert!(node.insert(i as u8, i).is_err());
        }

        if size + 1 < u8::MAX as usize {
            assert!(matches!(
                node.insert((size + 1) as u8, size + 1),
                InsertStatus::Overflow(_)
            ));
        } else {
            assert!(matches!(
                node.insert((size + 1) as u8, size + 1),
                InsertStatus::DuplicateKey
            ));
        }

        for i in 0..size {
            assert!(matches!(node.get_mut(i as u8), Some(v) if *v == i));
        }

        if size + 1 < u8::MAX as usize {
            assert!(matches!(node.get_mut((size + 1) as u8), None));
        }

        for i in 0..size {
            assert!(matches!(node.remove(i as u8), Some(v) if v == i));
        }
        assert!(matches!(node.remove((size + 1) as u8), None));
    }
}
