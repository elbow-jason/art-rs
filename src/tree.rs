use crate::{BoxedNode, Leaf, NodeIter};

// #[derive(Debug)]
pub enum TypedNode<K, V> {
    /// Interim node contains links to leaf and interim nodes on next level of tree.
    Interim(Interim<K, V>),
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
    Combined(Box<TypedNode<K, V>>, Leaf<K, V>),
}

impl<K, V> TypedNode<K, V> {
    pub fn as_leaf_mut(&mut self) -> &mut Leaf<K, V> {
        match self {
            TypedNode::Leaf(node) => node,
            _ => panic!("Only leaf can be retrieved"),
        }
    }

    pub fn take_leaf(self) -> Leaf<K, V> {
        match self {
            TypedNode::Leaf(node) => node,
            _ => panic!("Only leaf can be retrieved"),
        }
    }

    pub fn as_interim_mut(&mut self) -> &mut BoxedNode<TypedNode<K, V>> {
        match self {
            TypedNode::Interim(interim) => interim.node_mut(),
            _ => panic!("Only interim can be retrieved"),
        }
    }
}

#[cfg(test)]
impl<K, V> TypedNode<K, V> {
    pub fn leaf(&self) -> &Leaf<K, V> {
        match self {
            TypedNode::Leaf(node) => node,
            _ => panic!("Only leaf can be retrieved"),
        }
    }

    pub fn is_leaf(&self) -> bool {
        match self {
            TypedNode::Leaf(_) => true,
            _ => false,
        }
    }

    pub fn is_interim(&self) -> bool {
        match self {
            TypedNode::Interim(_) => true,
            _ => false,
        }
    }

    pub fn interim(&self) -> &Interim<K, V> {
        match self {
            TypedNode::Interim(inter) => inter,
            _ => panic!("not an interim"),
        }
    }
}

pub struct Interim<K, V>(BoxedNode<TypedNode<K, V>>);

impl<K, V> Interim<K, V> {
    // #[cfg(test)]
    // pub(crate) fn node_size(&self) -> usize {
    //     self.node().node_size()
    // }

    pub(crate) fn new(node: BoxedNode<TypedNode<K, V>>) -> Interim<K, V> {
        Interim(node)
    }

    pub(crate) fn node(&self) -> &BoxedNode<TypedNode<K, V>> {
        &self.0
    }

    pub(crate) fn node_mut(&mut self) -> &mut BoxedNode<TypedNode<K, V>> {
        &mut self.0
    }

    // pub fn prefix(&self) -> &[u8] {
    //     self.node().prefix()
    // }

    // pub fn insert(
    //     &mut self,
    //     key: u8,
    //     typed_node: TypedNode<K, V>,
    // ) -> InsertStatus<TypedNode<K, V>> {
    //     self.node_mut().insert(key, typed_node)
    // }

    // pub fn remove(&mut self, key: u8) -> Option<TypedNode<K, V>> {
    //     self.node_mut().remove(key)
    // }

    // pub fn set_prefix(&mut self, prefix: &[u8]) {
    //     self.node_mut().set_prefix(prefix)
    // }

    // pub fn expand(self) -> BoxedNode<TypedNode<K, V>> {
    //     self.0.expand()
    // }

    // pub fn should_shrink(&self) -> bool {
    //     self.node().should_shrink()
    // }

    // pub fn shrink(self) -> BoxedNode<TypedNode<K, V>> {
    //     self.0.shrink()
    // }

    // pub fn get_mut(&mut self, key: u8) -> Option<&mut TypedNode<K, V>> {
    //     self.node_mut().get_mut(key)
    // }

    pub fn iter<'a>(&'a self) -> NodeIter<'a, TypedNode<K, V>> {
        self.node().iter()
    }
}

#[test]
fn sizeof_k_v_typenode() {
    let size = std::mem::size_of::<TypedNode<u8, ()>>();
    assert_eq!(size, 24);
}
