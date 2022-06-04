mod leaf;
pub use leaf::Leaf;

// mod branch;
// pub use branch::BoxedNode;

mod tree;
pub use tree::Tree;

use crate::node::*;
use crate::Key;

use std::{fmt, ptr};

pub struct TreeNode<K: Key, V: Clone + fmt::Debug> {
    pub tree: Tree<K, V>,
}

impl<K: Key, V: Clone + fmt::Debug> TreeNode<K, V> {
    pub(crate) fn interim_insert<'a>(
        &'a mut self,
        key: K,
        value: V,
        key_start_offset: usize,
    ) -> Result<bool, InsertOp<'a, K, V>> {
        let node: &'a mut Tree<K, V> = &mut self.tree;
        let node_ptr = node as *mut Tree<K, V>;
        let interim = node.as_interim_mut();
        if key.to_bytes().as_slice().len() <= key_start_offset {
            // no more bytes in key to go deeper inside the tree => replace interim by combined node
            // which will contains link to existing interim and leaf node with new KV.

            let existing_interim = unsafe { ptr::read(interim) };
            let new_interim = Tree::new_combined(existing_interim, Leaf::new(key, value));
            unsafe { ptr::write(node_ptr, new_interim) }
            return Ok(true);
        }

        let kb = key.to_bytes();
        let key_bytes = &kb.as_slice()[key_start_offset..];
        let prefix = interim.prefix();
        let prefix_size = common_prefix_len(prefix, key_bytes);

        if prefix_size == key_bytes.len() {
            // existing interim prefix fully equals to new key: replace existing interim by combined
            // node which will contain new key and link to existing values of interim
            unsafe {
                let existing_interim = ptr::read(interim);
                let new_node = Tree::Combined(
                    Box::new(Tree::BoxedNode(existing_interim)),
                    Leaf::new(key, value),
                );
                ptr::write(node_ptr, new_node)
            };
            Ok(true)
        } else if prefix_size < prefix.len() {
            // Node prefix and key has common byte sequence. For instance, node prefix is
            // "abc" and key is "abde", common sequence will be "ab". This sequence will be
            // used as prefix for new interim node and this interim will point to new leaf(with passed
            // KV) and previous interim(with prefix "abc").
            let mut new_interim = FlatNode::new(&prefix[..prefix_size]);
            let res = new_interim.insert(key_bytes[prefix_size], Tree::Leaf(Leaf::new(key, value)));
            debug_assert!(res.is_ok());
            let mut interim = unsafe { ptr::read(interim) };
            let interim_key = prefix[prefix_size];
            // update prefix of existing interim to remaining part of old prefix.
            // e.g, prefix was "abcd", prefix of new node is "ab".
            // Updated prefix will be "d" because "c" used as pointer inside new interim.
            if prefix_size + 1 < prefix.len() {
                interim.set_prefix(&prefix[prefix_size + 1..]);
            } else {
                interim.set_prefix(&[]);
            }
            let res = new_interim.insert(interim_key, Tree::BoxedNode(interim));
            debug_assert!(res.is_ok());
            unsafe {
                ptr::write(
                    node_ptr,
                    Tree::BoxedNode(BoxedNode::Size4(Box::new(new_interim))),
                )
            };
            Ok(true)
        } else {
            let interim_ptr = unsafe { &mut *(interim as *mut BoxedNode<Tree<K, V>>) };
            if let Some(next_node) = interim.get_mut(key_bytes[prefix_size]) {
                // interim already contains node with same 'next byte', we will try to insert on
                // the next level of tree. Existing node may be:
                // - leaf node: in this case leaf node will be replaced by interim node
                // - interim node: in this case we retry this method
                Err(InsertOp {
                    node: next_node,
                    key_byte_offset: key_start_offset + prefix_size + 1,
                    key,
                    value,
                })
            } else {
                // we find interim node which should contain new KV
                let leaf = Tree::Leaf(Leaf::new(key.clone(), value));
                match interim_ptr.insert(key_bytes[prefix_size], leaf) {
                    InsertStatus::Overflow(val) => {
                        let interim = unsafe { ptr::read(interim_ptr) };
                        let mut new_interim = interim.expand();
                        let err = new_interim.insert(key_bytes[prefix_size], val);
                        debug_assert!(
                            err.is_ok(),
                            "Insert failed after node expand (unexpected duplicate key)"
                        );
                        unsafe { ptr::write(node_ptr, Tree::BoxedNode(new_interim)) }
                        Ok(true)
                    }
                    InsertStatus::DuplicateKey => unreachable!(),
                    InsertStatus::Ok => Ok(true),
                }
            }
        }
    }

    pub(crate) fn replace_combined(&mut self, key: K, value: V) {
        let node: &mut Tree<K, V> = &mut self.tree;
        let existing_node = unsafe { ptr::read(node) };
        let new_node = Tree::Combined(Box::new(existing_node), Leaf::new(key, value));
        unsafe { ptr::write(node, new_node) };
    }

    pub(crate) fn replace_leaf(
        &mut self,
        key: K,
        value: V,
        key_bytes: &[u8],
        key_start_offset: usize,
        upsert: bool,
    ) -> bool {
        let node: &mut Tree<K, V> = &mut self.tree;
        let leaf = node.as_leaf_mut();
        if *key_bytes == *leaf.key.to_bytes().as_slice() {
            return if upsert {
                leaf.val = value;
                true
            } else {
                false
            };
        }

        let leaf_kb = leaf.key.to_bytes();
        let leaf_key_bytes = leaf_kb.as_slice();
        // skip bytes which covered by upper levels of tree
        let leaf_key = &leaf_key_bytes[key_start_offset..];
        let key_bytes = &key_bytes[key_start_offset..];

        // compute common prefix between existing key(found in leaf node) and key of new KV pair
        let prefix_size = common_prefix_len(leaf_key, key_bytes);

        let prefix = &leaf_key[..prefix_size];
        let leaf_key = &leaf_key[prefix_size..];
        let key_bytes = &key_bytes[prefix_size..];

        let new_interim = if leaf_key.is_empty() {
            // prefix covers entire leaf key => existing leaf key is shorter than new key.
            // in this case we replace existing leaf by new 'combined' node which will point to
            // existing leaf and new interim node(which will hold new KV).
            let mut new_interim = FlatNode::new(prefix);
            let err = new_interim.insert(key_bytes[0], Tree::Leaf(Leaf::new(key, value)));
            debug_assert!(err.is_ok());

            // safely move out value from node holder because
            // later we will override it without drop
            let existing_leaf = unsafe { ptr::read(leaf) };
            Tree::Combined(
                Box::new(Tree::BoxedNode(BoxedNode::Size4(Box::new(new_interim)))),
                existing_leaf,
            )
        } else if key_bytes.is_empty() {
            // no more bytes left in key of new KV => create combined node which will
            // point to new key, existing leaf will be moved into new interim node.
            // in this case, key of existing leaf is always longer(length in bytes) than new
            // key(if leaf key has the same length as new key, then keys are equal).
            let mut new_interim = FlatNode::new(prefix);
            // safely move out value from node holder because
            // later we will override it without drop
            let existing_leaf = unsafe { ptr::read(leaf) };
            let err = new_interim.insert(leaf_key[0], Tree::Leaf(existing_leaf));
            debug_assert!(err.is_ok());

            Tree::Combined(
                Box::new(Tree::BoxedNode(BoxedNode::Size4(Box::new(new_interim)))),
                Leaf::new(key, value),
            )
        } else {
            // existing leaf and new KV has common prefix => create new interim node which will
            // hold both KVs.

            // safely move out value from node holder because
            // later we will override it without drop
            let leaf = unsafe { ptr::read(leaf) };
            let mut new_interim = FlatNode::new(prefix);
            let err = new_interim.insert(key_bytes[0], Tree::Leaf(Leaf::new(key, value)));
            debug_assert!(err.is_ok());
            let err = new_interim.insert(leaf_key[0], Tree::Leaf(leaf));
            debug_assert!(err.is_ok());
            Tree::BoxedNode(BoxedNode::Size4(Box::new(new_interim)))
        };
        unsafe { ptr::write(node, new_interim) };
        true
    }
}

pub(crate) struct InsertOp<'n, K: Key, V: Clone + fmt::Debug> {
    node: &'n mut Tree<K, V>,
    // offset of byte in key which should be used to insert KV pair inside `node`
    key_byte_offset: usize,
    key: K,
    value: V,
}

fn common_prefix_len(k1: &[u8], k2: &[u8]) -> usize {
    let mut len = 0;
    for (b1, b2) in k1.iter().zip(k2.iter()) {
        if b1 != b2 {
            break;
        }
        len += 1;
    }
    len
}
