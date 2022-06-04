//! # Adaptive Radix Tree
//! The radix tree based on ([The Adaptive Radix Tree:
//! ARTful Indexing for Main-Memory Databases](https://15721.courses.cs.cmu.edu/spring2016/papers/leis-icde2013.pdf)).
//!
//! # Examples
//! ```
//! use art_tree::{Art, Key};
//!
//! let mut art = Art::<u16, u16>::new();
//! for i in 0..u8::MAX as u16 {
//!     assert!(art.insert(i, i), "{}", i);
//!     assert!(matches!(art.get(&i), Some(val) if val == &i));
//! }
//! for i in 0..u8::MAX as u16 {
//!     assert!(matches!(art.remove(&i), Some(val) if val == i));
//! }
//!
//! let mut art = Art::<(u16, &str), u16>::new();
//! for i in 0..u8::MAX as u16 {
//!     let key = (i, "abc");
//!     art.upsert(key.clone(), i + 1);
//!     assert!(matches!(art.get(&key), Some(val) if val == &(i + 1)));
//! }
//!
//! let from_key = (16u16, "abc");
//! let until_key = (20u16, "abc");
//! assert_eq!(art.range(from_key..=until_key).count(), 5);
//! assert_eq!(art.iter().count(), u8::MAX as usize);
//! ```

mod keys;
pub use keys::*;

mod node;
use node::*;

mod tree;
use tree::{Leaf, Tree};

mod scanner;
use scanner::Scanner;

use std::cmp::Ordering;
use std::ops::RangeBounds;
use std::option::Option::Some;
use std::{fmt, mem, ptr};

/// Adaptive Radix Tree.  
///
/// Radix tree is ordered according to key. Radix tree requires that key to be representable as
/// comparable by sequence, e.g. key should implement [Key] trait which used to convert it to
/// byte sequence.
///
/// This crate provides [Key] implementations for most commonly used data types:
/// - unsigned integers(u8, u16, u32, u64, u128)  
/// - signed integers(i8, i16, i32, i64, i128)
/// - usize
/// - floating point numbers f32 and f64
/// - floating point numbers through [Float32]/[Float64] types
#[derive(Clone, PartialEq, Eq)]
pub struct Art<K, V>
where
    K: Key,
    V: Clone + fmt::Debug,
{
    root: Tree<K, V>,
}

impl<K: Key, V: Clone + fmt::Debug> Default for Art<K, V> {
    fn default() -> Self {
        Self::new()
    }
}

impl<'a, K: Key, V: Clone + fmt::Debug> Art<K, V> {
    /// Create empty [ART] tree.
    pub fn new() -> Self {
        Self { root: Tree::Empty }
    }

    /// Insert key-value pair into tree.  
    /// Return `true` if key-value successfully inserted into tree, otherwise `false` if tree
    /// already contains same key.
    pub fn insert(&'a mut self, key: K, value: V) -> bool {
        self.insert_internal(key, value, false)
    }

    /// Insert key-value pair into tree.
    /// If key already exists in tree, existing value will be replaced, otherwise inserts new KV
    /// into tree.
    pub fn upsert(&'a mut self, key: K, value: V) {
        self.insert_internal(key, value, true);
    }

    fn insert_internal(&mut self, key: K, value: V, upsert: bool) -> bool {
        let kb = key.to_bytes();
        let key_bytes = kb.as_slice();
        assert!(
            !key_bytes.is_empty(),
            "Key must have non empty bytes representation"
        );

        let mut node = self.root_mut();
        let mut key = key.clone();
        let mut offset = 0;
        let mut val = value;
        loop {
            let node_ptr = node as *mut Tree<K, V>;
            let res = match node {
                Tree::Empty => {
                    let mut new_root = Tree::Leaf(Leaf { key, val });
                    std::mem::swap(&mut new_root, &mut self.root);
                    Ok(true)
                }
                Tree::Leaf(_) => Ok(Self::replace_leaf(
                    node, key, val, key_bytes, offset, upsert,
                )),
                Tree::Combined(interim, leaf) => {
                    match leaf
                        .key
                        .to_bytes()
                        .as_slice()
                        .cmp(key.to_bytes().as_slice())
                    {
                        Ordering::Equal => {
                            if upsert {
                                leaf.val = val;
                                Ok(true)
                            } else {
                                Ok(false)
                            }
                        }
                        Ordering::Greater => {
                            // new key is 'less' than any key in this level
                            Self::replace_combined(unsafe { &mut *node_ptr }, key, val);
                            Ok(true)
                        }
                        _ => Err(InsertOp {
                            node: interim.as_mut(),
                            key_byte_offset: offset,
                            key,
                            value: val,
                        }),
                    }
                }
                Tree::BoxedNode(_) => Self::interim_insert(node, key, val, offset),
            };
            match res {
                Ok(is_inserted) => return is_inserted,
                Err(op) => {
                    node = op.node;
                    offset = op.key_byte_offset;
                    key = op.key;
                    val = op.value;
                }
            }
        }
    }

    /// Remove value associated with key.  
    /// Returns `Some(V)` if key found in tree, otherwise `None`.
    pub fn remove(&mut self, key: &'a K) -> Option<V> {
        if self.root.is_empty() {
            return None;
        }
        let root = &mut self.root;
        let kb = key.to_bytes();
        let key_bytes_vec = kb.as_slice();
        let mut key_bytes = key_bytes_vec.as_ref();
        let key_ro_buffer = key_bytes;
        let mut parent_link = 0;
        let mut parent: Option<&mut BoxedNode<Tree<K, V>>> = None;
        let mut node_ptr = root as *mut Tree<K, V>;
        loop {
            match unsafe { &mut *node_ptr } {
                Tree::Empty => return None,
                Tree::Leaf(leaf) => {
                    // TODO: merge nodes if parent contains only link to child node
                    return if key_ro_buffer == leaf.key.to_bytes().as_slice() {
                        if let Some(p) = parent {
                            if p.should_shrink() {
                                unsafe {
                                    let new_node = ptr::read(p).shrink();
                                    ptr::write(p, new_node);
                                };
                            }
                            Some(p.remove(parent_link).unwrap().take_leaf().val)
                        } else {
                            Some(mem::replace(&mut self.root, Tree::Empty).take_leaf().val)
                        }
                    } else {
                        None
                    };
                }
                Tree::BoxedNode(interim) => {
                    if let Some((next_node, rem_key_bytes, key)) =
                        Self::find_in_interim_mut(interim, key_bytes)
                    {
                        node_ptr = next_node as *mut Tree<K, V>;
                        parent = Some(interim);
                        parent_link = key;
                        key_bytes = rem_key_bytes;
                    } else {
                        return None;
                    }
                }
                Tree::Combined(interim, leaf) => {
                    if key_ro_buffer == leaf.key.to_bytes().as_slice() {
                        let leaf = unsafe { ptr::read(leaf) };
                        unsafe { ptr::write(node_ptr, *ptr::read(interim)) };
                        return Some(leaf.val);
                    } else {
                        node_ptr = interim.as_mut() as *mut Tree<K, V>;
                    }
                }
            }
        }
    }

    /// Get value associated with key.  
    /// Returns `Some(V)` if key found in tree, otherwise `None`.
    pub fn get(&self, key: &K) -> Option<&V> {
        let kb = key.to_bytes();
        let key_vec = kb.as_slice();
        assert!(
            !key_vec.is_empty(),
            "Key must have non empty byte string representation"
        );

        let mut node = self.root();
        let mut key_bytes = key_vec.as_ref();
        let key_ro_buffer = key_bytes;
        loop {
            match node {
                Tree::Empty => return None,
                Tree::Leaf(leaf) => {
                    return if leaf.key.to_bytes().as_slice() == key_ro_buffer {
                        Some(&leaf.val)
                    } else {
                        None
                    }
                }
                Tree::BoxedNode(interim) => {
                    if let Some((next_node, rem_key_bytes, _)) =
                        Self::find_in_interim(interim, key_bytes)
                    {
                        node = next_node;
                        key_bytes = rem_key_bytes;
                    } else {
                        node = &Tree::Empty;
                    }
                }
                Tree::Combined(interim, leaf) => {
                    if *key_ro_buffer == *leaf.key.to_bytes().as_slice() {
                        return Some(&leaf.val);
                    } else {
                        node = interim;
                    }
                }
            }
        }
    }

    fn root(&'a self) -> &Tree<K, V> {
        &self.root
    }

    fn root_mut(&mut self) -> &mut Tree<K, V> {
        &mut self.root
    }

    /// Execute tree range scan.  
    pub fn range(&self, range: impl RangeBounds<K>) -> impl DoubleEndedIterator<Item = (&K, &V)>
    where
        K: Key + Ord,
    {
        match self.root() {
            Tree::Empty => Scanner::empty(range),
            root => Scanner::new(root, range),
        }
    }

    /// Returns tree iterator.
    pub fn iter(&'a self) -> impl DoubleEndedIterator<Item = (&K, &V)>
    where
        K: Ord,
    {
        self.range(..)
    }

    fn find_in_interim<'n, 'k>(
        interim: &'n BoxedNode<Tree<K, V>>,
        key_bytes: &'k [u8],
    ) -> Option<(&'a Tree<K, V>, &'k [u8], u8)> {
        let node = unsafe {
            #[allow(clippy::cast_ref_to_mut)]
            &mut *(interim as *const BoxedNode<Tree<K, V>> as *mut BoxedNode<Tree<K, V>>)
        };
        Self::find_in_interim_mut(node, key_bytes.as_ref())
            .map(|(node, bytes, key)| (unsafe { &*(node as *const Tree<K, V>) }, bytes, key))
    }

    fn find_in_interim_mut<'n, 'k>(
        interim: &'n mut BoxedNode<Tree<K, V>>,
        key_bytes: &'k [u8],
    ) -> Option<(&'n mut Tree<K, V>, &'k [u8], u8)> {
        let prefix = interim.prefix().to_vec();
        if key_bytes.len() == prefix.len() || common_prefix_len(&prefix, key_bytes) != prefix.len()
        {
            // prefix of node exactly the same as key => no matches to key
            // because all keys inside interim node longer at least by 1 byte
            // or
            // node has prefix which is not prefix of search key.
            None
        } else {
            // we have a prefix match, now try to find next byte of key which follows immediately
            // after prefix.
            interim.get_mut(key_bytes[prefix.len()]).map(|node| {
                let key_byte_in_parent = key_bytes[prefix.len()];
                let key_bytes = if key_bytes.len() > prefix.len() + 1 {
                    &key_bytes[prefix.len() + 1..]
                } else {
                    &[]
                };
                (node, key_bytes, key_byte_in_parent)
            })
        }
    }

    fn replace_combined(node: &mut Tree<K, V>, key: K, value: V) {
        let existing_node = unsafe { ptr::read(node) };
        let new_node = Tree::Combined(Box::new(existing_node), Leaf::new(key, value));
        unsafe { ptr::write(node, new_node) };
    }

    fn replace_leaf(
        node: &'a mut Tree<K, V>,
        key: K,
        value: V,
        key_bytes: &[u8],
        key_start_offset: usize,
        upsert: bool,
    ) -> bool {
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

    fn interim_insert(
        node: &'a mut Tree<K, V>,
        key: K,
        value: V,
        key_start_offset: usize,
    ) -> Result<bool, InsertOp<'a, K, V>> {
        let node_ptr = node as *mut Tree<K, V>;
        let interim = node.as_interim_mut();
        if key.to_bytes().as_slice().len() <= key_start_offset {
            // no more bytes in key to go deeper inside the tree => replace interim by combined node
            // which will contains link to existing interim and leaf node with new KV.
            unsafe {
                let existing_interim = ptr::read(interim);
                let new_interim = Tree::Combined(
                    Box::new(Tree::BoxedNode(existing_interim)),
                    Leaf::new(key, value),
                );
                ptr::write(node_ptr, new_interim)
            }
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

struct InsertOp<'n, K: Key, V: Clone + fmt::Debug> {
    node: &'n mut Tree<K, V>,
    // offset of byte in key which should be used to insert KV pair inside `node`
    key_byte_offset: usize,
    key: K,
    value: V,
}

#[test]
fn art_with_no_items() {
    let a: Art<i32, i32> = Art::new();
    assert!(a.root.is_empty());
}

#[test]
fn art_with_one_items() {
    let mut a: Art<i32, i32> = Art::new();
    assert_eq!(a.insert(1, 2), true);
    let root = a.root;
    let expected = Leaf::new(1, 2);
    let leaf = root.take_leaf();
    assert_eq!(leaf.key, expected.key);
    assert_eq!(leaf.val, expected.val);
}

#[test]
fn art_with_two_items_with_common_prefix() {
    let mut a: Art<u32, u32> = Art::new();
    assert!(a.root.is_empty());
    assert_eq!(a.insert(1, 2), true);
    assert!(&a.root.is_leaf());
    assert_eq!(a.insert(3, 4), true);
    let mut root = a.root;
    let bnode = root.as_interim_mut();
    assert_eq!(bnode.node_size(), 4);
    assert_eq!(bnode.prefix(), &vec![0, 0, 0]);
    let mut node_it: NodeIter<Tree<u32, u32>> = bnode.iter();
    let one = node_it.next().unwrap();
    assert!(one.is_leaf());
    assert_eq!(one.leaf(), &Leaf::new(1u32, 2));
    let two = node_it.next().unwrap();
    assert!(two.is_leaf());
    assert_eq!(two.leaf(), &Leaf::new(3u32, 4));
    assert!(node_it.next().is_none());
}

#[test]
fn art_with_two_items_with_no_common_prefix() {
    let mut a: Art<i32, i32> = Art::new();
    assert_eq!(a.insert(1, 2), true);
    assert_eq!(a.insert(-1, -2), true);
    let mut root = a.root;
    let bnode = root.as_interim_mut();
    assert_eq!(bnode.node_size(), 4);
    assert_eq!(bnode.prefix(), &vec![]);
    let mut node_it: NodeIter<Tree<i32, i32>> = bnode.iter();
    let one = node_it.next().unwrap();
    assert!(one.is_leaf());
    assert_eq!(one.leaf(), &Leaf::new(-1i32, -2));
    let two = node_it.next().unwrap();
    assert!(two.is_leaf());
    assert_eq!(two.leaf(), &Leaf::new(1i32, 2));
    assert!(node_it.next().is_none());
}

#[test]
fn art_with_2_different_length_string_keys() {
    let mut a: Art<String, i32> = Art::new();
    let k1 = "aaa".to_owned();
    let k2 = "bbbbb".to_owned();
    // inserting 1 turns root into a leaf
    assert_eq!(a.insert(k1.clone(), 2), true);
    assert!(&a.root.is_leaf());
    // inserting another turns root into an interim
    assert_eq!(a.insert(k2.clone(), -2), true);
    assert!(&a.root.is_interim());

    let mut root = a.root;
    let bnode = root.as_interim_mut();
    assert_eq!(bnode.node_size(), 4);
    assert_eq!(bnode.prefix(), &[]);
    let mut node_it: NodeIter<Tree<String, i32>> = bnode.iter();
    let one = node_it.next().unwrap();
    assert!(one.is_leaf());
    assert_eq!(one.leaf(), &Leaf::new(k1.clone(), -2));
    let two = node_it.next().unwrap();
    assert!(two.is_leaf());
    assert_eq!(two.leaf(), &Leaf::new(k2.clone(), 2));
    assert!(node_it.next().is_none());
}

#[test]
fn art_with_3_string_keys_with_2_common_prefix() {
    let mut a: Art<String, i32> = Art::new();
    let k1 = "aaa".to_owned();
    let k2 = "bbbbb".to_owned();
    let k3 = "bbbcc".to_owned();
    // inserting 1 turns root into a leaf
    assert_eq!(a.insert(k1.clone(), 2), true);
    assert!(&a.root.is_leaf());
    // inserting another turns root into an interim
    assert_eq!(a.insert(k2.clone(), -2), true);
    assert!(&a.root.is_interim());

    assert_eq!(a.insert(k3.clone(), -16), true);
    assert!(&a.root.is_interim());

    let mut root = a.root;
    let bnode = root.as_interim_mut();
    assert_eq!(bnode.node_size(), 4);
    assert_eq!(bnode.prefix(), &[]);
    let mut node_it: NodeIter<Tree<String, i32>> = bnode.iter();
    let one = node_it.next().unwrap();
    assert!(one.is_leaf());
    assert_eq!(one.leaf(), &Leaf::new(k1.clone(), -2));
    let two = node_it.next().unwrap();
    assert!(two.is_interim());
    let two_inter = two.interim();
    assert_eq!(two_inter.prefix(), &vec![98, 98]);
    assert!(node_it.next().is_none());
}

#[cfg(test)]
mod tests {
    use crate::{Art, Float32, Float64, Key};
    use rand::prelude::IteratorRandom;
    use rand::seq::SliceRandom;
    use rand::{thread_rng, Rng};
    use std::collections::HashSet;

    fn compound_key<A: Key, B: Key>(a: A, b: B) -> Vec<u8> {
        let mut key = vec_key(a);
        key.extend(b.to_bytes().as_slice());
        key
    }

    fn vec_key<K: Key>(k: K) -> Vec<u8> {
        k.to_bytes().as_slice().to_vec()
    }

    #[test]
    fn seq_insert_combined_key() {
        let mut art = Art::new();
        for i in 0..=u8::MAX {
            for j in i8::MIN..=i8::MAX {
                let key = compound_key(i, j);
                assert!(art.insert(key, i.to_string()), "{}", i);
            }
        }

        for i in 0..=u8::MAX {
            for j in i8::MIN..=i8::MAX {
                let key = compound_key(i, j);
                assert!(matches!(art.get(&key), Some(val) if val == &i.to_string()));
            }
        }
    }

    #[test]
    fn seq_insert_u8() {
        let mut art = Art::new();
        for i in 0..=u8::MAX {
            assert!(art.insert(i, i.to_string()), "{}", i);
        }

        for i in 0..=u8::MAX {
            assert!(matches!(art.get(&i), Some(val) if val == &i.to_string()));
        }
    }

    #[test]
    fn seq_insert_i8() {
        let mut art = Art::new();
        for i in i8::MIN..=i8::MAX {
            assert!(art.insert(i, i.to_string()), "{}", i);
        }

        for i in i8::MIN..=i8::MAX {
            assert!(matches!(art.get(&i), Some(val) if val == &i.to_string()));
        }
    }

    #[test]
    fn seq_insert_u16() {
        let mut art = Art::new();
        for i in 0..=u16::MAX {
            assert!(art.insert(i, i.to_string()), "{}", i);
        }

        for i in 0..=u16::MAX {
            assert!(matches!(art.get(&i), Some(val) if val == &i.to_string()));
        }
    }

    #[test]
    fn seq_insert_i16() {
        let mut art = Art::new();
        for i in i16::MIN..=i16::MAX {
            assert!(art.insert(i, i.to_string()), "{}", i);
        }

        for i in i16::MIN..=i16::MAX {
            assert!(matches!(art.get(&i), Some(val) if val == &i.to_string()));
        }
    }

    #[test]
    fn seq_insert_u32() {
        let mut art = Art::new();
        for shift in 0..2 {
            let start = (u16::MAX as u32 + 1) << (shift * 8);
            let end = start + 10000;
            for i in start..=end {
                assert!(art.insert(i, i.to_string()), "{}", i);
            }
            for i in start..=end {
                assert!(matches!(art.get(&i), Some(val) if val == &i.to_string()));
            }
        }
    }

    #[test]
    fn seq_insert_i32() {
        let mut art = Art::new();
        for shift in 0..2 {
            let start = i32::MIN >> (shift * 8);
            let end = start + 10000;
            for i in start..=end {
                assert!(art.insert(i, i.to_string()), "{}", i);
            }
            for i in start..=end {
                assert!(matches!(art.get(&i), Some(val) if val == &i.to_string()));
            }
        }

        assert!(art.insert(0, "0".to_string()), "{}", 0);

        for shift in 0..2 {
            let start = (i16::MAX as i32 + 1) << (shift * 8);
            let end = start + 10000;
            for i in start..=end {
                assert!(art.insert(i, i.to_string()), "{}", i);
            }
            for i in start..=end {
                assert!(matches!(art.get(&i), Some(val) if val == &i.to_string()));
            }
        }
    }

    #[test]
    fn seq_insert_f32() {
        let mut art: Art<Float32, String> = Art::new();
        assert!(
            art.insert(f32::MIN.into(), f32::MIN.to_string()),
            "{}",
            f32::MIN
        );
        assert!(matches!(art.get(&f32::MIN.into()), Some(val) if val == &f32::MIN.to_string()));
        assert!(
            art.insert(f32::MAX.into(), f32::MAX.to_string()),
            "{}",
            f32::MAX
        );
        assert!(matches!(art.get(&f32::MAX.into()), Some(val) if val == &f32::MAX.to_string()));
        assert!(art.insert(0.0.into(), 0.to_string()), "{}", 0);
        assert!(matches!(art.get(&0.0.into()), Some(val) if val == &0.to_string()));
        assert!(
            art.insert(Float32::from(-1.0000001), 0.to_string()),
            "{}",
            0
        );
        assert!(
            matches!(art.get(&Float32::from(-1.0000001)), Some(val) if val == &0.to_string
            ())
        );

        assert!(
            art.insert(f32::NAN.into(), f32::NAN.to_string()),
            "{}",
            f32::NAN
        );
        assert!(matches!(art.get(&f32::NAN.into()), Some(val) if val == &f32::NAN.to_string()));

        assert!(
            art.insert(f32::NEG_INFINITY.into(), f32::NEG_INFINITY.to_string()),
            "{}",
            f32::NEG_INFINITY
        );
        assert!(
            matches!(art.get(&f32::NEG_INFINITY.into()), Some(val) if val == &f32::NEG_INFINITY.to_string())
        );

        assert!(
            art.insert(f32::INFINITY.into(), f32::INFINITY.to_string()),
            "{}",
            f32::INFINITY
        );
        assert!(
            matches!(art.get(&f32::INFINITY.into()), Some(val) if val == &f32::INFINITY.to_string())
        );
    }

    #[test]
    fn seq_insert_f64() {
        let mut art: Art<Float64, String> = Art::new();
        assert!(
            art.insert(f64::MIN.into(), f64::MIN.to_string()),
            "{}",
            f64::MIN
        );
        assert!(matches!(art.get(&f64::MIN.into()), Some(val) if val == &f64::MIN.to_string()));
        assert!(
            art.insert(f64::MAX.into(), f64::MAX.to_string()),
            "{}",
            f64::MAX
        );
        assert!(matches!(art.get(&f64::MAX.into()), Some(val) if val == &f64::MAX.to_string()));
        assert!(art.insert(0.0.into(), 0.to_string()), "{}", 0);
        assert!(matches!(art.get(&0.0.into()), Some(val) if val == &0.to_string()));
        assert!(
            art.insert(Float64::from(-1.00000012), 0.to_string()),
            "{}",
            0
        );
        assert!(
            matches!(art.get(&Float64::from(-1.00000012)), Some(val) if val == &0.to_string
            ())
        );

        assert!(
            art.insert(f64::NAN.into(), f64::NAN.to_string()),
            "{}",
            f64::NAN
        );
        assert!(matches!(art.get(&f64::NAN.into()), Some(val) if val == &f64::NAN.to_string()));

        assert!(
            art.insert(f64::NEG_INFINITY.into(), f64::NEG_INFINITY.to_string()),
            "{}",
            f64::NEG_INFINITY
        );
        assert!(
            matches!(art.get(&f64::NEG_INFINITY.into()), Some(val) if val == &f64::NEG_INFINITY.to_string())
        );

        assert!(
            art.insert(f64::INFINITY.into(), f64::INFINITY.to_string()),
            "{}",
            f64::INFINITY
        );
        assert!(
            matches!(art.get(&f64::INFINITY.into()), Some(val) if val == &f64::INFINITY.to_string())
        );
    }

    #[test]
    fn seq_insert_u64() {
        let mut art = Art::new();
        for shift in 0..4 {
            let start = (u32::MAX as u64 + 1) << (shift * 8);
            let end = start + 100_000;
            for i in start..=end {
                assert!(art.insert(i, i.to_string()), "{}", i);
            }
            for i in start..=end {
                assert!(matches!(art.get(&i), Some(val) if val == &i.to_string()));
            }
        }
    }

    #[test]
    fn seq_insert_i64() {
        let mut art = Art::new();
        for shift in 0..4 {
            let start = i64::MIN >> (shift * 8);
            let end = start + 10000;
            for i in start..=end {
                assert!(art.insert(i, i.to_string()), "{}", i);
            }
            for i in start..=end {
                assert!(matches!(art.get(&i), Some(val) if val == &i.to_string()));
            }
        }

        assert!(art.insert(0, "0".to_string()), "{}", 0);

        for shift in 0..4 {
            let start = (i32::MAX as i64 + 1) << (shift * 8);
            let end = start + 10000;
            for i in start..=end {
                assert!(art.insert(i, i.to_string()), "{}", i);
            }
            for i in start..=end {
                assert!(matches!(art.get(&i), Some(val) if val == &i.to_string()));
            }
        }
    }

    #[test]
    fn seq_insert_u128() {
        let mut art = Art::new();
        for shift in 0..8 {
            let start = (u64::MAX as u128 + 1) << (shift * 8);
            let end = start + 10000;
            for i in start..=end {
                assert!(art.insert(i, i.to_string()), "{}", i);
            }
            for i in start..=end {
                assert!(matches!(art.get(&i), Some(val) if val == &i.to_string()));
            }
        }
    }

    #[test]
    fn seq_insert_i128() {
        let mut art = Art::new();
        for shift in 0..8 {
            let start = i128::MIN >> (shift * 8);
            let end = start + 10000;
            for i in start..=end {
                assert!(art.insert(i, i.to_string()), "{}", i);
            }
            for i in start..=end {
                assert!(matches!(art.get(&i), Some(val) if val == &i.to_string()));
            }
        }

        assert!(art.insert(0, "0".to_string()), "{}", 0);

        for shift in 0..8 {
            let start = (i64::MAX as i128 + 1) << (shift * 8);
            let end = start + 10000;
            for i in start..=end {
                assert!(art.insert(i, i.to_string()), "{}", i);
            }
            for i in start..=end {
                assert!(matches!(art.get(&i), Some(val) if val == &i.to_string()));
            }
        }
    }

    #[test]
    fn seq_remove_combined_key() {
        let mut art = Art::new();
        for i in 0..=u8::MAX {
            for j in i8::MIN..=i8::MAX {
                let key = compound_key(i, j);
                assert!(art.insert(key, i.to_string()), "{}", i);
            }
        }

        for i in 0..=u8::MAX {
            for j in i8::MIN..=i8::MAX {
                let key = compound_key(i, j);
                assert!(matches!(art.remove(&key), Some(val) if val == i.to_string()));
                assert!(matches!(art.get(&key), None));
            }
        }
    }

    #[test]
    fn seq_remove_u8() {
        let mut art = Art::new();
        for i in 0..=u8::MAX {
            assert!(art.insert(i, i.to_string()), "{}", i);
        }

        for i in 0..=u8::MAX {
            assert!(matches!(art.remove(&i), Some(val) if val == i.to_string()));
            assert!(matches!(art.get(&i), None));
        }
    }

    #[test]
    fn seq_remove_i8() {
        let mut art = Art::new();
        for i in i8::MIN..=i8::MAX {
            assert!(art.insert(i, i.to_string()), "{}", i);
        }

        for i in i8::MIN..=i8::MAX {
            assert!(matches!(art.remove(&i), Some(val) if val == i.to_string()));
            assert!(matches!(art.get(&i), None));
        }
    }

    #[test]
    fn seq_remove_u16() {
        let mut art = Art::new();
        for i in 0..=u16::MAX {
            assert!(art.insert(i, i.to_string()), "{}", i);
        }

        for i in 0..=u16::MAX {
            assert!(matches!(art.remove(&i), Some(val) if val == i.to_string()));
            assert!(matches!(art.get(&i), None));
        }
    }

    #[test]
    fn seq_remove_i16() {
        let mut art = Art::new();
        for i in i16::MIN..=i16::MAX {
            assert!(art.insert(i, i.to_string()), "{}", i);
        }

        for i in i16::MIN..=i16::MAX {
            assert!(matches!(art.remove(&i), Some(val) if val == i.to_string()));
            assert!(matches!(art.get(&i), None));
        }
    }

    #[test]
    fn seq_remove_u32() {
        let mut art = Art::new();
        for shift in 0..2 {
            let start = (u16::MAX as u32 + 1) << (shift * 8);
            let end = start + 10000;
            for i in start..=end {
                assert!(art.insert(i, i.to_string()), "{}", i);
            }
            for i in start..=end {
                assert!(matches!(art.remove(&i), Some(val) if val == i.to_string()));
                assert!(matches!(art.get(&i), None));
            }
        }
    }

    #[test]
    fn seq_remove_i32() {
        let mut art = Art::new();
        for shift in 0..2 {
            let start = i32::MIN >> (shift * 8);
            let end = start + 10000;
            for i in start..=end {
                assert!(art.insert(i, i.to_string()), "{}", i);
            }
            for i in start..=end {
                assert!(matches!(art.remove(&i), Some(val) if val == i.to_string()));
                assert!(matches!(art.get(&i), None));
            }
        }

        assert!(art.insert(0, "0".to_string()), "{}", 0);
        assert!(matches!(art.remove(&0), Some(val) if val == 0.to_string()));

        for shift in 0..2 {
            let start = (i16::MAX as i32 + 1) << (shift * 8);
            let end = start + 10000;
            for i in start..=end {
                assert!(art.insert(i, i.to_string()), "{}", i);
            }
            for i in start..=end {
                assert!(matches!(art.remove(&i), Some(val) if val == i.to_string()));
                assert!(matches!(art.get(&i), None));
            }
        }
    }

    #[test]
    fn seq_remove_u64() {
        let mut art = Art::new();
        for shift in 0..4 {
            let start = (u32::MAX as u64 + 1) << (shift * 8);
            let end = start + 100_000;
            for i in start..=end {
                assert!(art.insert(i, i.to_string()), "{}", i);
            }
            for i in start..=end {
                assert!(matches!(art.remove(&i), Some(val) if val == i.to_string()));
                assert!(matches!(art.get(&i), None));
            }
        }
    }

    #[test]
    fn seq_remove_i64() {
        let mut art = Art::new();
        for shift in 0..4 {
            let start = i64::MIN >> (shift * 8);
            let end = start + 10000;
            for i in start..=end {
                assert!(art.insert(i, i.to_string()), "{}", i);
            }
            for i in start..=end {
                assert!(matches!(art.remove(&i), Some(val) if val == i.to_string()));
                assert!(matches!(art.get(&i), None));
            }
        }

        assert!(art.insert(0, "0".to_string()), "{}", 0);
        assert!(matches!(art.remove(&0), Some(val) if val == 0.to_string()));

        for shift in 0..4 {
            let start = (i32::MAX as i64 + 1) << (shift * 8);
            let end = start + 10000;
            for i in start..=end {
                assert!(art.insert(i, i.to_string()), "{}", i);
            }
            for i in start..=end {
                assert!(matches!(art.remove(&i), Some(val) if val == i.to_string()));
                assert!(matches!(art.get(&i), None));
            }
        }
    }

    #[test]
    fn seq_remove_u128() {
        let mut art = Art::new();
        for shift in 0..8 {
            let start = (u64::MAX as u128 + 1) << (shift * 8);
            let end = start + 10000;
            for i in start..=end {
                assert!(art.insert(i, i.to_string()), "{}", i);
            }
            for i in start..=end {
                assert!(matches!(art.remove(&i), Some(val) if val == i.to_string()));
                assert!(matches!(art.get(&i), None));
            }
        }
    }

    #[test]
    fn seq_remove_i128() {
        let mut art = Art::new();
        for shift in 0..8 {
            let start = i128::MIN >> (shift * 8);
            let end = start + 10000;
            for i in start..=end {
                assert!(art.insert(i, i.to_string()), "{}", i);
            }
            for i in start..=end {
                assert!(matches!(art.remove(&i), Some(val) if val == i.to_string()));
                assert!(matches!(art.get(&i), None));
            }
        }

        assert!(art.insert(0, "0".to_string()), "{}", 0);

        for shift in 0..8 {
            let start = (i64::MAX as i128 + 1) << (shift * 8);
            let end = start + 10000;
            for i in start..=end {
                assert!(art.insert(i, i.to_string()), "{}", i);
            }
            for i in start..=end {
                assert!(matches!(art.remove(&i), Some(val) if val == i.to_string()));
                assert!(matches!(art.get(&i), None));
            }
        }
    }

    #[test]
    fn modifications_with_seq_keys_with_increasing_size() {
        let mut art = Art::new();
        for i in 0..=u8::MAX {
            let key = vec_key(i);
            assert!(art.insert(key.clone(), i.to_string()), "{}", i);
            assert!(matches!(art.get(&key), Some(val) if val == &i.to_string()));
        }
        for i in 0..=u8::MAX {
            let key = vec_key(i);
            assert!(matches!(art.get(&key), Some(val) if val == &i.to_string()));
        }

        for i in u8::MAX as u16 + 1..=u16::MAX {
            let key = vec_key(i);
            assert!(art.insert(key.clone(), i.to_string()), "{}", i);
            assert!(matches!(art.get(&key), Some(val) if val == &i.to_string()));
        }
        for i in u8::MAX as u16 + 1..=u16::MAX {
            let key = vec_key(i);
            assert!(matches!(art.get(&key), Some(val) if val == &i.to_string()));
        }

        for i in u16::MAX as u32 + 1..=(1 << 21) as u32 {
            let key = vec_key(i);
            assert!(art.insert(key.clone(), i.to_string()), "{}", i);
            assert!(matches!(art.get(&key), Some(val) if val == &i.to_string()));
        }
        for i in u16::MAX as u32 + 1..=(1 << 21) as u32 {
            let key = vec_key(i);
            assert!(matches!(art.get(&key), Some(val) if val == &i.to_string()));
        }

        for i in 0..=u8::MAX {
            let key = vec_key(i);
            assert!(matches!(art.remove(&key), Some(val) if val == i.to_string()));
        }

        for i in u8::MAX as u16 + 1..=u16::MAX {
            let key = vec_key(i);
            assert!(matches!(art.remove(&key), Some(val) if val == i.to_string()));
        }

        for i in u16::MAX as u32 + 1..=(1 << 21) as u32 {
            let key = vec_key(i);
            assert!(matches!(art.remove(&key), Some(val) if val == i.to_string()));
        }
    }

    #[test]
    fn insert_with_long_prefix() {
        let mut art = Art::new();
        long_prefix_test(&mut art, |art, key| {
            let vk = vec_key(key.clone());
            assert!(art.insert(vk.clone(), key.clone()), "{}", key);
            assert!(matches!(art.get(&vk), Some(val) if val == &key));
        });
    }

    #[test]
    fn mixed_upsert_and_delete() {
        let mut art = Art::new();
        let mut existing = HashSet::new();
        long_prefix_test(&mut art, |art, key| {
            // let vk = vec_key(key.clone());
            if thread_rng().gen_bool(0.3) && !existing.is_empty() {
                let key: &String = existing.iter().choose(&mut thread_rng()).unwrap();
                let key = key.clone();
                art.remove(&key[..].as_bytes().to_vec()).unwrap();
                existing.remove(&key);
            } else {
                art.upsert(key.as_bytes().to_vec(), key.clone());
                existing.insert(key);
            }
        });

        let res: Vec<&String> = art.iter().map(|(_, v)| v).collect();
        let mut expected: Vec<&String> = existing.iter().collect();
        expected.sort();
        assert_eq!(expected, res);
    }

    #[test]
    fn upsert() {
        let mut art = Art::new();
        let mut existing = HashSet::new();
        long_prefix_test(&mut art, |art, key| {
            let vk = vec_key(key.clone());
            if existing.insert(key.clone()) {
                art.insert(vk, key);
            }
        });

        for (i, key) in existing.iter().enumerate() {
            let new_val = i.to_string();
            let vk = vec_key(key.clone());
            art.upsert(vk.clone(), new_val.clone());
            assert!(matches!(
                art.get(&vk),
                Some(v) if v == &new_val
            ));
        }
    }

    #[test]
    fn existed_elements_cannot_be_inserted() {
        let mut art = Art::new();
        let mut existing = HashSet::new();
        long_prefix_test(&mut art, |art, key| {
            let vk = vec_key(key.clone());
            if existing.insert(key.clone()) {
                assert!(
                    art.insert(vk, key.clone()),
                    "{} not exist in tree, but insertion failed",
                    key
                );
            } else {
                assert!(
                    !art.insert(vk, key.clone()),
                    "{} already exists but inserted again",
                    key
                );
            }
        });
    }

    #[test]
    fn remove_with_long_prefix() {
        let mut art = Art::new();
        let mut existing = HashSet::new();
        long_prefix_test(&mut art, |art, key| {
            let vk = vec_key(key.clone());
            assert!(art.insert(vk, key.clone()), "{}", key);
            existing.insert(key);
        });

        for key in existing {
            let vk = vec_key(key.clone());
            assert!(
                matches!(art.remove(&vk), Some(val) if val == key.clone()),
                "{}",
                key
            );
            assert!(matches!(art.get(&vk), None));
        }
    }

    fn long_prefix_test<F: FnMut(&mut Art<Vec<u8>, String>, String)>(
        art: &mut Art<Vec<u8>, String>,
        mut test_fn: F,
    ) {
        let mut existing = HashSet::new();
        let mut chars: Vec<char> = ('a'..='z').collect();
        chars.shuffle(&mut thread_rng());
        let chars = &chars[..thread_rng().gen_range(1..chars.len())];
        for i in 0..chars.len() {
            let level1_prefix = chars[i].to_string().repeat(thread_rng().gen_range(1..8));
            for i in 0..chars.len() {
                let level2_prefix = chars[i].to_string().repeat(thread_rng().gen_range(1..8));
                let key_prefix = level1_prefix.clone() + &level2_prefix;
                for _ in 0..=u8::MAX {
                    let suffix: String = (0..thread_rng().gen_range(0..8))
                        .map(|_| chars[thread_rng().gen_range(0..chars.len())])
                        .collect();
                    let string = key_prefix.clone() + &suffix;
                    if !existing.insert(string.clone()) {
                        continue;
                    }
                    test_fn(art, string);
                    if existing.len() >= 10_000 {
                        return;
                    }
                }
            }
        }
    }
}
