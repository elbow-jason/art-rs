use super::{FlatNode, InsertError, Node256, NodeOps};
use std::mem;

pub struct Node48<V> {
    pub(crate) prefix: Vec<u8>,
    pub(crate) len: usize,
    pub(crate) keys: [u8; 256],
    pub(crate) values: [Option<V>; 48],
}

impl<V> NodeOps<V> for Node48<V> {
    fn insert(&mut self, key: u8, value: V) -> Option<InsertError<V>> {
        let i = key as usize;
        if self.keys[i] != 0 {
            return Some(InsertError::DuplicateKey);
        }
        if self.len >= 48 {
            return Some(InsertError::Overflow(value));
        }

        self.values[self.len as usize] = Some(value);
        self.keys[i] = self.len as u8 + 1;
        self.len += 1;
        None
    }

    fn remove(&mut self, key: u8) -> Option<V> {
        let key_idx = key as usize;
        if self.keys[key_idx] == 0 {
            return None;
        }
        let val_idx = self.keys[key_idx] as usize - 1;
        let val = mem::replace(&mut self.values[val_idx], None).unwrap();
        self.keys[key_idx] = 0;

        if self.len == 1 {
            self.len = 0;
            return Some(val);
        }

        #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
        unsafe {
            for offset in (0..256).step_by(16) {
                let keys = _mm_loadu_si128(self.keys[offset..].as_ptr() as *const __m128i);
                if let Some(i) = key_index_sse(self.len as u8, keys, 16).map(|i| i + offset) {
                    // move value of key which points to last array cell of values
                    self.keys[i] = val_idx as u8 + 1;
                    self.values[val_idx] = mem::replace(&mut self.values[self.len - 1], None);
                    break;
                }
            }
            self.len -= 1;
            return Some(val);
        };

        for i in 0..self.keys.len() {
            // find key which uses last cell inside values array
            if self.keys[i] == self.len as u8 {
                // move value of key which points to last array cell
                self.keys[i] = val_idx as u8 + 1;
                self.values[val_idx] = mem::replace(&mut self.values[self.len - 1], None);
                break;
            }
        }
        self.len -= 1;
        Some(val)
    }

    fn get_mut(&mut self, key: u8) -> Option<&mut V> {
        let i = self.keys[key as usize] as usize;
        if i > 0 {
            return match self.values.get_mut(i - 1).unwrap() {
                Some(v) => Some(v),
                None => None,
            };
        }
        None
    }

    fn drain(mut self) -> Vec<(u8, V)> {
        let mut res = Vec::with_capacity(self.len);
        for (k, v) in self.keys.iter().enumerate().filter(|(_, v)| **v > 0) {
            let val_idx = *v as usize;
            let value = mem::replace(&mut self.values[val_idx - 1], None).unwrap();
            res.push((k as u8, value));
        }

        // emulate that all values was moved out from node before drop
        self.len = 0;
        res
    }
}

impl<V> Node48<V> {
    pub(crate) fn new(prefix: &[u8]) -> Self {
        Self {
            prefix: prefix.to_vec(),
            len: 0,
            keys: [0; 256],
            values: array_init::array_init(|_| None),
        }
    }

    pub(crate) fn iter(&self) -> impl DoubleEndedIterator<Item = &V> {
        let slice = &self.values[..];
        self.keys.iter().filter_map(move |k| match *k {
            0 => None,
            i_plus_one => slice.get((i_plus_one - 1) as usize).unwrap().as_ref(),
        })
    }
}

impl<V> From<Node256<V>> for Node48<V> {
    fn from(node: Node256<V>) -> Node48<V> {
        debug_assert!(node.len <= 48);
        let mut new_node = Node48::new(&node.prefix);
        for (k, v) in node.drain() {
            new_node.values[new_node.len as usize] = Some(v);
            new_node.keys[k as usize] = new_node.len as u8 + 1;
            new_node.len += 1;
        }
        new_node
    }
}

impl<V, const N: usize> From<FlatNode<V, N>> for Node48<V> {
    fn from(node: FlatNode<V, N>) -> Node48<V> {
        debug_assert!(node.len <= 48);
        let mut new_node = Node48::new(&node.prefix);
        for (k, v) in node.drain() {
            new_node.values[new_node.len] = Some(v);
            new_node.keys[k as usize] = new_node.len as u8 + 1;
            new_node.len += 1;
        }
        new_node
    }
}
