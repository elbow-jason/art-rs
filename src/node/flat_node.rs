use super::{InsertError, Node48, NodeOps};
use std::mem;

pub struct FlatNode<V, const N: usize> {
    pub(crate) prefix: Vec<u8>,
    pub(crate) len: usize,
    pub(crate) keys: [u8; N],
    pub(crate) values: [Option<V>; N],
}

// #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
// #[target_feature(enable = "sse2")]
// unsafe fn key_index_sse(key: u8, keys_vec: __m128i, vec_len: usize) -> Option<usize> {
//     debug_assert!(vec_len <= 16);
//     let search_key_vec = _mm_set1_epi8(key as i8);
//     let cmp_res = _mm_cmpeq_epi8(keys_vec, search_key_vec);
//     let zeroes_from_start = _tzcnt_u32(_mm_movemask_epi8(cmp_res) as u32) as usize;
//     if zeroes_from_start >= vec_len {
//         None
//     } else {
//         Some(zeroes_from_start)
//     }
// }

impl<V, const N: usize> FlatNode<V, N> {
    fn remove_index(&mut self, i: usize) -> V {
        let val = mem::replace(&mut self.values[i], None).unwrap();
        self.keys[i] = self.keys[self.len - 1];
        self.values[i] = mem::replace(&mut self.values[self.len - 1], None);
        self.len -= 1;
        val
    }

    fn unchecked_push(&mut self, key: u8, val: V) {
        self.keys[self.len] = key;
        self.values[self.len] = Some(val);
        self.len += 1;
    }
}

impl<V, const N: usize> NodeOps<V> for FlatNode<V, N> {
    fn insert(&mut self, key: u8, val: V) -> Result<(), InsertError<V>> {
        if self.len >= N {
            return Err(InsertError::Overflow(val));
        }

        match self.get_mut(key) {
            Some(_) => Err(InsertError::DuplicateKey),
            None => {
                self.unchecked_push(key, val);
                Ok(())
            }
        }
    }

    fn remove(&mut self, key: u8) -> Option<V> {
        match self.get_key_index(key) {
            None => None,
            Some(i) => Some(self.remove_index(i)),
        }
    }

    fn get_mut(&mut self, key: u8) -> Option<&mut V> {
        match self
            .get_key_index(key)
            .and_then(move |i| self.values.get_mut(i))
        {
            Some(Some(v)) => Some(v),
            _ => None,
        }
    }

    fn drain(mut self) -> Vec<(u8, V)> {
        let mut res = Vec::with_capacity(self.len);
        for i in 0..self.len {
            let value = mem::replace(&mut self.values[i], None).unwrap();
            res.push((self.keys[i], value));
        }

        // emulate that all values was moved out from node before drop
        self.len = 0;
        res
    }
}

impl<V, const N: usize> FlatNode<V, N> {
    pub fn new(prefix: &[u8]) -> Self {
        Self {
            prefix: prefix.to_vec(),
            len: 0,
            keys: [0; N],
            values: array_init::array_init(|_| None),
        }
    }

    fn get_key_index(&self, key: u8) -> Option<usize> {
        // #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
        // unsafe {
        //     if N == 4 {
        //         let keys = _mm_set_epi8(
        //             0,
        //             0,
        //             0,
        //             0,
        //             0,
        //             0,
        //             0,
        //             0,
        //             0,
        //             0,
        //             0,
        //             0,
        //             self.keys[3] as i8,
        //             self.keys[2] as i8,
        //             self.keys[1] as i8,
        //             self.keys[0] as i8,
        //         );
        //         return key_index_sse(key, keys, self.len);
        //     } else if N == 16 {
        //         let keys = _mm_loadu_si128(self.keys.as_ptr() as *const __m128i);
        //         return key_index_sse(key, keys, self.len);
        //     }
        // }

        self.keys[..self.len]
            .iter()
            .enumerate()
            .filter_map(|(i, k)| if *k == key { Some(i) } else { None })
            .next()
    }

    pub(crate) fn resize<const NEW_SIZE: usize>(mut self) -> FlatNode<V, NEW_SIZE> {
        debug_assert!(NEW_SIZE >= self.len);
        let mut new_node = FlatNode::new(&self.prefix);
        new_node.len = self.len;
        new_node.keys[..self.len].copy_from_slice(&self.keys[..self.len]);
        for (v, nn) in self.values.iter_mut().zip(new_node.values.iter_mut()) {
            mem::swap(v, nn);
        }
        // emulate that all values was moved out from node before drop
        self.len = 0;
        new_node
    }

    pub fn iter(&self) -> impl DoubleEndedIterator<Item = &V> {
        let mut kvs: Vec<(u8, &V)> = self.keys[..self.len]
            .iter()
            .zip(self.values[..self.len].iter())
            .map(|(k, v)| (*k, v.as_ref().unwrap()))
            .collect();
        kvs.sort_unstable_by_key(|(k, _)| *k);
        kvs.into_iter().map(|(_, v)| v)
    }
}

impl<V, const N: usize> From<Node48<V>> for FlatNode<V, N> {
    fn from(node: Node48<V>) -> Self {
        debug_assert!(node.len <= N);
        let mut new_node = FlatNode::new(&node.prefix);
        for (k, v) in node.drain() {
            let err = new_node.insert(k as u8, v);
            debug_assert!(err.is_ok());
        }
        new_node
    }
}

pub struct FlatNodeIter<'a, V, const N: usize> {
    node: &'a FlatNode<V, N>,
    index: usize,
}

impl<'a, V, const N: usize> FlatNodeIter<'a, V, N> {
    fn new(node: &'a FlatNode<V, N>) -> FlatNodeIter<'a, V, N> {
        FlatNodeIter { node, index: 0 }
    }
}

impl<'a, V, const N: usize> Iterator for FlatNodeIter<'a, V, N> {
    type Item = (u8, &'a V);

    fn next(&mut self) -> Option<(u8, &'a V)> {
        if self.index >= self.node.len {
            return None;
        }
        let key = *self.node.keys.get(self.index).unwrap();
        let val = self.node.values.get(self.index).unwrap();
        self.index += 1;
        Some((key, val.as_ref().unwrap()))
    }
}

#[test]
fn test_flatnode_iter() {
    let mut f = FlatNode::<i32, 8>::new(b"jas");
    assert!(f.insert(10, 20).is_ok());
    assert!(f.insert(30, 40).is_ok());
    assert!(f.insert(50, 60).is_ok());
    assert!(f.insert(70, 80).is_ok());
    assert_eq!(f.keys, [10u8, 30, 50, 70, 0, 0, 0, 0]);
    assert_eq!(
        f.values,
        [
            Some(20i32),
            Some(40),
            Some(60),
            Some(80),
            None,
            None,
            None,
            None
        ]
    );
    let mut it = FlatNodeIter::new(&f);
    assert_eq!(it.next(), Some((10, &20)));
    assert_eq!(it.next(), Some((30, &40)));
    assert_eq!(it.next(), Some((50, &60)));
    assert_eq!(it.next(), Some((70, &80)));
    assert_eq!(it.next(), None);
}
