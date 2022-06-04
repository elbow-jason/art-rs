use super::{InsertStatus, Node48, NodeOps};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Node256<V> {
    pub(crate) prefix: Vec<u8>,
    pub(crate) len: usize,
    pub(crate) values: [Option<V>; 256],
}

impl<V> NodeOps<V> for Node256<V> {
    fn insert(&mut self, key: u8, value: V) -> InsertStatus<V> {
        let i = key as usize;
        if self.values[i].is_none() {
            self.values[i] = Some(value);
            self.len += 1;
            InsertStatus::Ok
        } else {
            InsertStatus::DuplicateKey
        }
    }

    fn remove(&mut self, key: u8) -> Option<V> {
        let i = key as usize;
        self.values[i].take().map(|v| {
            self.len -= 1;
            v
        })
    }

    fn get_mut(&mut self, key: u8) -> Option<&mut V> {
        self.values[key as usize].as_mut()
    }

    fn drain(mut self) -> Vec<(u8, V)> {
        let mut res = Vec::with_capacity(self.len);
        for i in 0..self.values.len() {
            if let Some(v) = self.values[i].take() {
                res.push((i as u8, v))
            }
        }

        // emulate that all values was moved out from node before drop
        self.len = 0;
        res
    }
}

impl<V> Node256<V> {
    pub(crate) fn new(prefix: &[u8]) -> Self {
        Self {
            prefix: prefix.to_vec(),
            len: 0,
            values: array_init::array_init(|_| None),
        }
    }

    pub(crate) fn iter<'a>(&'a self) -> Node256Iter<'a, V> {
        Node256Iter::new(self)
        // self.values.iter().filter_map(|v| v.as_ref())
    }
}

impl<V> From<Node48<V>> for Node256<V> {
    fn from(node: Node48<V>) -> Self {
        let mut new_node = Node256::new(&node.prefix);
        for (k, v) in node.drain() {
            new_node.values[k as usize] = Some(v);
            new_node.len += 1;
        }

        new_node
    }
}

pub struct Node256Iter<'a, V> {
    values: &'a [Option<V>],
    lo: u16,
    hi: u16,
}

impl<'a, V> Node256Iter<'a, V> {
    fn new(node: &'a Node256<V>) -> Node256Iter<'a, V> {
        Node256Iter {
            values: &node.values[..],
            lo: 0,
            hi: 256,
        }
    }

    fn is_empty(&self) -> bool {
        self.hi <= self.lo
    }
}

impl<'a, V> Iterator for Node256Iter<'a, V> {
    type Item = &'a V;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            if self.is_empty() {
                return None;
            }
            let val = self.values.get(self.lo as usize).unwrap().as_ref();
            self.lo += 1;
            if val.is_none() {
                continue;
            }
            return val;
        }
    }
}

impl<'a, V> DoubleEndedIterator for Node256Iter<'a, V> {
    fn next_back(&mut self) -> Option<&'a V> {
        loop {
            if self.is_empty() {
                return None;
            }
            self.hi -= 1;
            let val = self.values.get(self.hi as usize).unwrap().as_ref();
            if val.is_none() {
                continue;
            }
            return val;
        }
    }
}

#[test]
fn test_node256_iterator_next() {
    let mut f = Node256::<i32>::new(b"jas");
    assert!(f.insert(10, 20).is_ok());
    assert!(f.insert(30, 40).is_ok());
    assert!(f.insert(50, 60).is_ok());
    assert!(f.insert(70, 80).is_ok());
    assert_eq!(f.values[10], Some(20));
    assert_eq!(f.values[30], Some(40));
    assert_eq!(f.values[50], Some(60));
    assert_eq!(f.values[70], Some(80));
    assert_eq!(f.values[71], None);
    let mut it = Node256Iter::new(&f);
    assert_eq!(it.next(), Some(&20));
    assert_eq!(it.next(), Some(&40));
    assert_eq!(it.next(), Some(&60));
    assert_eq!(it.next(), Some(&80));
    assert_eq!(it.next(), None);
}

#[test]
fn test_node256_double_ended_iterator_next_back() {
    let mut f = Node256::<i32>::new(b"jas");
    assert!(f.insert(10, 20).is_ok());
    assert!(f.insert(30, 40).is_ok());
    assert!(f.insert(50, 60).is_ok());
    assert!(f.insert(70, 80).is_ok());
    let mut it = Node256Iter::new(&f);
    assert_eq!(it.next_back(), Some(&80));
    assert_eq!(it.next(), Some(&20));
    assert_eq!(it.next_back(), Some(&60));
    assert_eq!(it.next(), Some(&40));
    assert_eq!(it.next_back(), None);
    assert_eq!(it.next(), None);
}
