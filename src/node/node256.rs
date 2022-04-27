use super::{InsertError, Node48, NodeOps};

pub struct Node256<V> {
    pub(crate) prefix: Vec<u8>,
    pub(crate) len: usize,
    pub(crate) values: [Option<V>; 256],
}

impl<V> NodeOps<V> for Node256<V> {
    fn insert(&mut self, key: u8, value: V) -> Option<InsertError<V>> {
        let i = key as usize;
        if self.values[i].is_none() {
            self.values[i] = Some(value);
            self.len += 1;
            None
        } else {
            Some(InsertError::DuplicateKey)
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

    pub(crate) fn iter(&self) -> impl DoubleEndedIterator<Item = &V> {
        self.values.iter().filter_map(|v| v.as_ref())
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
