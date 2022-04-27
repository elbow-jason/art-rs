use std::cmp::Ordering;
use std::fmt;

pub struct Leaf<K, V> {
    pub key: K,
    pub val: V,
}

impl<K: fmt::Debug, V: fmt::Debug> fmt::Debug for Leaf<K, V> {
    // This trait requires `fmt` with this exact signature.
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_struct("Leaf")
            .field("key", &self.key)
            .field("val", &self.val)
            .finish()
    }
}

impl<K, V> Leaf<K, V> {
    pub fn new(key: K, val: V) -> Self {
        Self { key, val }
    }
}

impl<K: PartialEq, V> PartialEq for Leaf<K, V> {
    fn eq(&self, other: &Self) -> bool {
        self.key == other.key
    }
}

impl<K: Eq, V> Eq for Leaf<K, V> {}

impl<K: PartialOrd, V> PartialOrd for Leaf<K, V> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.key.partial_cmp(&other.key)
    }
}

impl<K: Ord, V> Ord for Leaf<K, V> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.key.cmp(&other.key)
    }
}
