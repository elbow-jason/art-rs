use super::InsertError;

pub trait NodeOps<V> {
    fn insert(&mut self, key: u8, value: V) -> Option<InsertError<V>>;
    fn remove(&mut self, key: u8) -> Option<V>;
    fn get_mut(&mut self, key: u8) -> Option<&mut V>;
    fn drain(self) -> Vec<(u8, V)>;
}
