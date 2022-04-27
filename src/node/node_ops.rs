use thiserror::Error as ThisError;

#[derive(ThisError, Debug)]
pub enum InsertError<V> {
    #[error("insert error - duplicate key")]
    DuplicateKey,

    #[error("insert error - node overflow")]
    Overflow(V),
}

pub trait NodeOps<V> {
    fn insert(&mut self, key: u8, value: V) -> Result<(), InsertError<V>>;
    fn remove(&mut self, key: u8) -> Option<V>;
    fn get_mut(&mut self, key: u8) -> Option<&mut V>;
    fn drain(self) -> Vec<(u8, V)>;
}
