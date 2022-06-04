pub enum InsertStatus<V> {
    Ok,
    DuplicateKey,
    // The owned value in Overflow allows us to pass an owned value back up the
    // tree stack when there is an overflow
    Overflow(V),
}

impl<V> InsertStatus<V> {
    pub fn is_ok(&self) -> bool {
        match self {
            InsertStatus::Ok => true,
            _ => false,
        }
    }

    #[cfg(test)]
    pub fn is_err(&self) -> bool {
        !self.is_ok()
    }

    #[cfg(test)]
    pub fn unwrap(&self) {
        match self {
            InsertStatus::Ok => {}
            InsertStatus::DuplicateKey => panic!("insert status error - duplicate key"),
            InsertStatus::Overflow(_) => panic!("insert status error - overflow"),
        }
    }
}

pub trait NodeOps<V> {
    fn insert(&mut self, key: u8, value: V) -> InsertStatus<V>;
    fn remove(&mut self, key: u8) -> Option<V>;
    fn get_mut(&mut self, key: u8) -> Option<&mut V>;
    fn drain(self) -> Vec<(u8, V)>;
}
