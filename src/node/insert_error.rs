pub enum InsertError<V> {
    DuplicateKey,
    Overflow(V),
}
