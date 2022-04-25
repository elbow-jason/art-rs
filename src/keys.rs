use std::borrow::Borrow;
use std::cmp::Ordering;
use std::mem;

pub enum KeyBuffer<'a> {
    L1([u8; 1]),
    L2([u8; 2]),
    L4([u8; 4]),
    L8([u8; 8]),
    L16([u8; 16]),
    Vec(Vec<u8>),
    Slice(&'a [u8]),
}

impl<'a> KeyBuffer<'a> {
    pub fn as_slice(&'a self) -> &'a [u8] {
        match self {
            KeyBuffer::L1(v) => &v[..],
            KeyBuffer::L2(v) => &v[..],
            KeyBuffer::L4(v) => &v[..],
            KeyBuffer::L8(v) => &v[..],
            KeyBuffer::L16(v) => &v[..],
            KeyBuffer::Vec(v) => &v[..],
            KeyBuffer::Slice(v) => &v[..],
        }
    }
}

// impl Deref for KeyBuffer {
//     type Target = [u8];

//     fn deref(&self) -> &[u8] {
//         self.as_slice()
//     }
// }

/// Trait represent [Art](crate::Art) key.
/// Trait define method which convert key into byte comparable sequence. This sequence will be
/// used to order keys inside tree.
pub trait Key: Clone {
    // type Bytes: AsRef<[u8]>;
    /// Converts key to byte comparable sequence. This sequence used to represent key inside
    /// [Art] tree.
    ///
    /// ## Warning
    /// Implementation must ensure that returned bytes vector have consistent order of bytes. E.g.
    /// key type must have same ordering guarantees as returned byte sequence.  
    /// For instance, if `"abc" < "def"`, then `"abc".to_bytes() < "def".to_bytes()`.
    /// Violation of this rule is **undefined behaviour** and can cause `panic`.
    fn to_bytes<'a>(&'a self) -> KeyBuffer<'a>;
}

/// Implementation of [Key] which wraps bytes slice. It can be used to represent strings as
/// comparable byte sequence.
#[derive(Clone, PartialOrd, Ord, Debug)]
#[repr(transparent)]
pub struct ByteString {
    bytes: Vec<u8>,
}

impl ByteString {
    pub fn new(bytes: &[u8]) -> Self {
        Self {
            bytes: bytes.to_vec(),
        }
    }
}

// impl Borrow<[u8]> for ByteString {
//     fn borrow(&self) -> &[u8] {
//         &self.bytes
//     }
// }

impl Key for ByteString {
    fn to_bytes(&self) -> KeyBuffer {
        KeyBuffer::Slice(&self.bytes[..])
    }
}

impl Eq for ByteString {}

impl PartialEq for ByteString {
    fn eq(&self, other: &Self) -> bool {
        self.bytes == other.bytes
    }
}

macro_rules! impl_key {
    ($t:ty, $s:ident) => {
        impl Key for $t {
            fn to_bytes(&self) -> KeyBuffer {
                KeyBuffer::$s(self.to_be_bytes())
            }
        }
    };
}

// const SIZEOF_USIZE: usize = std::mem::size_of::<usize>();

impl_key!(u128, L16);
impl_key!(usize, L8);
impl_key!(u64, L8);
impl_key!(u32, L4);
impl_key!(u16, L2);
impl_key!(u8, L1);

impl Key for i8 {
    fn to_bytes(&self) -> KeyBuffer {
        // flip upper bit of signed value to get comparable byte sequence:
        // -128 => 0
        // -127 => 1
        // 0 => 128
        // 1 => 129
        // 127 => 255
        let v: u8 = unsafe { mem::transmute(*self) };
        // flip upper bit and set to 0 other bits:
        // (0000_1100 ^ 1000_0000) & 1000_0000 = 1000_0000
        // (1000_1100 ^ 1000_0000) & 1000_0000 = 0000_0000
        let i = (v ^ 0x80) & 0x80;
        // repair bits(except upper bit) of value:
        // self = -127
        // i = 0 (0b0000_0000)
        // v = 129 (0b1000_0001)
        // j = 0b0000_0000 | (0b1000_0001 & 0b0111_1111) = 0b0000_0000 | 0b0000_0001 = 0b0000_0001 = 1
        let j = i | (v & 0x7F);
        KeyBuffer::L1(j.to_be_bytes())
    }
}

impl Key for i16 {
    fn to_bytes(&self) -> KeyBuffer {
        let v: u16 = unsafe { mem::transmute(*self) };
        let xor = 1 << 15;
        let i = (v ^ xor) & xor;
        let j = i | (v & (u16::MAX >> 1));
        KeyBuffer::L2(j.to_be_bytes())
    }
}

impl Key for i32 {
    fn to_bytes(&self) -> KeyBuffer {
        let v: u32 = unsafe { mem::transmute(*self) };
        let xor = 1 << 31;
        let i = (v ^ xor) & xor;
        let j = i | (v & (u32::MAX >> 1));
        KeyBuffer::L4(j.to_be_bytes())
    }
}

impl Key for i64 {
    fn to_bytes(&self) -> KeyBuffer {
        let v: u64 = unsafe { mem::transmute(*self) };
        let xor = 1 << 63;
        let i = (v ^ xor) & xor;
        let j = i | (v & (u64::MAX >> 1));
        KeyBuffer::L8(j.to_be_bytes())
    }
}

impl Key for i128 {
    fn to_bytes(&self) -> KeyBuffer {
        let v: u128 = unsafe { mem::transmute(*self) };
        let xor = 1 << 127;
        let i = (v ^ xor) & xor;
        let j = i | (v & (u128::MAX >> 1));
        KeyBuffer::L16(j.to_be_bytes())
    }
}

/// Type to represent `f32` keys
#[derive(Clone, Debug)]
#[repr(transparent)]
pub struct Float32 {
    key: [u8; 4],
}

impl Borrow<[u8]> for Float32 {
    fn borrow(&self) -> &[u8] {
        &self.key
    }
}

impl Eq for Float32 {}

impl PartialEq<Float32> for Float32 {
    fn eq(&self, other: &Self) -> bool {
        self.key == other.key
    }
}

impl Ord for Float32 {
    fn cmp(&self, other: &Self) -> Ordering {
        self.partial_cmp(other).unwrap()
    }
}

impl PartialOrd<Float32> for Float32 {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.key.cmp(&other.key))
    }
}

impl From<f32> for Float32 {
    fn from(v: f32) -> Self {
        let v: u32 = v.to_bits();
        let xor = 1 << 31;
        let i = (v ^ xor) & xor;
        let j = i | (v & (u32::MAX >> 1));
        Self {
            key: j.to_be_bytes(),
        }
    }
}

/// Type to represent `f64` keys
#[derive(Clone, Debug)]
#[repr(transparent)]
pub struct Float64 {
    key: [u8; 8],
}

impl Borrow<[u8]> for Float64 {
    fn borrow(&self) -> &[u8] {
        &self.key
    }
}

impl Eq for Float64 {}

impl PartialEq<Float64> for Float64 {
    fn eq(&self, other: &Self) -> bool {
        self.key == other.key
    }
}

impl Ord for Float64 {
    fn cmp(&self, other: &Self) -> Ordering {
        self.partial_cmp(other).unwrap()
    }
}

impl PartialOrd<Float64> for Float64 {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.key.cmp(&other.key))
    }
}

impl From<f64> for Float64 {
    fn from(v: f64) -> Self {
        let v: u64 = v.to_bits();
        let xor = 1 << 63;
        let i = (v ^ xor) & xor;
        let j = i | (v & (u64::MAX >> 1));
        Self {
            key: j.to_be_bytes(),
        }
    }
}

impl Key for Float32 {
    fn to_bytes(&self) -> KeyBuffer {
        KeyBuffer::L4(self.key)
    }
}

impl Key for Float64 {
    fn to_bytes(&self) -> KeyBuffer {
        KeyBuffer::L8(self.key)
    }
}

/// Builder to create keys based on several other keys.
///
/// For instance, we have a structure:
/// ```
/// struct MyStruct(u8, String, u32, Box<f64>);
/// ```
/// and we want to store this structure inside [Art](crate::Art) tree. This structure can identified
/// by first 2 fields: `(u8, String)`. We can create compound key based on them and use it as
/// tree key.
/// ```
/// use art_tree::Art;
/// use art_tree::KeyBuilder;
/// use art_tree::ByteString;
///
/// struct MyStruct(u8, String, u32, Box<f64>);
///
/// let mut art = Art::new();
/// let key = KeyBuilder::new().append(1).append(ByteString::new("abc".to_string().as_bytes())).build();
/// let val = MyStruct(1, "abc".to_string(), 200, Box::new(0.1));
/// assert!(art.insert(key.clone(), val));
/// assert!(art.get(&key).is_some());
/// ```
#[repr(transparent)]
pub struct KeyBuilder {
    key: ByteString,
}

impl Default for KeyBuilder {
    fn default() -> Self {
        Self::new()
    }
}

impl KeyBuilder {
    pub fn new() -> Self {
        Self {
            key: ByteString { bytes: Vec::new() },
        }
    }

    pub fn with_capacity(cap: usize) -> Self {
        Self {
            key: ByteString {
                bytes: Vec::with_capacity(cap),
            },
        }
    }

    pub fn append<K: Key>(mut self, key_part: K) -> Self {
        for b in key_part.to_bytes().as_slice() {
            self.key.bytes.push(*b);
        }

        self
    }

    pub fn build(self) -> ByteString {
        self.key
    }
}
