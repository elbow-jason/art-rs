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

impl Key for &[u8] {
    fn to_bytes(&self) -> KeyBuffer {
        KeyBuffer::Slice(self)
    }
}

impl Key for &Vec<u8> {
    fn to_bytes(&self) -> KeyBuffer {
        KeyBuffer::Slice(self)
    }
}

impl Key for String {
    fn to_bytes(&self) -> KeyBuffer {
        KeyBuffer::Slice(self.as_bytes())
    }
}

impl Key for &String {
    fn to_bytes(&self) -> KeyBuffer {
        KeyBuffer::Slice(self.as_bytes())
    }
}

impl Key for &str {
    fn to_bytes(&self) -> KeyBuffer {
        KeyBuffer::Slice(self.as_bytes())
    }
}

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

fn build_arr<const N: usize>(a: &[u8], b: &[u8]) -> [u8; N] {
    let a_len = a.len();
    array_init::array_init(|i| {
        if i < a_len {
            *a.get(i).unwrap()
        } else {
            *b.get(i - a_len).unwrap()
        }
    })
}

impl<A: Key, B: Key> Key for (A, B) {
    fn to_bytes(&self) -> KeyBuffer {
        let a_buf = self.0.to_bytes();
        let b_buf = self.0.to_bytes();
        let a = a_buf.as_slice();
        let b = b_buf.as_slice();
        let a_len = a.len();
        let b_len = b.len();
        if a_len == 0 {
            return b_buf;
        }
        if b_len == 0 {
            return a_buf;
        }
        match a_len + b_len {
            1 => KeyBuffer::L1(build_arr(a, b)),
            2 => KeyBuffer::L2(build_arr(a, b)),
            4 => KeyBuffer::L4(build_arr(a, b)),
            8 => KeyBuffer::L8(build_arr(a, b)),
            16 => KeyBuffer::L16(build_arr(a, b)),
            _ => {
                let mut a_vec = a.to_vec();
                a_vec.extend(b);
                KeyBuffer::Vec(a_vec)
            }
        }
    }
}

impl Key for Vec<u8> {
    fn to_bytes(&self) -> KeyBuffer {
        KeyBuffer::Slice(&self[..])
    }
}

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

impl Key for f32 {
    fn to_bytes(&self) -> KeyBuffer {
        let f = Float32::from(*self);
        KeyBuffer::L4(f.key)
    }
}

impl Key for f64 {
    fn to_bytes(&self) -> KeyBuffer {
        let f = Float64::from(*self);
        KeyBuffer::L8(f.key)
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
