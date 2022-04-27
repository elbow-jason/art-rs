use paste::paste;
use std::borrow::Borrow;
use std::cmp::Ordering;
use std::mem;

macro_rules! build_key_buffer {
    ([ $( $n:literal ),* ]) => {
        paste! {
            pub enum KeyBuffer<'a> {
                Vec(Vec<u8>),
                Slice(&'a [u8]),
                $(
                    [<Arr $n>]([u8; $n]),
                )*
            }
        }
        paste! {
            impl<'a> KeyBuffer<'a> {
                pub fn as_slice(&'a self) -> &'a [u8] {
                    use KeyBuffer::*;
                    match self {
                        KeyBuffer::Vec(v) => &v[..],
                        KeyBuffer::Slice(v) => &v[..],
                        $(
                            [<Arr $n>](v) => &v[..],
                        )*
                    }
                }
            }
            $(
                impl<'a> From<[u8; $n]> for KeyBuffer<'a> {
                    fn from(a: [u8; $n]) -> KeyBuffer<'a> {
                        use KeyBuffer::*;
                        [<Arr $n>](a)
                    }
                }
            )*
        }

        paste! {
            impl<'a> KeyBuffer<'a> {
                pub fn concat_slices(a: &[u8], b: &[u8]) -> KeyBuffer<'a> {
                    use KeyBuffer::*;
                    let a_len = a.len();
                    let b_len = b.len();
                    match a_len + b_len {
                        $(
                            $n => [<Arr $n>](build_arr(a, b)),
                        )*
                        _ => {
                            let mut a_vec = a.to_vec();
                            a_vec.extend(b);
                            KeyBuffer::Vec(a_vec)
                        }
                    }
                }
            }
        }
    }
}

build_key_buffer!([
    1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26,
    27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50,
    51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74,
    75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98,
    99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117,
    118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136,
    137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155,
    156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174,
    175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193,
    194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212,
    213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231,
    232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248
]);

impl<'a> KeyBuffer<'a> {
    fn is_empty(&self) -> bool {
        match self {
            KeyBuffer::Vec(v) => v.is_empty(),
            KeyBuffer::Slice(v) => v.is_empty(),
            _ => false,
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

impl_key!(u128, Arr16);
impl_key!(usize, Arr8);
impl_key!(u64, Arr8);
impl_key!(u32, Arr4);
impl_key!(u16, Arr2);
impl_key!(u8, Arr1);

#[inline(always)]
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
        if a_buf.is_empty() {
            return b_buf;
        }
        if b_buf.is_empty() {
            return a_buf;
        }
        KeyBuffer::concat_slices(a_buf.as_slice(), b_buf.as_slice())
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
        j.to_be_bytes().into()
    }
}

impl Key for i16 {
    fn to_bytes(&self) -> KeyBuffer {
        let v: u16 = unsafe { mem::transmute(*self) };
        let xor = 1 << 15;
        let i = (v ^ xor) & xor;
        let j = i | (v & (u16::MAX >> 1));
        j.to_be_bytes().into()
    }
}

impl Key for i32 {
    fn to_bytes(&self) -> KeyBuffer {
        let v: u32 = unsafe { mem::transmute(*self) };
        let xor = 1 << 31;
        let i = (v ^ xor) & xor;
        let j = i | (v & (u32::MAX >> 1));
        j.to_be_bytes().into()
    }
}

impl Key for i64 {
    fn to_bytes(&self) -> KeyBuffer {
        let v: u64 = unsafe { mem::transmute(*self) };
        let xor = 1 << 63;
        let i = (v ^ xor) & xor;
        let j = i | (v & (u64::MAX >> 1));
        j.to_be_bytes().into()
    }
}

impl Key for i128 {
    fn to_bytes(&self) -> KeyBuffer {
        let v: u128 = unsafe { mem::transmute(*self) };
        let xor = 1 << 127;
        let i = (v ^ xor) & xor;
        let j = i | (v & (u128::MAX >> 1));
        j.to_be_bytes().into()
    }
}

impl Key for f32 {
    fn to_bytes(&self) -> KeyBuffer {
        let f = Float32::from(*self);
        f.key.into()
    }
}

impl Key for f64 {
    fn to_bytes(&self) -> KeyBuffer {
        let f = Float64::from(*self);
        f.key.into()
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
        self.key.into()
    }
}

impl Key for Float64 {
    fn to_bytes(&self) -> KeyBuffer {
        self.key.into()
    }
}

#[test]
fn test_sizeof_key_buffer_is_256() {
    let s = std::mem::size_of::<KeyBuffer>();
    assert_eq!(s, 256);
}
