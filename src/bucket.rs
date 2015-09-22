use std::iter::FromIterator;
use std::borrow::Borrow;

use byteorder::{ByteOrder, NativeEndian};
use quickcheck::{self, Arbitrary};

#[derive(Clone, Debug)]
pub struct Bucket {
    array: Vec<u8>,
    len: usize,
}

impl Bucket {
    pub fn new() -> Self {
        Bucket {
            array: Vec::new(),
            len: 0,
        }
    }

    pub fn with_capacity(len: usize) -> Self {
        Bucket {
            array: Vec::with_capacity(len),
            len: 0,
        }
    }

    pub fn from_slice<T: Borrow<[u8]>>(slice: &[T]) -> Self {
        let len = slice.iter().fold(0, |sum, key| sum + key.borrow().len());
        let mut bucket = Bucket::with_capacity(len);
        for key in slice.iter() {
            bucket.push(key.borrow());
        }
        bucket
    }

    pub fn contains(&self, key: &[u8]) -> bool {
        self.iter().any(|k| k == key)
    }

    pub fn len(&self) -> usize {
        self.len
    }

    /// Appends the key without looking to see if it's already in the bucket.
    pub fn push(&mut self, key: &[u8]) {
        // First we encode the length;
        let len = key.len();
        if len < 128 {
            self.array.push((len << 1) as u8);
        } else {
            assert!(len < ::std::u16::MAX as usize);

            // The least significant bit is set to indicate that two bytes are being used to store
            // the length.
            let len = ((len << 1) as u16) | 0x1;
            let mut len_slice = [0; 2];
            NativeEndian::write_u16(&mut len_slice, len);

            self.array.extend(&len_slice);
        }
        
        self.array.extend(key);

        self.len += 1;
    }

    pub fn iter(&self) -> Iter {
        Iter {
            array: &self.array,
            len: self.len,
        }
    }
}

fn read_len(slice: &[u8]) -> (usize, &[u8]) {
    let byte = slice[0];
    if 0x1 & byte == 0 {
        ((byte as usize) >> 1, &slice[1..])
    } else {
        ((NativeEndian::read_u16(slice) >> 1) as usize, &slice[2..])
    }
}

pub struct Iter<'a> {
    array: &'a [u8],
    len: usize,
}

impl<'a> Iterator for Iter<'a> {
    type Item = &'a [u8];

    fn next(&mut self) -> Option<&'a [u8]> {
        if self.array.is_empty() {
            None
        } else {
            self.len -= 1;

            // Read the length.
            let (len, array) = read_len(self.array);

            // Read the key.
            let (key, array) = array.split_at(len);
            self.array = array;

            Some(key)
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len, Some(self.len))
    }
}

impl<T> FromIterator<T> for Bucket
    where T: Borrow<[u8]>,
{
    fn from_iter<I: IntoIterator<Item=T>>(iterator: I) -> Self {
        let iterator = iterator.into_iter();

        let mut bucket = Bucket::with_capacity(iterator.size_hint().0);

        for key in iterator.into_iter() {
            bucket.push(key.borrow());
        }

        bucket
    }
}

impl Arbitrary for Bucket {
    fn arbitrary<G: quickcheck::Gen>(g: &mut G) -> Bucket {
        let keys: Vec<Vec<u8>> = Arbitrary::arbitrary(g);
        Bucket::from_iter(keys.iter().map(|key| &**key))
    }

    fn shrink(&self) -> Box<Iterator<Item=Bucket>> {
        let keys: Vec<Vec<u8>> = self.iter().map(|key| key.to_owned()).collect();
        Box::new(keys.shrink().map(|keys| keys.iter().map(|key| &**key).collect::<Bucket>()))
    }
}
