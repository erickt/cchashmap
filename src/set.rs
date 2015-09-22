use std::borrow::Borrow;
use std::fmt;
use std::hash::{Hash, Hasher, SipHasher};
use std::iter::FromIterator;
use std::slice;

use bucket::{self, Bucket};

use quickcheck;

static DEFAULT_CAPACITY: usize = 4096;

#[derive(Clone)]
pub struct CCHashSet {
    buckets: Vec<Bucket>,
    len: usize,
}

impl CCHashSet {
    pub fn new() -> Self {
        CCHashSet::with_capacity(DEFAULT_CAPACITY)
    }

    pub fn with_capacity(len: usize) -> Self {
        CCHashSet {
            buckets: vec![Bucket::new(); len],
            len: 0,
        }
    }

    pub fn len(&self) -> usize {
        self.len
    }

    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    pub fn insert<T>(&mut self, key: T) -> bool
        where T: Borrow<[u8]>
    {
        let key = key.borrow();

        let inserted = {
            let bucket = self.get_bucket_mut(key);
            let contains = bucket.contains(key);

            if !contains {
                bucket.push(key);
            }

            !contains
        };

        if inserted {
            self.len += 1;
        }

        inserted
    }

    pub fn contains<T>(&self, key: T) -> bool
        where T: Borrow<[u8]>
    {
        let key = key.borrow();
        self.get_bucket(key).contains(key)
    }

    pub fn iter(&self) -> Iter {
        Iter {
            iter: self.buckets.iter(),
            bucket_iter: None,
            len: self.len,
        }
    }

    fn get_bucket_index(&self, key: &[u8]) -> usize {
        let mut hasher = SipHasher::new();
        key.hash(&mut hasher);
        let hash = hasher.finish() as usize;

        hash % self.buckets.len()
    }

    fn get_bucket(&self, key: &[u8]) -> &Bucket {
        let index = self.get_bucket_index(key);
        &self.buckets[index]
    }

    fn get_bucket_mut(&mut self, key: &[u8]) -> &mut Bucket {
        let index = self.get_bucket_index(key);
        &mut self.buckets[index]
    }
}

pub struct Iter<'a> {
    iter: slice::Iter<'a, Bucket>,
    bucket_iter: Option<bucket::Iter<'a>>,
    len: usize,
}

impl<'a> Iterator for Iter<'a> {
    type Item = &'a [u8];

    fn next(&mut self) -> Option<&'a [u8]> {
        loop {
            match self.bucket_iter {
                Some(ref mut iter) => {
                    match iter.next() {
                        Some(key) => {
                            self.len -= 1;
                            return Some(key);
                        }
                        None => { }
                    }
                }
                None => { }
            }

            match self.iter.next() {
                Some(bucket) => { self.bucket_iter = Some(bucket.iter()); }
                None => { return None; }
            }
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len, Some(self.len))
    }
}

impl<T> FromIterator<T> for CCHashSet
    where T: Borrow<[u8]>,
{
    fn from_iter<I: IntoIterator<Item=T>>(iterator: I) -> Self {
        let mut set = CCHashSet::new();
        for key in iterator.into_iter() {
            set.insert(key);
        }
        set
    }
}

impl quickcheck::Arbitrary for CCHashSet {
    fn arbitrary<G: quickcheck::Gen>(g: &mut G) -> CCHashSet {
        let keys: Vec<Vec<u8>> = quickcheck::Arbitrary::arbitrary(g);
        CCHashSet::from_iter(keys.iter().map(|key| &**key))
    }

    fn shrink(&self) -> Box<Iterator<Item=CCHashSet>> {
        let keys: Vec<Vec<u8>> = self.iter().map(|key| key.to_owned()).collect();
        Box::new(keys.shrink().map(|keys| keys.iter().map(|key| &**key).collect::<CCHashSet>()))
    }
}

impl fmt::Debug for CCHashSet {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_set().entries(self.iter()).finish()
    }
}
