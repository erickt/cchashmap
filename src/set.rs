use std::borrow::Borrow;
use std::convert::AsRef;
use std::fmt;
use std::iter::FromIterator;

use map::{self, CCHashMap};

use quickcheck;

#[derive(Clone)]
pub struct CCHashSet {
    map: CCHashMap<()>,
}

impl CCHashSet {
    pub fn new() -> Self {
        CCHashSet {
            map: CCHashMap::new(),
        }
    }

    pub fn with_capacity(len: usize) -> Self {
        CCHashSet {
            map: CCHashMap::with_capacity(len),
        }
    }

    /// Returns the number of elements in the set.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::BTreeSet;
    ///
    /// let mut v = BTreeSet::new();
    /// assert_eq!(v.len(), 0);
    /// v.insert(1);
    /// assert_eq!(v.len(), 1);
    /// ```
    pub fn len(&self) -> usize {
        self.map.len()
    }

    /// Returns true if the set contains no elements.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::BTreeSet;
    ///
    /// let mut v = BTreeSet::new();
    /// assert!(v.is_empty());
    /// v.insert(1);
    /// assert!(!v.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.map.is_empty()
    }

    /// Clears the set, removing all values.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::BTreeSet;
    ///
    /// let mut v = BTreeSet::new();
    /// v.insert(1);
    /// v.clear();
    /// assert!(v.is_empty());
    /// ```
    pub fn clear(&mut self) {
        self.map.clear()
    }

    /// Adds a value to the set. Returns `true` if the value was not already
    /// present in the set.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::BTreeSet;
    ///
    /// let mut set = BTreeSet::new();
    ///
    /// assert_eq!(set.insert(2), true);
    /// assert_eq!(set.insert(2), false);
    /// assert_eq!(set.len(), 1);
    /// ```
    pub fn insert<T>(&mut self, key: T) -> bool
        where T: Borrow<[u8]>
    {
        self.map.insert(key, ()).is_none()
    }

    /// Gets an iterator over the BTreeSet's contents.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::BTreeSet;
    ///
    /// let set: BTreeSet<usize> = [1, 2, 3, 4].iter().cloned().collect();
    ///
    /// for x in set.iter() {
    ///     println!("{}", x);
    /// }
    ///
    /// let v: Vec<_> = set.iter().cloned().collect();
    /// assert_eq!(v, [1, 2, 3, 4]);
    /// ```
    pub fn iter(&self) -> Iter {
        Iter { inner: self.map.keys() }
    }

    /// Returns `true` if the set contains a value.
    ///
    /// The value may be any borrowed form of the set's value type,
    /// but the ordering on the borrowed form *must* match the
    /// ordering on the value type.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::BTreeSet;
    ///
    /// let set: BTreeSet<_> = [1, 2, 3].iter().cloned().collect();
    /// assert_eq!(set.contains(&1), true);
    /// assert_eq!(set.contains(&4), false);
    /// ```
    pub fn contains<T>(&self, value: T) -> bool
        where T: Borrow<[u8]>
    {
        self.map.contains_key(value)
    }
}

/// An iterator over a ArrayMap's keys.
pub struct Iter<'a> {
    inner: map::Keys<'a, ()>,
}

impl<'a> Iterator for Iter<'a> {
    type Item = &'a [u8];

    fn next(&mut self) -> Option<&'a [u8]> { self.inner.next() }
    fn size_hint(&self) -> (usize, Option<usize>) { self.inner.size_hint() }
}

/*
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
*/

impl<T> FromIterator<T> for CCHashSet
    where T: Borrow<[u8]>,
{
    fn from_iter<I: IntoIterator<Item=T>>(iterator: I) -> Self {
        CCHashSet {
            map: CCHashMap::from_iter(iterator.into_iter().map(|key| (key, ()))),
        }
    }
}

impl quickcheck::Arbitrary for CCHashSet {
    fn arbitrary<G: quickcheck::Gen>(g: &mut G) -> CCHashSet {
        CCHashSet {
            map: quickcheck::Arbitrary::arbitrary(g),
        }
    }

    fn shrink(&self) -> Box<Iterator<Item=CCHashSet>> {
        Box::new(self.map.shrink().map(|map| CCHashSet { map: map }))
    }
}

impl fmt::Debug for CCHashSet {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_set().entries(self.iter()).finish()
    }
}
