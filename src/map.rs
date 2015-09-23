use std::borrow::Borrow;
use std::fmt;
use std::hash::{Hash, Hasher, SipHasher};
use std::iter::{self, FromIterator};
use std::slice;

use array::{self, Array};

use quickcheck;

static DEFAULT_CAPACITY: usize = 4096;

#[derive(Clone)]
pub struct CCHashMap<V> {
    buckets: Vec<Array<V>>,
    len: usize,
}

impl<V> CCHashMap<V> {
    pub fn new() -> Self {
        CCHashMap::with_capacity(DEFAULT_CAPACITY)
    }

    pub fn with_capacity(len: usize) -> Self {
        assert!(len > 0);

        CCHashMap {
            buckets: Vec::from_iter((0..len).map(|_| Array::new())),
            len: 0,
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
        self.len
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
        self.len == 0
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
        for bucket in self.buckets.iter_mut() {
            bucket.clear();
        }
    }

    pub fn insert<T>(&mut self, key: T, value: V) -> bool
        where T: Borrow<[u8]>
    {
        let key = key.borrow();

        let inserted = {
            let bucket = self.get_bucket_mut(key);
            let contains = bucket.contains_key(key);

            if !contains {
                bucket.insert(key, value);
            }

            !contains
        };

        if inserted {
            self.len += 1;
        }

        inserted
    }

    pub fn contains_key<T>(&self, key: T) -> bool
        where T: Borrow<[u8]>
    {
        let key = key.borrow();
        self.get_bucket(key).contains_key(key)
    }

    pub fn iter<'a>(&'a self) -> Iter<'a, V> {
        Iter {
            iter: self.buckets.iter(),
            bucket_iter: None,
            len: self.len,
        }
    }

    /// Gets an iterator over the keys of the map.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::BTreeMap;
    ///
    /// let mut a = BTreeMap::new();
    /// a.insert(1, "a");
    /// a.insert(2, "b");
    ///
    /// let keys: Vec<_> = a.keys().cloned().collect();
    /// assert_eq!(keys, [1, 2]);
    /// ```
    pub fn keys<'a>(&'a self) -> Keys<'a, V> {
        fn first<A, B>((a, _): (A, B)) -> A { a }
        let first: fn((&'a [u8], &'a V)) -> &'a [u8] = first; // coerce to fn pointer

        Keys { inner: self.iter().map(first) }
    }

    /// Gets an iterator over the values of the map.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::BTreeMap;
    ///
    /// let mut a = BTreeMap::new();
    /// a.insert(1, "a");
    /// a.insert(2, "b");
    ///
    /// let values: Vec<&str> = a.values().cloned().collect();
    /// assert_eq!(values, ["a", "b"]);
    /// ```
    pub fn values<'a>(&'a self) -> Values<'a, V> {
        fn second<A, B>((_, b): (A, B)) -> B { b }
        let second: fn((&'a [u8], &'a V)) -> &'a V = second; // coerce to fn pointer

        Values { inner: self.iter().map(second) }
    }

    fn get_bucket_index(&self, key: &[u8]) -> usize {
        let mut hasher = SipHasher::new();
        key.hash(&mut hasher);
        let hash = hasher.finish() as usize;

        hash % self.buckets.len()
    }

    fn get_bucket(&self, key: &[u8]) -> &Array<V> {
        let index = self.get_bucket_index(key);
        &self.buckets[index]
    }

    fn get_bucket_mut(&mut self, key: &[u8]) -> &mut Array<V> {
        let index = self.get_bucket_index(key);
        &mut self.buckets[index]
    }
}

pub struct Iter<'a, V: 'a> {
    iter: slice::Iter<'a, Array<V>>,
    bucket_iter: Option<array::Iter<'a, V>>,
    len: usize,
}

impl<'a, V> Iterator for Iter<'a, V> {
    type Item = (&'a [u8], &'a V);

    fn next(&mut self) -> Option<(&'a [u8], &'a V)> {
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

/// An iterator over a ArrayMap's keys.
pub struct Keys<'a, V: 'a> {
    inner: iter::Map<Iter<'a, V>, fn((&'a [u8], &'a V)) -> &'a [u8]>
}

/// An iterator over a ArrayMap's values.
pub struct Values<'a, V: 'a> {
    inner: iter::Map<Iter<'a, V>, fn((&'a [u8], &'a V)) -> &'a V>
}

impl<'a, V> Iterator for Keys<'a, V> {
    type Item = &'a [u8];

    fn next(&mut self) -> Option<&'a [u8]> { self.inner.next() }
    fn size_hint(&self) -> (usize, Option<usize>) { self.inner.size_hint() }
}

impl<'a, V> Iterator for Values<'a, V> {
    type Item = &'a V;

    fn next(&mut self) -> Option<&'a V> { self.inner.next() }
    fn size_hint(&self) -> (usize, Option<usize>) { self.inner.size_hint() }
}

impl<K, V> FromIterator<(K, V)> for CCHashMap<V>
    where K: Borrow<[u8]>,
{
    fn from_iter<I: IntoIterator<Item=(K, V)>>(iterator: I) -> Self {
        let mut map = CCHashMap::new();
        for (key, value) in iterator.into_iter() {
            map.insert(key, value);
        }
        map
    }
}

impl<V> quickcheck::Arbitrary for CCHashMap<V>
    where V: Clone + quickcheck::Arbitrary,
{
    fn arbitrary<G: quickcheck::Gen>(g: &mut G) -> CCHashMap<V> {
        use std::collections::HashMap;

        let items: HashMap<Vec<u8>, V> = quickcheck::Arbitrary::arbitrary(g);
        CCHashMap::from_iter(items.into_iter())
    }

    fn shrink(&self) -> Box<Iterator<Item=CCHashMap<V>>> {
        use std::collections::HashMap;

        let items: HashMap<Vec<u8>, V> = self.iter()
            .map(|(key, value)| (key.to_owned(), value.clone()))
            .collect();

        Box::new(items.shrink()
            .map(|items| items.into_iter().collect::<CCHashMap<V>>()))
    }
}

impl<V> fmt::Debug for CCHashMap<V>
    where V: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_map().entries(self.iter()).finish()
    }
}
