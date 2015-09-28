use std::borrow::Borrow;
use std::fmt;
use std::hash::{Hash, Hasher, SipHasher};
use std::iter::{self, FromIterator};
use std::ops::Index;
use std::slice;

use array::{self, ArrayMap};

use quickcheck;

static DEFAULT_CAPACITY: usize = 4096;

#[derive(Clone)]
pub struct CCHashMap<V> {
    pub buckets: Vec<ArrayMap<V>>,
    len: usize,
}

impl<V> CCHashMap<V> {
    pub fn new() -> Self {
        CCHashMap::with_capacity(DEFAULT_CAPACITY)
    }

    pub fn with_capacity(len: usize) -> Self {
        assert!(len > 0);

        CCHashMap {
            buckets: Vec::from_iter((0..len).map(|_| ArrayMap::new())),
            len: 0,
        }
    }

    /// Returns the number of elements in the set.
    ///
    /// # Examples
    ///
    /// ```
    /// use cchashmap::CCHashMap;
    ///
    /// let mut v = CCHashMap::new();
    /// assert_eq!(v.len(), 0);
    /// v.insert(&b"1"[..], 1);
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
    /// use cchashmap::CCHashMap;
    ///
    /// let mut v = CCHashMap::new();
    /// assert!(v.is_empty());
    /// v.insert(&b"1"[..], 1);
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
    /// use cchashmap::CCHashMap;
    ///
    /// let mut v = CCHashMap::new();
    /// v.insert(&b"1"[..], 1);
    /// v.clear();
    /// assert!(v.is_empty());
    /// ```
    pub fn clear(&mut self) {
        for bucket in self.buckets.iter_mut() {
            bucket.clear();
        }
        self.len = 0;
    }

    pub fn contains_key<K>(&self, key: K) -> bool
        where K: Borrow<[u8]>
    {
        let key = key.borrow();
        self.get_bucket(key).contains_key(key)
    }

    /// Returns a reference to the value corresponding to the key.
    ///
    /// The key may be any borrowed form of the map's key type, but
    /// `Hash` and `Eq` on the borrowed form *must* match those for
    /// the key type.
    ///
    /// # Examples
    ///
    /// ```
    /// use cchashmap::CCHashMap;
    ///
    /// let mut map = CCHashMap::new();
    /// map.insert(&b"1"[..], "a");
    /// assert_eq!(map.get(&b"1"[..]), Some(&"a"));
    /// assert_eq!(map.get(&b"2"[..]), None);
    /// ```
    pub fn get<K>(&self, key: K) -> Option<&V>
        where K: Borrow<[u8]>
    {
        let key = key.borrow();
        self.get_bucket(key).get(key)
    }

    /// Returns a mutable reference to the value corresponding to the key.
    ///
    /// The key may be any borrowed form of the map's key type, but the ordering
    /// on the borrowed form *must* match the ordering on the key type.
    ///
    /// # Examples
    ///
    /// ```
    /// use cchashmap::CCHashMap;
    ///
    /// let mut map = CCHashMap::new();
    /// map.insert(&b"1"[..], "a");
    /// if let Some(x) = map.get_mut(&b"1"[..]) {
    ///     *x = "b";
    /// }
    /// assert_eq!(map.get(&b"1"[..]), Some(&"b"));
    /// ```
    pub fn get_mut<K>(&mut self, key: K) -> Option<&mut V>
        where K: Borrow<[u8]>
    {
        let key = key.borrow();
        self.get_bucket_mut(key).get_mut(key)
    }

    /// Inserts a key-value pair into the map. If the key already had a value
    /// present in the map, that value is returned. Otherwise, `None` is returned.
    ///
    /// # Examples
    ///
    /// ```
    /// use cchashmap::CCHashMap;
    ///
    /// let mut map = CCHashMap::new();
    /// assert_eq!(map.insert(&b"37"[..], "a"), None);
    /// assert_eq!(map.is_empty(), false);
    ///
    /// map.insert(&b"37"[..], "b");
    /// assert_eq!(map.insert(&b"37"[..], "c"), Some("b"));
    /// assert_eq!(map.get(&b"37"[..]), Some(&"c"));
    /// ```
    pub fn insert<T>(&mut self, key: T, value: V) -> Option<V>
        where T: Borrow<[u8]>
    {
        let key = key.borrow();
        let old_value = self.get_bucket_mut(key).insert(key, value);

        if old_value.is_none() {
            self.len += 1;
        }

        old_value
    }

    /// Removes a key from the map, returning the value at the key if the key
    /// was previously in the map.
    ///
    /// The key may be any borrowed form of the map's key type, but the ordering
    /// on the borrowed form *must* match the ordering on the key type.
    ///
    /// # Examples
    ///
    /// ```
    /// use cchashmap::CCHashMap;
    ///
    /// let mut map = CCHashMap::new();
    /// map.insert(&b"1"[..], "a");
    /// assert_eq!(map.remove(&b"1"[..]), Some("a"));
    /// assert_eq!(map.remove(&b"1"[..]), None);
    /// ```
    pub fn remove<K>(&mut self, key: K) -> Option<V>
        where K: Borrow<[u8]>
    {
        let key = key.borrow();
        self.get_bucket_mut(key).remove(key)
    }

    pub fn iter<'a>(&'a self) -> Iter<'a, V> {
        Iter {
            iter: self.buckets.iter(),
            array_iter: None,
            len: self.len,
        }
    }

    /// Gets an iterator over the keys of the map.
    ///
    /// # Examples
    ///
    /// ```
    /// use cchashmap::CCHashMap;
    ///
    /// let mut a = CCHashMap::new();
    /// a.insert(&b"1"[..], "a");
    /// a.insert(&b"2"[..], "b");
    ///
    /// let keys: Vec<_> = a.keys().collect();
    /// assert_eq!(keys, [&b"1"[..], &b"2"[..]]);
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
    /// use cchashmap::CCHashMap;
    ///
    /// let mut a = CCHashMap::new();
    /// a.insert(&b"1"[..], "a");
    /// a.insert(&b"2"[..], "b");
    ///
    /// let values: Vec<&str> = a.values().map(|v| *v).collect();
    /// assert_eq!(values, ["a", "b"]);
    /// ```
    pub fn values<'a>(&'a self) -> Values<'a, V> {
        fn second<A, B>((_, b): (A, B)) -> B { b }
        let second: fn((&'a [u8], &'a V)) -> &'a V = second; // coerce to fn pointer

        Values { inner: self.iter().map(second) }
    }

    pub fn drain<'a>(&'a mut self) -> Drain<'a, V> {
        let &mut CCHashMap { ref mut buckets, ref mut len } = self;

        Drain {
            inner: buckets.iter_mut(),
            array_iter: None,
            len: len,
        }
    }

    /// Gets the given key's corresponding entry in the map for in-place manipulation.
    ///
    /// # Examples
    ///
    /// ```
    /// use cchashmap::CCHashMap;
    ///
    /// let mut letters = CCHashMap::new();
    ///
    /// for ch in "a short treatise on fungi".chars() {
    ///     let counter = letters.entry(ch.to_string().as_bytes()).or_insert(0);
    ///     *counter += 1;
    /// }
    ///
    /// assert_eq!(letters[&*b"s"], 2);
    /// assert_eq!(letters[&*b"t"], 3);
    /// assert_eq!(letters[&*b"u"], 1);
    /// assert_eq!(letters.get(&b"y"[..]), None);
    /// ```
    pub fn entry<'a, 'b>(&'a mut self, key: &'b [u8]) -> Entry<'a, 'b, V> {
        let index = self.get_bucket_index(key);

        let &mut CCHashMap { ref mut buckets, ref mut len } = self;

        match buckets[index].entry(key) {
            array::Entry::Vacant(entry) => {
                Entry::Vacant(VacantEntry {
                    len: len,
                    entry: entry,
                })
            }
            array::Entry::Occupied(entry) => {
                Entry::Occupied(OccupiedEntry {
                    entry: entry,
                })
            }
        }
    }

    fn get_bucket_index(&self, key: &[u8]) -> usize {
        let mut hasher = SipHasher::new();
        key.hash(&mut hasher);
        let hash = hasher.finish() as usize;

        hash % self.buckets.len()
    }

    fn get_bucket(&self, key: &[u8]) -> &ArrayMap<V> {
        let index = self.get_bucket_index(key);
        &self.buckets[index]
    }

    fn get_bucket_mut(&mut self, key: &[u8]) -> &mut ArrayMap<V> {
        let index = self.get_bucket_index(key);
        &mut self.buckets[index]
    }
}

impl<'a, K, V> Index<&'a K> for CCHashMap<V>
    where K: Borrow<[u8]>
{
    type Output = V;

    #[inline]
    fn index(&self, key: &K) -> &V {
        self.get(key.borrow()).expect("no entry found for key")
    }
}

pub struct Iter<'a, V: 'a> {
    iter: slice::Iter<'a, ArrayMap<V>>,
    array_iter: Option<array::Iter<'a, V>>,
    len: usize,
}

impl<'a, V> Iterator for Iter<'a, V> {
    type Item = (&'a [u8], &'a V);

    fn next(&mut self) -> Option<(&'a [u8], &'a V)> {
        loop {
            match self.array_iter {
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
                Some(bucket) => { self.array_iter = Some(bucket.iter()); }
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

pub struct Drain<'a, V: 'a> {
    inner: slice::IterMut<'a, ArrayMap<V>>,
    array_iter: Option<array::Drain<'a, V>>,
    len: &'a mut usize,
}

impl<'a, V> Iterator for Drain<'a, V> {
    type Item = (&'a [u8], V);

    fn next(&mut self) -> Option<(&'a [u8], V)> {
        loop {
            match self.array_iter {
                Some(ref mut iter) => {
                    match iter.next() {
                        Some(key) => {
                            *self.len = *self.len - 1;
                            return Some(key);
                        }
                        None => { }
                    }
                }
                None => { }
            }

            match self.inner.next() {
                Some(array) => { self.array_iter = Some(array.drain()); }
                None => { return None; }
            }
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = *self.len;
        (len, Some(len))
    }
}

impl<'a, V> Drop for Drain<'a, V> {
    fn drop(&mut self) {
        // exhaust self first
        while let Some(_) = self.next() { }
    }
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

/// A view into a single entry in a map, which may either be vacant or occupied.
pub enum Entry<'a, 'b, V: 'a> {
    /// A vacant Entry
    Vacant(VacantEntry<'a, 'b, V>),

    /// An occupied Entry
    Occupied(OccupiedEntry<'a, V>),
}

/// A vacant Entry.
pub struct VacantEntry<'a, 'b, V: 'a> {
    len: &'a mut usize,
    entry: array::VacantEntry<'a, 'b, V>,
}

/// An occupied Entry.
pub struct OccupiedEntry<'a, V: 'a> {
    entry: array::OccupiedEntry<'a, V>,
}

impl<'a, 'b, V> Entry<'a, 'b, V> {
    /// Ensures a value is in the entry by inserting the default if empty, and returns
    /// a mutable reference to the value in the entry.
    pub fn or_insert(self, default: V) -> &'a mut V {
        match self {
            Entry::Occupied(entry) => entry.into_mut(),
            Entry::Vacant(entry) => entry.insert(default),
        }
    }

    /// Ensures a value is in the entry by inserting the result of the default function if empty,
    /// and returns a mutable reference to the value in the entry.
    pub fn or_insert_with<F: FnOnce() -> V>(self, default: F) -> &'a mut V {
        match self {
            Entry::Occupied(entry) => entry.into_mut(),
            Entry::Vacant(entry) => entry.insert(default()),
        }
    }
}

impl<'a, V> OccupiedEntry<'a, V> {
    /// Gets a reference to the value in the entry.
    pub fn get(&self) -> &V {
        self.entry.get()
    }

    /// Gets a mutable reference to the value in the entry.
    pub fn get_mut(&mut self) -> &mut V {
        self.entry.get_mut()
    }

    /// Converts the OccupiedEntry into a mutable reference to the value in the entry
    /// with a lifetime bound to the map itself
    pub fn into_mut(self) -> &'a mut V {
        self.entry.into_mut()
    }

    /// Sets the value of the entry, and returns the entry's old value
    pub fn insert(&mut self, value: V) -> V {
        self.entry.insert(value)
    }

    /// Takes the value out of the entry, and returns it
    pub fn remove(self) -> V {
        self.entry.remove()
    }
}

impl<'a, 'b, V: 'a> VacantEntry<'a, 'b, V> {
    /// Sets the value of the entry with the VacantEntry's key,
    /// and returns a mutable reference to it
    pub fn insert(self, value: V) -> &'a mut V {
        *self.len = *self.len + 1;
        self.entry.insert(value)
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
