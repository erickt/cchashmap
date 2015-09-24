use std::borrow::Borrow;
use std::fmt;
use std::iter::FromIterator;
use std::marker::PhantomData;
use std::mem;
use std::ops::Index;
use std::ptr;
use std::slice;

use quickcheck::{self, Arbitrary};

#[derive(Clone)]
pub struct ArrayMap<V> {
    buf: Vec<u8>,
    len: usize,
    _marker: PhantomData<V>,
}

impl<V> ArrayMap<V> {
    pub fn new() -> Self {
        ArrayMap::with_capacity(0)
    }

    pub fn with_capacity(cap: usize) -> Self {
        ArrayMap {
            buf: Vec::with_capacity(cap),
            len: 0,
            _marker: PhantomData,
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
        // FIXME: Replace with `std::intrinsics::drop_in_place` once stabilized.
        // For now, just let drain take care of dropping all our items.
        for _ in self.drain() {}
        self.buf.clear();
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
    /// use std::collections::HashMap;
    ///
    /// let mut map = HashMap::new();
    /// map.insert(1, "a");
    /// assert_eq!(map.get(&1), Some(&"a"));
    /// assert_eq!(map.get(&2), None);
    /// ```
    #[inline]
    pub fn get<K>(&self, key: K) -> Option<&V>
        where K: Borrow<[u8]>
    {
        let key = key.borrow();

        unsafe {
            for item in self.iter_raw() {
                if item.key() == key {
                    return Some(item.value_ref());
                }
            }
        }

        None
    }

    /// Returns true if the map contains a value for the specified key.
    ///
    /// The key may be any borrowed form of the map's key type, but
    /// `Hash` and `Eq` on the borrowed form *must* match those for
    /// the key type.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::HashMap;
    ///
    /// let mut map = HashMap::new();
    /// map.insert(1, "a");
    /// assert_eq!(map.contains_key(&1), true);
    /// assert_eq!(map.contains_key(&2), false);
    /// ```
    pub fn contains_key<K>(&self, key: K) -> bool
        where K: Borrow<[u8]>
    {
        self.get(key.borrow()).is_some()
    }

    /// Returns a mutable reference to the value corresponding to the key.
    ///
    /// The key may be any borrowed form of the map's key type, but
    /// `Hash` and `Eq` on the borrowed form *must* match those for
    /// the key type.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::HashMap;
    ///
    /// let mut map = HashMap::new();
    /// map.insert(1, "a");
    /// if let Some(x) = map.get_mut(&1) {
    ///     *x = "b";
    /// }
    /// assert_eq!(map[&1], "b");
    /// ```
    pub fn get_mut<K>(&mut self, key: K) -> Option<&mut V>
        where K: Borrow<[u8]>
    {
        let key = key.borrow();
        self.iter_mut().find(|&(k, _)| key == k).map(|(_, v)| v)
    }

    /// Inserts a key-value pair into the map. If the key already had a value
    /// present in the map, that value is returned. Otherwise, `None` is returned.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::HashMap;
    ///
    /// let mut map = HashMap::new();
    /// assert_eq!(map.insert(37, "a"), None);
    /// assert_eq!(map.is_empty(), false);
    ///
    /// map.insert(37, "b");
    /// assert_eq!(map.insert(37, "c"), Some("b"));
    /// assert_eq!(map[&37], "c");
    /// ```
    pub fn insert(&mut self, key: &[u8], value: V) -> bool {
        for (k, v) in self.iter_mut() {
            if key == k {
                *v = value;
                return true;
            }
        }

        self.push(key, value);

        false
    }

    /// Removes a key from the map, returning the value at the key if the key
    /// was previously in the map.
    ///
    /// The key may be any borrowed form of the map's key type, but
    /// `Hash` and `Eq` on the borrowed form *must* match those for
    /// the key type.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::HashMap;
    ///
    /// let mut map = HashMap::new();
    /// map.insert(1, "a");
    /// assert_eq!(map.remove(&1), Some("a"));
    /// assert_eq!(map.remove(&1), None);
    /// ```
    pub fn remove(&mut self, key: &[u8]) -> Option<V> {
        if self.is_empty() {
            return None;
        }

        unsafe {
            let item = self.iter_raw()
                .find(|item| item.key() == key)
                .map(|item| (item.value_index(), item.next_index()));

            match item {
                Some((value_index, next_index)) => Some(self.remove_at(value_index, next_index)),
                None => None,
            }
        }
    }

    unsafe fn remove_at(&mut self, value_index: usize, next_index: usize) -> V {
        let buf_ptr = self.buf.as_ptr();
        let value_ptr = buf_ptr.offset(value_index as isize);
        let next_ptr = buf_ptr.offset(next_index as isize);
        let remaining_items = self.buf.len() - next_index;

        let value: V = ptr::read(value_ptr as *const V);

        // Truncate the buffer so we don't drop the value twice if there's a panic.
        self.buf.set_len(value_index);

        // Move the remaining items into this item's spot.
        ptr::copy(next_ptr, value_ptr as *mut u8, remaining_items);

        self.buf.set_len(value_index + remaining_items);

        value
    }

    unsafe fn get_value_at<'a>(&'a self, index: usize) -> &'a V {
        mem::transmute(self.buf.as_ptr().offset(index as isize))
    }

    unsafe fn get_mut_value_at<'a>(&'a mut self, index: usize) -> &'a mut V {
        mem::transmute(self.buf.as_mut_ptr().offset(index as isize))
    }

    /// Gets the given key's corresponding entry in the map for in-place manipulation.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::HashMap;
    ///
    /// let mut letters = HashMap::new();
    ///
    /// for ch in "a short treatise on fungi".chars() {
    ///     let counter = letters.entry(ch).or_insert(0);
    ///     *counter += 1;
    /// }
    ///
    /// assert_eq!(letters[&'s'], 2);
    /// assert_eq!(letters[&'t'], 3);
    /// assert_eq!(letters[&'u'], 1);
    /// assert_eq!(letters.get(&'y'), None);
    /// ```
    pub fn entry<'a, 'b>(&'a mut self, key: &'b [u8]) -> Entry<'a, 'b, V> {
        unsafe {
            let item = self.iter_raw()
                .find(|item| item.key() == key)
                .map(|item| (item.value_index(), item.next_index()));

            match item {
                Some((value_index, next_index)) => {
                    Entry::Occupied(OccupiedEntry {
                        array: self,
                        value_index: value_index,
                        next_index: next_index,
                    })
                }
                None => {
                    Entry::Vacant(VacantEntry {
                        array: self,
                        key: key,
                    })
                }
            }
        }
    }

    pub fn iter<'a>(&'a self) -> Iter<'a, V> {
        unsafe {
            Iter {
                iter: self.iter_raw(),
            }
        }
    }

    pub fn iter_mut<'a>(&'a mut self) -> IterMut<'a, V> {
        unsafe {
            IterMut {
                iter: self.iter_raw(),
            }
        }
    }

    pub fn drain<'a>(&'a mut self) -> Drain<'a, V> {
        // Memory safety
        //
        // When the Drain is first created, it shortens the length of
        // the source vector to make sure no uninitalized or moved-from elements
        // are accessible at all if the Drain's destructor never gets to run.
        //
        // Drain will ptr::read out the values to remove.
        // When finished, remaining tail of the vec is copied back to cover
        // the hole, and the vector length is restored to the new length.
        //
        let buf_len = self.buf.len();
        let len = self.len;

        unsafe {
            // set self.buf length's to start, to be safe in case Drain is leaked
            self.buf.set_len(0);
            self.len = 0;

            Drain {
                iter: self.iter_raw_len(buf_len, len),
            }
        }
    }

    #[inline]
    unsafe fn iter_raw<'a>(&'a self) -> IterRaw<'a, V> {
        self.iter_raw_len(self.buf.len(), self.len)
    }

    #[inline]
    unsafe fn iter_raw_len<'a>(&'a self, end: usize, len: usize) -> IterRaw<'a, V> {
        IterRaw {
            array: self,
            index: 0,
            end: end,
            len: len,
        }
    }

    #[inline]
    fn push(&mut self, key: &[u8], value: V) -> &mut V {
        unsafe {
            let buf_len = self.buf.len();

            // First, make sure we reserve enough space to write everything.
            // FIXME: Account for alignment.
            let len_len = mem::size_of::<usize>();
            let key_len = key.len();
            let value_len = mem::size_of::<V>();
            let len = buf_len + len_len + key_len + value_len;
            self.buf.reserve_exact(len);

            // Grab a pointer that's pointing to the end of the space.
            let mut end = self.buf.as_mut_ptr().offset(buf_len as isize);

            // First, write the value.
            ptr::write(end as *mut V, value);
            end = end.offset(value_len as isize);

            // Next, write the length at the end and adjust the pointer.
            ptr::write(end as *mut usize, key_len);
            end = end.offset(len_len as isize);

            // Next, write the key.
            ptr::copy_nonoverlapping(key.as_ptr(), end, key_len);
            end = end.offset(key_len as isize);

            // Finally, adjust the buffer length.
            self.buf.set_len(len);
            self.len += 1;

            mem::transmute(end)
        }
    }

    #[inline]
    fn raw_item_at(&self, index: usize, end: usize) -> Option<RawItem<V>> {
        if index == end {
            None
        } else {
            Some(RawItem {
                ptr: self.buf.as_ptr(),
                index: index,
                _marker: PhantomData,
            })
        }
    }
}

impl<T> Drop for ArrayMap<T> {
    fn drop(&mut self) {
        // FIXME: Replace with `std::intrinsics::drop_in_place` once stabilized.
        // For now, just let drain take care of dropping all our items.
        self.drain();
    }
}

impl<'a, K, V> Index<&'a K> for ArrayMap<V>
    where K: Borrow<[u8]>
{
    type Output = V;

    #[inline]
    fn index(&self, key: &K) -> &V {
        self.get(key.borrow()).expect("no entry found for key")
    }
}

impl<K, V> FromIterator<(K, V)> for ArrayMap<V>
    where K: Borrow<[u8]>,
{
    fn from_iter<I: IntoIterator<Item=(K, V)>>(iterator: I) -> Self {
        let iterator = iterator.into_iter();

        let mut bucket = ArrayMap::with_capacity(iterator.size_hint().0);

        for (key, value) in iterator.into_iter() {
            bucket.insert(key.borrow(), value);
        }

        bucket
    }
}

impl<V> fmt::Debug for ArrayMap<V> where V: fmt::Debug {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_set().entries(self.iter()).finish()
    }
}

struct RawItem<'a, V: 'a> {
    ptr: *const u8,
    index: usize,
    _marker: PhantomData<&'a V>,
}

impl<'a, V> RawItem<'a, V> {
    #[inline(always)]
    fn key_len_index(&self) -> usize {
        self.value_index() + mem::size_of::<V>()
    }

    #[inline(always)]
    fn key_index(&self) -> usize {
        self.key_len_index() + mem::size_of::<usize>()
    }

    #[inline(always)]
    fn value_index(&self) -> usize {
        self.index
    }

    #[inline(always)]
    fn next_index(&self) -> usize {
        self.key_index() + self.key_len()
    }

    #[inline(always)]
    fn key_len(&self) -> usize {
        unsafe {
            ptr::read(self.ptr.offset(self.key_len_index() as isize) as *const usize)
        }
    }

    #[inline(always)]
    fn key(&self) -> &'a [u8] {
        unsafe {
            slice::from_raw_parts(
                self.ptr.offset(self.key_index() as isize),
                self.key_len())
        }
    }

    #[inline(always)]
    fn value_ptr(&self) -> *const V {
        unsafe {
            self.ptr.offset(self.value_index() as isize) as *const V
        }
    }

    #[inline(always)]
    fn value(&self) -> V {
        unsafe {
            ptr::read(self.value_ptr())
        }
    }

    #[inline(always)]
    fn value_ref(&self) -> &'a V {
        unsafe {
            mem::transmute(self.value_ptr())
        }
    }

    #[inline(always)]
    fn value_ref_mut(&self) -> &'a mut V {
        unsafe {
            mem::transmute(self.value_ptr())
        }
    }
}


struct IterRaw<'a, V: 'a> {
    array: &'a ArrayMap<V>,
    index: usize,
    end: usize,
    len: usize,
}

impl<'a, V> Iterator for IterRaw<'a, V> {
    type Item = RawItem<'a, V>;

    #[inline(always)]
    fn next(&mut self) -> Option<RawItem<'a, V>> {
        match self.array.raw_item_at(self.index, self.end) {
            Some(raw_item) => {
                self.len -= 1;
                self.index = raw_item.next_index();
                Some(raw_item)
            }
            None => None,
        }
    }

    #[inline(always)]
    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len, Some(self.len))
    }
}



macro_rules! iterator {
    (struct $name:ident -> $elem:ty, $read:ident) => {
        impl<'a, V> Iterator for $name<'a, V> {
            type Item = (&'a [u8], $elem);

            #[inline]
            fn next(&mut self) -> Option<(&'a [u8], $elem)> {
                self.iter.next().map(|item| (item.key(), item.$read()))
            }

            fn size_hint(&self) -> (usize, Option<usize>) {
                self.iter.size_hint()
            }
        }
    }
}

pub struct Iter<'a, V: 'a> {
    iter: IterRaw<'a, V>,
}

iterator! { struct Iter -> &'a V, value_ref }

pub struct IterMut<'a, V: 'a> {
    iter: IterRaw<'a, V>,
}

iterator! { struct IterMut -> &'a mut V, value_ref_mut }

pub struct Drain<'a, V: 'a> {
    iter: IterRaw<'a, V>,
}

iterator! { struct Drain -> V, value }

unsafe impl<'a, T: Sync> Sync for Drain<'a, T> {}
unsafe impl<'a, T: Send> Send for Drain<'a, T> {}

impl<'a, T> Drop for Drain<'a, T> {
    fn drop(&mut self) {
        // exhaust self first
        while let Some(_) = self.next() { }
    }
}

//iterator! { struct IntoIter -> *mut u8, &'a mut V }

/// A view into a single entry in a map, which may either be vacant or occupied.
pub enum Entry<'a, 'b, V: 'a> {
    /// A vacant Entry
    Vacant(VacantEntry<'a, 'b, V>),

    /// An occupied Entry
    Occupied(OccupiedEntry<'a, V>),
}

/// A vacant Entry.
pub struct VacantEntry<'a, 'b, V: 'a> {
    array: &'a mut ArrayMap<V>,
    key: &'b [u8],
}

/// An occupied Entry.
pub struct OccupiedEntry<'a, V: 'a> {
    array: &'a mut ArrayMap<V>,
    value_index: usize,
    next_index: usize,
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
        unsafe {
            self.array.get_value_at(self.value_index)
        }
    }

    /// Gets a mutable reference to the value in the entry.
    pub fn get_mut(&mut self) -> &mut V {
        unsafe {
            self.array.get_mut_value_at(self.value_index)
        }
    }

    /// Converts the OccupiedEntry into a mutable reference to the value in the entry
    /// with a lifetime bound to the map itself
    pub fn into_mut(self) -> &'a mut V {
        unsafe {
            self.array.get_mut_value_at(self.value_index)
        }
    }

    /// Sets the value of the entry, and returns the entry's old value
    pub fn insert(&mut self, mut value: V) -> V {
        let old_value = self.get_mut();
        mem::swap(&mut value, old_value);
        value
    }

    /// Takes the value out of the entry, and returns it
    pub fn remove(self) -> V {
        unsafe {
            self.array.remove_at(self.value_index, self.next_index)
        }
    }
}

impl<'a, 'b, V: 'a> VacantEntry<'a, 'b, V> {
    /// Sets the value of the entry with the VacantEntry's key,
    /// and returns a mutable reference to it
    pub fn insert(self, value: V) -> &'a mut V {
        self.array.push(self.key, value)
    }
}

impl<V> Arbitrary for ArrayMap<V> where V: Arbitrary {
    fn arbitrary<G: quickcheck::Gen>(g: &mut G) -> ArrayMap<V> {
        use std::collections::HashMap;
        let keys: HashMap<Vec<u8>, V> = Arbitrary::arbitrary(g);
        ArrayMap::from_iter(keys.into_iter())
    }

    fn shrink(&self) -> Box<Iterator<Item=ArrayMap<V>>> {
        use std::collections::HashMap;
        let keys: HashMap<Vec<u8>, V> = self.iter().map(|(k, v)| (k.to_owned(), v.clone())).collect();
        Box::new(keys.shrink().map(|keys| ArrayMap::from_iter(keys.into_iter())))
    }
}
