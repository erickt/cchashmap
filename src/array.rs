use std::borrow::Borrow;
use std::fmt;
use std::iter::FromIterator;
use std::marker::PhantomData;
use std::mem;
use std::ops::Index;
use std::ptr;
use std::slice;
use std::u16;

use quickcheck::{self, Arbitrary};

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
        // Guestimate how much capacity we will need. Assume keys will be on average 4 bytes long.
        let len_size   = cap.checked_mul(mem::size_of::<usize>())
            .expect("capacity overflow");

        let key_size   = cap.checked_mul(mem::size_of::<*const u8>() * 4)
            .expect("capacity overflow");

        let value_size = cap.checked_mul(mem::size_of::<V>())
            .expect("capacity overflow");

        let size = len_size
            .checked_add(key_size).expect("capacity overflow")
            .checked_add(value_size).expect("capacity overflow");

        ArrayMap::with_capacity_raw(size)
    }

    fn with_capacity_raw(cap: usize) -> Self {
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
            for (key_ptr, key_len, value_ptr) in self.iter_raw() {
                if key == slice::from_raw_parts(key_ptr, key_len) {
                    return Some(mem::transmute(value_ptr));
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
    #[inline(never)]
    pub fn insert(&mut self, key: &[u8], mut value: V) -> Option<V> {
        for (k, v) in self.iter_mut() {
            if key == k {
                mem::swap(v, &mut value);
                return Some(value);
            }
        }

        self.push(key, value);

        None
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
                .find(|&(key_ptr, key_len, _)| key == slice::from_raw_parts(key_ptr, key_len));

            match item {
                Some((key_ptr, key_len, value_ptr)) => Some(self.remove_at(key_ptr, key_len, value_ptr)),
                None => None,
            }
        }
    }

    unsafe fn remove_at(&mut self, key_ptr: *const u8, key_len: usize, value_ptr: *const V) -> V {
        let buf_ptr = self.buf.as_ptr();
        let end_ptr = buf_ptr.offset(self.buf.len() as isize);

        let next_ptr = (value_ptr as *const u8).offset(mem::size_of::<V>() as isize);
        let remaining_bytes = (end_ptr as usize) - (next_ptr as usize);

        // Truncate the buffer so we don't drop the value twice if there's a panic.
        let item_ptr = key_ptr.offset(-(mem::size_of::<usize>() as isize));
        let item_index = (item_ptr as usize) - (buf_ptr as usize);

        self.buf.set_len(item_index);

        // Read out the value. We now own it since the buffer was truncated.
        let value: V = ptr::read(value_ptr);

        // Move the remaining items into this item's spot.
        ptr::copy(next_ptr, value_ptr as *mut u8, remaining_bytes);

        // Finally, restore the length, minus the item we removed.
        self.buf.set_len(item_index + remaining_bytes);

        value
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
                .find(|&(key_ptr, key_len, _)| key == slice::from_raw_parts(key_ptr, key_len));

            match item {
                Some((key_ptr, key_len, value_ptr)) => {
                    Entry::Occupied(OccupiedEntry {
                        array: self,
                        key_ptr: key_ptr,
                        key_len: key_len,
                        value_ptr: value_ptr,
                        _marker: PhantomData,
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
                len: self.len,
                _marker: PhantomData,
            }
        }
    }

    pub fn iter_mut<'a>(&'a mut self) -> IterMut<'a, V> {
        unsafe {
            IterMut {
                iter: self.iter_raw(),
                len: self.len,
                _marker: PhantomData,
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
                iter: self.iter_raw_len(buf_len),
                len: len,
                _marker: PhantomData,
            }
        }
    }

    unsafe fn iter_raw(&self) -> IterRaw<V> {
        self.iter_raw_len(self.buf.len())
    }

    unsafe fn iter_raw_len(&self, end: usize) -> IterRaw<V> {
        let ptr = self.buf.as_ptr();
        IterRaw {
            ptr: ptr,
            end: ptr.offset(end as isize),
            _marker: PhantomData,
        }
    }

    #[inline(never)]
    fn push(&mut self, key: &[u8], value: V) -> &mut V {
        assert!(key.len() < u16::MAX as usize);

        let buf_len = self.buf.len();

        // First, make sure we reserve enough space to write everything.
        // FIXME: Account for alignment.
        let len_len = mem::size_of::<usize>();
        let key_len = key.len();
        let value_len = mem::size_of::<V>();
        let len = buf_len + len_len + key_len + value_len;
        self.buf.reserve(len);

        unsafe {
            // Grab a pointer that's pointing to the end of the space.
            let mut ptr = self.buf.as_mut_ptr().offset(buf_len as isize);

            // Write the length at the end and adjust the pointer.
            ptr::write(ptr as *mut usize, key_len);
            ptr = ptr.offset(len_len as isize);

            // Write the key.
            ptr::copy_nonoverlapping(key.as_ptr(), ptr, key_len);
            ptr = ptr.offset(key_len as isize);

            // Write the value.
            ptr::write(ptr as *mut V, value);

            // Finally, adjust the buffer length.
            self.buf.set_len(len);

            self.len += 1;

            assert!(self.buf.len() <= self.buf.capacity());

            mem::transmute(ptr)
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

impl<T: Clone> Clone for ArrayMap<T> {
    fn clone(&self) -> Self {
        let mut dst = ArrayMap::with_capacity_raw(self.buf.len());

        for (key, value) in self.iter() {
            dst.push(key, value.clone());
        }

        dst
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

unsafe fn raw_item<V>(ptr: *const u8) -> (*const u8, usize, *const V, *const u8) {
    let key_len = ptr::read(ptr as *const usize);
    let key_ptr = ptr.offset(mem::size_of::<usize>() as isize);
    let value_ptr = key_ptr.offset(key_len as isize);
    let next_ptr = value_ptr.offset(mem::size_of::<V>() as isize);

    (key_ptr, key_len, value_ptr as *const V, next_ptr)
}


struct IterRaw<V> {
    ptr: *const u8,
    end: *const u8,
    _marker: PhantomData<V>,
}

impl<V> Iterator for IterRaw<V> {
    type Item = (*const u8, usize, *const V);

    #[inline(always)]
    fn next(&mut self) -> Option<(*const u8, usize, *const V)> {
        if self.ptr == self.end {
            None
        } else {
            unsafe {
                let (key_ptr, key_len, value_ptr, next_ptr) = raw_item(self.ptr);
                self.ptr = next_ptr;

                Some((key_ptr, key_len, value_ptr))
            }
        }
    }
}

macro_rules! iterator {
    (struct $name:ident -> $elem:ty, $read:expr) => {
        impl<'a, V> Iterator for $name<'a, V> {
            type Item = (&'a [u8], $elem);

            fn next(&mut self) -> Option<(&'a [u8], $elem)> {
                match self.iter.next() {
                    Some((key_ptr, len, value_ptr)) => {
                        self.len -= 1;
                        unsafe {
                            let key = slice::from_raw_parts(key_ptr, len);
                            let value = $read(value_ptr);
                            Some((key, value))
                        }
                    }
                    None => None,
                }
            }

            #[inline(always)]
            fn size_hint(&self) -> (usize, Option<usize>) {
                (self.len, Some(self.len))
            }
        }
    }
}

pub struct Iter<'a, V: 'a> {
    iter: IterRaw<V>,
    len: usize,
    _marker: PhantomData<&'a V>,
}

iterator! { struct Iter -> &'a V, mem::transmute }

pub struct IterMut<'a, V: 'a> {
    iter: IterRaw<V>,
    len: usize,
    _marker: PhantomData<&'a V>,
}

iterator! { struct IterMut -> &'a mut V, mem::transmute }

pub struct Drain<'a, V: 'a> {
    iter: IterRaw<V>,
    len: usize,
    _marker: PhantomData<&'a V>,
}

iterator! { struct Drain -> V, ptr::read }

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
    key_ptr: *const u8,
    key_len: usize,
    value_ptr: *const V,
    _marker: PhantomData<&'a V>,
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
            mem::transmute(self.value_ptr)
        }
    }

    /// Gets a mutable reference to the value in the entry.
    pub fn get_mut(&mut self) -> &mut V {
        unsafe {
            mem::transmute(self.value_ptr)
        }
    }

    /// Converts the OccupiedEntry into a mutable reference to the value in the entry
    /// with a lifetime bound to the map itself
    pub fn into_mut(self) -> &'a mut V {
        unsafe {
            mem::transmute(self.value_ptr)
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
            self.array.remove_at(self.key_ptr, self.key_len, self.value_ptr)
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


/*
/// Rounds up to a multiple of a power of two. Returns the closest multiple
/// of `target_alignment` that is higher or equal to `unrounded`.
///
/// # Panics
///
/// Panics if `target_alignment` is not a power of two.
#[inline]
fn round_up_to_next(unrounded: usize, target_alignment: usize) -> usize {
    assert!(target_alignment.is_power_of_two());
    (unrounded + target_alignment - 1) & !(target_alignment - 1)
}

#[test]
fn test_rounding() {
    assert_eq!(round_up_to_next(0, 4), 0);
    assert_eq!(round_up_to_next(1, 4), 4);
    assert_eq!(round_up_to_next(2, 4), 4);
    assert_eq!(round_up_to_next(3, 4), 4);
    assert_eq!(round_up_to_next(4, 4), 4);
    assert_eq!(round_up_to_next(5, 4), 8);
}

// Returns a tuple of (key_offset, val_offset),
// from the start of a mallocated array.
#[inline]
fn calculate_offsets(len_size: usize,
                     keys_size: usize, keys_align: usize,
                     vals_align: usize)
                     -> (usize, usize, bool) {
    let keys_offset = round_up_to_next(hashes_size, keys_align);
    let (end_of_keys, oflo) = keys_offset.overflowing_add(keys_size);

    let vals_offset = round_up_to_next(end_of_keys, vals_align);

    (keys_offset, vals_offset, oflo)
}
*/
