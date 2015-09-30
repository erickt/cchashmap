use std::borrow::Borrow;
use std::fmt;
use std::iter::FromIterator;
use std::marker::PhantomData;
use std::mem;
use std::ptr;
use std::slice;
use std::u8;

use quickcheck::{self, Arbitrary};

use util;

pub struct ArrayMap<V> {
    buf: Vec<u8>,
    len: usize,
    pub queries: ::std::cell::Cell<usize>,
    pub hash_hits: ::std::cell::Cell<usize>,
    pub key_hits: ::std::cell::Cell<usize>,
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
            queries: ::std::cell::Cell::new(0),
            hash_hits: ::std::cell::Cell::new(0),
            key_hits: ::std::cell::Cell::new(0),
            _marker: PhantomData,
        }
    }

    /// Returns the number of elements in the set.
    //
    // # Examples
    //
    // ```
    // use cchashmap::array::ArrayMap;
    //
    // let mut v = ArrayMap::new();
    // assert_eq!(v.len(), 0);
    // v.insert(*b"1", 2);
    // assert_eq!(v.len(), 1);
    // ```
    pub fn len(&self) -> usize {
        self.len
    }

    /// Returns true if the set contains no elements.
    //
    // # Examples
    //
    // ```
    // use cchashmap::array::ArrayMap;
    //
    // let mut v = ArrayMap::new();
    // assert!(v.is_empty());
    // v.insert(*b"1", 2);
    // assert!(!v.is_empty());
    // ```
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Clears the set, removing all values.
    //
    // # Examples
    //
    // ```
    // use cchashmap::array::ArrayMap;
    //
    // let mut v = ArrayMap::new();
    // v.insert(*b"1", 2);
    // v.clear();
    // assert!(v.is_empty());
    // ```
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
    //
    // # Examples
    //
    // ```
    // use cchashmap::array::ArrayMap;
    //
    // let mut map = ArrayMap::new();
    // map.insert(*b"1", "a");
    // assert_eq!(map.get(*b"1"), Some(&"a"));
    // assert_eq!(map.get(*b"2"), None);
    // ```
    pub fn get<K>(&self, hash: u64, key: K) -> Option<&V>
        where K: Borrow<[u8]>
    {
        let hash = hash as u8;
        match self.raw_find(hash, key) {
            Some((_, _, value)) => Some(value),
            None => None,
        }
    }

    /// Returns true if the map contains a value for the specified key.
    ///
    /// The key may be any borrowed form of the map's key type, but
    /// `Hash` and `Eq` on the borrowed form *must* match those for
    /// the key type.
    //
    // # Examples
    //
    // ```
    // use cchashmap::array::ArrayMap;
    //
    // let mut map = ArrayMap::new();
    // map.insert(*b"1", "a");
    // assert_eq!(map.contains_key(*b"1"), true);
    // assert_eq!(map.contains_key(*b"2"), false);
    // ```
    pub fn contains_key<K>(&self, hash: u64, key: K) -> bool
        where K: Borrow<[u8]>
    {
        self.get(hash, key).is_some()
    }

    /// Returns a mutable reference to the value corresponding to the key.
    ///
    /// The key may be any borrowed form of the map's key type, but
    /// `Hash` and `Eq` on the borrowed form *must* match those for
    /// the key type.
    //
    // # Examples
    //
    // ```
    // use cchashmap::array::ArrayMap;
    //
    // let mut map = ArrayMap::new();
    // map.insert(*b"1", "a");
    // if let Some(x) = map.get_mut(*b"1") {
    //     *x = "b";
    // }
    // assert_eq!(map.get(*b"1"), Some(&"b"));
    // ```
    pub fn get_mut<K>(&mut self, hash: u64, key: K) -> Option<&mut V>
        where K: Borrow<[u8]>
    {
        let hash = hash as u8;
        match self.raw_find_mut(hash, key) {
            Some((_, _, value)) => Some(value),
            None => None,
        }
    }

    /// Inserts a key-value pair into the map. If the key already had a value
    /// present in the map, that value is returned. Otherwise, `None` is returned.
    //
    // # Examples
    //
    // ```
    // use cchashmap::array::ArrayMap;
    //
    // let mut map = ArrayMap::new();
    // assert_eq!(map.insert(*b"37", "a"), None);
    // assert_eq!(map.is_empty(), false);
    //
    // map.insert(*b"37", "b");
    // assert_eq!(map.insert(*b"37", "c"), Some("b"));
    // assert_eq!(map.get(*b"37"), Some(&"c"));
    // ```
    pub fn insert<K>(&mut self, hash: u64, key: K, mut value: V) -> Option<V>
        where K: Borrow<[u8]>
    {
        let hash = hash as u8;
        match self.raw_find_mut(hash, key.borrow()) {
            Some((_, _, v)) => {
                mem::swap(v, &mut value);
                return Some(value);
            }
            None => { }
        }

        self.push(hash, key, value);

        None
    }

    /// Removes a key from the map, returning the value at the key if the key
    /// was previously in the map.
    ///
    /// The key may be any borrowed form of the map's key type, but
    /// `Hash` and `Eq` on the borrowed form *must* match those for
    /// the key type.
    //
    // # Examples
    //
    // ```
    // use cchashmap::array::ArrayMap;
    //
    // let mut map = ArrayMap::new();
    // map.insert(*b"1", "a");
    // assert_eq!(map.remove(*b"1"), Some("a"));
    // assert_eq!(map.remove(*b"1"), None);
    // ```
    pub fn remove<K>(&mut self, hash: u64, key: K) -> Option<V>
        where K: Borrow<[u8]>
    {
        let hash = hash as u8;
        let key = key.borrow();

        let (hash_ptr, value_ptr) = match self.raw_find(hash, key) {
            Some((h, _, v)) => (h as *const u8, (v as *const V) as *const u8),
            None => { return None; }
        };

        unsafe {
            Some(self.remove_at(hash_ptr, value_ptr))
        }
    }

    unsafe fn remove_at(&mut self, hash_ptr: *const u8, value_ptr: *const u8) -> V {
        let buf_ptr = self.buf.as_ptr();
        let end_ptr = buf_ptr.offset(self.buf.len() as isize);
        debug_assert!(end_ptr <= buf_ptr.offset(self.buf.capacity() as isize));

        debug_assert!(buf_ptr <= hash_ptr  && hash_ptr  <  end_ptr);
        debug_assert!(buf_ptr <  value_ptr && value_ptr <= end_ptr);

        let next_ptr = value_ptr.offset(mem::size_of::<V>() as isize);
        debug_assert!(next_ptr <= end_ptr);

        // Truncate the buffer so we don't drop the value twice if there's a panic.
        let item_index = (hash_ptr as usize) - (buf_ptr as usize);
        self.buf.set_len(item_index);

        // Read out the value. We now own it since the buffer was truncated.
        let value: V = ptr::read(value_ptr as *const V);

        // Move the remaining items into this item's spot.
        let remaining_bytes = (end_ptr as usize) - (next_ptr as usize);
        debug_assert!(next_ptr.offset(remaining_bytes as isize) <= end_ptr);

        ptr::copy(next_ptr, hash_ptr as *mut u8, remaining_bytes);

        // Finally, restore the length, minus the item we removed.
        self.buf.set_len(item_index + remaining_bytes);
        debug_assert!(self.buf.len() < self.buf.capacity());

        value

        /*
        let hash_ptr = key_ptr.offset(-(mem::size_of::<u64>() as isize));
        debug_assert!(buf_ptr <= hash_ptr && hash_ptr < end_ptr);

        let len_ptr = hash_ptr.offset(-(mem::size_of::<usize>() as isize));
        debug_assert!(buf_ptr <= len_ptr && len_ptr < end_ptr);

        let hash_index = (hash_ptr as usize) - (buf_ptr as usize);
        let len_index  = (len_ptr  as usize) - (buf_ptr as usize);
        let key_index  = (key_ptr  as usize) - (buf_ptr as usize);
        let val_index  = (val_ptr  as usize) - (buf_ptr as usize);

        debug_assert!(end_ptr <= buf_ptr.offset(self.buf.capacity() as isize));

        debug_assert!(len_ptr <  key_ptr && key_ptr < end_ptr);
        debug_assert!(key_ptr <= val_ptr);
        debug_assert!(val_ptr <  end_ptr);
        debug_assert!(val_ptr.offset(mem::size_of::<usize>() as isize) <= end_ptr);

        let next_ptr = val_ptr.offset(mem::size_of::<V>() as isize);
        let remaining_bytes = (end_ptr as usize) - (next_ptr as usize);

        // Truncate the buffer so we don't drop the value twice if there's a panic.
        let item_ptr = key_ptr.offset(-(mem::size_of::<usize>() as isize));
        let item_index = (item_ptr as usize) - (buf_ptr as usize);

        self.buf.set_len(item_index);
        debug_assert!(end_ptr <= buf_ptr.offset(self.buf.capacity() as isize));

        // Read out the value. We now own it since the buffer was truncated.
        let value: V = ptr::read(val_ptr as *const V);

        // Move the remaining items into this item's spot.
        debug_assert!(next_ptr.offset(remaining_bytes as isize) <= end_ptr);

        ptr::copy(next_ptr, item_ptr as *mut u8, remaining_bytes);

        // Finally, restore the length, minus the item we removed.
        self.buf.set_len(item_index + remaining_bytes);
        debug_assert!(self.buf.len() < self.buf.capacity());

        for _ in self.iter_raw() {}

        value
        */
    }

    /*
    /// Gets the given key's corresponding entry in the map for in-place manipulation.
    //
    // # Examples
    //
    // ```
    // use cchashmap::array::ArrayMap;
    //
    // let mut letters = ArrayMap::new();
    //
    // for ch in "a short treatise on fungi".chars() {
    //     let ch = ch.to_string();
    //     let counter = letters.entry(ch.as_bytes()).or_insert(0);
    //     *counter += 1;
    // }
    //
    // assert_eq!(letters[*b"s"], 2);
    // assert_eq!(letters[*b"t"], 3);
    // assert_eq!(letters[*b"u"], 1);
    // assert_eq!(letters.get(*b"y"), None);
    // ```
    pub fn entry<'a, K: 'a>(&'a mut self, hash: u64, key: K) -> Entry<'a, K, V>
        where K: Borrow<[u8]>
    {
        match self.raw_find_mut(hash, key.borrow()) {
            Some((hash, key, value)) => {
                Entry::Occupied(OccupiedEntry {
                    array: self,
                    hash: hash,
                    key: key,
                    value: value,
                    _marker: PhantomData,
                })
            }
            None => {
                Entry::Vacant(VacantEntry {
                    array: self,
                    hash: hash,
                    key: key,
                })
            }
        }
    }
    */

    pub fn iter<'a>(&'a self) -> Iter<'a, V> {
        Iter {
            items: RawItem::new(&self.buf),
            len: self.len,
        }
    }

    pub fn iter_mut<'a>(&'a mut self) -> IterMut<'a, V> {
        IterMut {
            items: RawItemMut::new(&mut self.buf),
            len: self.len,
        }
    }

    pub fn drain<'a>(&'a mut self) -> Drain<'a, V> {
        let len = self.len;

        // We no longer have any items.
        self.len = 0;

        Drain {
            items: RawItemDrain::new(&mut self.buf),
            len: len,
        }
    }

    /*
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
    */

    #[inline(always)]
    fn raw_find<K>(&self, hash: u8, key: K) -> Option<(&u8, &[u8], &V)>
        where K: Borrow<[u8]>
    {
        let key = key.borrow();

        for (h, k, v) in RawItem::<V>::new(&self.buf) {
            /*
            if hash == *h && key == k {
                return Some((h, k, v));
            }
            */

            let queries = self.queries.get();
            self.queries.set(queries + 1);

            if hash == *h {
                let hash_hits = self.hash_hits.get();
                self.hash_hits.set(hash_hits + 1);

                if key == k {
                    let key_hits = self.key_hits.get();
                    self.key_hits.set(key_hits + 1);

                    return Some((h, k, v));
                }
            }
        }

        None
    }

    #[inline(always)]
    fn raw_find_mut<K>(&mut self, hash: u8, key: K) -> Option<(&u8, &[u8], &mut V)>
        where K: Borrow<[u8]>
    {
        let key = key.borrow();

        for (h, k, v) in RawItemMut::new(&mut self.buf) {
            /*
            if hash == *h && key == k {
                return Some((h, k, v));
            }
            */

            let queries = self.queries.get();
            self.queries.set(queries + 1);

            if hash == *h {
                let hash_hits = self.hash_hits.get();
                self.hash_hits.set(hash_hits + 1);

                if key == k {
                    let key_hits = self.key_hits.get();
                    self.key_hits.set(key_hits + 1);

                    return Some((h, k, v));
                }
            }
        }

        None
    }

    fn push<K>(&mut self, hash: u8, key: K, value: V) -> &mut V
        where K: Borrow<[u8]>
    {
        let key = key.borrow();

        assert!(key.len() < u8::MAX as usize);
        let key_len = key.len() as u8;

        // First, make sure we reserve enough space to write everything.
        // FIXME: Account for alignment.
        let buf_size     = self.buf.len();
        let hash_size    = mem::size_of::<u8>();
        let key_len_size = mem::size_of::<u8>();
        let value_size   = mem::size_of::<V>();

        let len = buf_size + hash_size + key_len_size + key_len as usize + value_size;
        self.buf.reserve(len);

        unsafe {
            // Grab a pointer that's pointing to the end of the space.
            let mut ptr = self.buf.as_mut_ptr().offset(buf_size as isize);

            // Write the hash.
            ptr::write(ptr, hash);
            ptr = ptr.offset(hash_size as isize);

            // Write the length at the end and adjust the pointer.
            ptr::write(ptr, key_len);
            ptr = ptr.offset(key_len_size as isize);

            // Write the key.
            ptr::copy_nonoverlapping(key.as_ptr(), ptr, key_len as usize);
            ptr = ptr.offset(key_len as isize);

            // Write the value.
            ptr::write(ptr as *mut V, value);

            // Finally, adjust the buffer length.
            self.buf.set_len(len);

            self.len += 1;

            debug_assert!(self.buf.len() <= self.buf.capacity());

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

        for (hash, key, value) in self.iter() {
            dst.push(hash, key, value.clone());
        }

        dst
    }
}

impl<K, V> FromIterator<(u64, K, V)> for ArrayMap<V>
    where K: Borrow<[u8]>,
{
    fn from_iter<I: IntoIterator<Item=(u64, K, V)>>(iterator: I) -> Self {
        let iterator = iterator.into_iter();

        let mut bucket = ArrayMap::with_capacity(iterator.size_hint().0);

        for (hash, key, value) in iterator.into_iter() {
            bucket.insert(hash, key, value);
        }

        bucket
    }
}

impl<V> fmt::Debug for ArrayMap<V> where V: fmt::Debug {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_set().entries(self.iter()).finish()
    }
}

macro_rules! impl_raw_iter {
    ($name:ident, $bytes_ty:ty, $value_ty:ty, $read_value:expr) => {
        impl<'a, V> $name<'a, V> {
            unsafe fn read_ptr(&mut self, len: usize) -> *const u8 {
                let ptr = self.ptr;
                self.ptr = self.ptr.offset(len as isize);

                debug_assert!(self.ptr <= self.end);

                ptr
            }

            unsafe fn read_hash(&mut self) -> &'a u8 {
                let ptr = self.read_ptr(mem::size_of::<u8>());
                mem::transmute(ptr)
            }

            unsafe fn read_key_len(&mut self) -> &'a u8 {
                let ptr = self.read_ptr(mem::size_of::<u8>());
                mem::transmute(ptr)
            }

            unsafe fn read_key(&mut self) -> &'a [u8] {
                let len = (*self.read_key_len()) as usize;
                let ptr = self.read_ptr(len);
                slice::from_raw_parts(ptr, len)
            }

            unsafe fn read_value(&mut self) -> $value_ty {
                let ptr = self.read_ptr(mem::size_of::<V>()) as *const V;
                $read_value(ptr)
            }
        }

        impl<'a, V> Iterator for $name<'a, V> {
            type Item = (&'a u8, &'a [u8], $value_ty);

            fn next(&mut self) -> Option<Self::Item> {
                if self.ptr == self.end {
                    None
                } else {
                    unsafe {
                        let hash = self.read_hash();
                        let key = self.read_key();
                        let value = self.read_value();
                        Some((hash, key, value))
                    }
                }
            }
        }
    }
}

struct RawItem<'a, V: 'a> {
    ptr: *const u8,
    end: *const u8,
    _marker: PhantomData<&'a V>,
}

impl<'a, V> RawItem<'a, V> {
    fn new(bytes: &'a [u8]) -> Self {
        unsafe {
            let ptr = bytes.as_ptr();
            let end = ptr.offset(bytes.len() as isize);

            RawItem {
                ptr: ptr,
                end: end,
                _marker: PhantomData,
            }
        }
    }
}

impl_raw_iter!(RawItem, &'a [u8], &'a V, mem::transmute);

struct RawItemMut<'a, V: 'a> {
    ptr: *mut u8,
    end: *mut u8,
    _marker: PhantomData<&'a mut V>,
}

impl<'a, V> RawItemMut<'a, V> {
    fn new(bytes: &'a mut [u8]) -> Self {
        unsafe {
            let ptr = bytes.as_mut_ptr();
            let end = ptr.offset(bytes.len() as isize);

            RawItemMut {
                ptr: ptr,
                end: end,
                _marker: PhantomData,
            }
        }
    }
}

impl_raw_iter!(RawItemMut, &'a mut [u8], &'a mut V, mem::transmute);

struct RawItemDrain<'a, V: 'a> {
    ptr: *const u8,
    end: *const u8,
    _marker: PhantomData<&'a mut V>,
}

impl<'a, V> RawItemDrain<'a, V> {
    fn new(bytes: &'a mut Vec<u8>) -> Self {
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
        unsafe {
            let ptr = bytes.as_ptr();
            let end = ptr.offset(bytes.len() as isize);

            bytes.set_len(0);

            RawItemDrain {
                ptr: ptr,
                end: end,
                _marker: PhantomData,
            }
        }
    }
}

impl_raw_iter!(RawItemDrain, &'a mut [u8], V, ptr::read);


/*
struct IterRaw<V> {
    ptr: *const u8,
    end: *const u8,
    _marker: PhantomData<V>,
}

impl<V> Iterator for IterRaw<V> {
    type Item = (*const u8, usize, *const u8);

    #[inline(always)]
    fn next(&mut self) -> Option<(*const u8, usize, *const u8)> {
        if self.ptr == self.end {
            None
        } else {
            unsafe {
                let (key_ptr, key_len, val_ptr, next_ptr) = raw_item::<V>(self.ptr);
                assert!(key_ptr <= val_ptr);
                assert!(val_ptr <= next_ptr);

                assert!(key_ptr <= self.end);
                assert!(val_ptr <= self.end);
                assert!(next_ptr <= self.end);

                assert!(key_ptr.offset(key_len as isize) == val_ptr);
                assert!(key_ptr.offset(key_len as isize) <= self.end);

                self.ptr = next_ptr;

                Some((key_ptr, key_len, val_ptr))
            }
        }
    }
}
*/

macro_rules! iterator {
    ($name:ident, $value:ty) => {
        impl<'a, V> Iterator for $name<'a, V> {
            type Item = (u8, &'a [u8], $value);

            fn next(&mut self) -> Option<Self::Item> {
                match self.items.next() {
                    Some((hash, key, value)) => {
                        self.len -= 1;
                        Some((*hash, key, value))
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
    items: RawItem<'a, V>,
    len: usize,
}

iterator!(Iter, &'a V);

pub struct IterMut<'a, V: 'a> {
    items: RawItemMut<'a, V>,
    len: usize,
}

iterator!(IterMut, &'a mut V);

pub struct Drain<'a, V: 'a> {
    items: RawItemDrain<'a, V>,
    len: usize,
}

iterator!(Drain, V);

unsafe impl<'a, T: Sync> Sync for Drain<'a, T> {}
unsafe impl<'a, T: Send> Send for Drain<'a, T> {}

impl<'a, T> Drop for Drain<'a, T> {
    fn drop(&mut self) {
        // exhaust self first
        while let Some(_) = self.next() { }
    }
}

/// A view into a single entry in a map, which may either be vacant or occupied.
pub enum Entry<'a, K, V: 'a> {
    /// A vacant Entry
    Vacant(VacantEntry<'a, K, V>),

    /// An occupied Entry
    Occupied(OccupiedEntry<'a, V>),
}

/// A vacant Entry.
pub struct VacantEntry<'a, K, V: 'a> {
    array: &'a mut ArrayMap<V>,
    hash: u8,
    key: K,
}

/// An occupied Entry.
pub struct OccupiedEntry<'a, V: 'a> {
    array: &'a mut ArrayMap<V>,
    hash: &'a u8,
    key: &'a [u8],
    value: &'a mut V,
    _marker: PhantomData<&'a V>,
}

impl<'a, K, V> Entry<'a, K, V>
    where K: Borrow<[u8]>
{
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
        self.value
    }

    /// Gets a mutable reference to the value in the entry.
    pub fn get_mut(&mut self) -> &mut V {
        self.value
    }

    /// Converts the OccupiedEntry into a mutable reference to the value in the entry
    /// with a lifetime bound to the map itself
    pub fn into_mut(self) -> &'a mut V {
        self.value
    }

    /// Sets the value of the entry, and returns the entry's old value
    pub fn insert(&mut self, mut value: V) -> V {
        mem::swap(&mut value, self.value);
        value
    }

    /// Takes the value out of the entry, and returns it
    pub fn remove(self) -> V {
        unsafe {
            self.array.remove_at(
                (self.hash as *const u8) as *const u8,
                (self.value as *const V) as *const u8)
        }
    }
}

impl<'a, K, V: 'a> VacantEntry<'a, K, V>
    where K: Borrow<[u8]>
{
    /// Sets the value of the entry with the VacantEntry's key,
    /// and returns a mutable reference to it
    pub fn insert(self, value: V) -> &'a mut V {
        self.array.push(self.hash, self.key, value)
    }
}

impl<V> Arbitrary for ArrayMap<V> where V: Arbitrary {
    fn arbitrary<G: quickcheck::Gen>(g: &mut G) -> ArrayMap<V> {
        use std::collections::HashMap;
        let keys: HashMap<Vec<u8>, V> = Arbitrary::arbitrary(g);
        keys.into_iter()
            .map(|(k, v)| (util::hash(&k), k, v))
            .collect()
    }

    fn shrink(&self) -> Box<Iterator<Item=ArrayMap<V>>> {
        use std::collections::HashMap;
        let keys: HashMap<Vec<u8>, V> = self.iter()
            .map(|(_, k, v)| (k.to_owned(), v.clone()))
            .collect();

        Box::new(keys.shrink().map(|keys| {
            keys.into_iter()
                .map(|(k, v)| (util::hash(&k), k, v))
                .collect()
        }))
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
