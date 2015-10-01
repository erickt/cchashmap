#![feature(test)]

extern crate cchashmap;
extern crate quickcheck;
extern crate test;

use std::collections::BTreeMap;
use std::iter::FromIterator;

use cchashmap::CCHashMap;

#[test]
fn quickcheck_from_iter_and_iter() {
    fn prop(btree: BTreeMap<Vec<u8>, u32>) -> bool {
        let map = CCHashMap::from_iter(btree.iter().map(|(k, v)| (&**k, *v)));

        // Make sure the lengths are the same.
        if btree.len() != map.len() { return false; }
        if btree.is_empty() != map.is_empty() { return false; }

        // Make sure the map length matches the key length.
        let mut map_iter = map.iter();
        for i in 0 .. btree.len() {
            let len = btree.len() - i;
            if (len, Some(len)) != map_iter.size_hint() { return false; }
            if map_iter.next().is_none() { return false; }
        }
        if map_iter.next().is_some() { return false; }

        // Make sure we've got the same items in both maps.
        let mut btree_items = btree.iter().map(|(k, v)| (&**k, v)).collect::<Vec<_>>();
        btree_items.sort();

        let mut map_items = map.iter().collect::<Vec<_>>();
        map_items.sort();

        btree_items == map_items
    }

    quickcheck::quickcheck(prop as fn(BTreeMap<Vec<u8>, u32>) -> bool);
}

#[test]
fn quickcheck_insert_and_get() {
    fn prop(btree: BTreeMap<Vec<u8>, u32>) -> bool {
        let mut map = CCHashMap::new();

        for (key, value) in btree.iter() {
            map.insert(&**key, *value);
        }

        for (key, value) in btree.iter() {
            if map.get(&**key) != Some(value) { return false; }
        }

        // Find a key that's not in the map.
        let mut missing_key = Vec::new();
        while btree.contains_key(&missing_key) {
            missing_key.push(0);
        }

        map.get(missing_key).is_none()
    }

    quickcheck::quickcheck(prop as fn(BTreeMap<Vec<u8>, u32>) -> bool);
}

/*
#[test]
fn test_drain_empty() {
    let mut map = CCHashMap::<u32>::new();

    assert_eq!(map.len(), 0);
    assert!(map.is_empty());

    {
        let mut iter = map.drain();
        assert_eq!(iter.next(), None);
    }

    assert_eq!(map.len(), 0);
    assert!(map.is_empty());
}

#[test]
fn test_drain_one() {
    let mut map = CCHashMap::<u32>::new();
    map.insert([], 0);

    assert_eq!(map.len(), 1);
    assert!(!map.is_empty());

    {
        let mut iter = map.drain();
        assert_eq!(iter.next(), Some((&[][..], 0)));
        assert_eq!(iter.next(), None);
    }

    assert_eq!(map.len(), 0);
    assert!(map.is_empty());
}

#[test]
fn test_drain_two() {
    let mut map = CCHashMap::<u32>::new();
    map.insert([], 0);
    map.insert([21], 0);

    assert_eq!(map.len(), 2);
    assert!(!map.is_empty());

    {
        let mut vec = map.drain().collect::<Vec<_>>();
        vec.sort();

        assert_eq!(vec, vec![(&[][..], 0), (&[21][..], 0)]);
    }


    assert_eq!(map.len(), 0);
    assert!(map.is_empty());
}

#[test]
fn quickcheck_drain() {
    fn prop(btree: BTreeMap<Vec<u8>, u32>) -> bool {
        let mut map = CCHashMap::from_iter(btree.iter().map(|(k, v)| (&**k, *v)));
        let mut items = map.drain().collect::<Vec<_>>();
        items.sort();

        for ((k1, v1), (k2, v2)) in btree.iter().zip(items.into_iter()) {
            if &**k1 != k2 || v1 != &v2 {
                return false;
            }
        }

        true
    }

    quickcheck::quickcheck(prop as fn(BTreeMap<Vec<u8>, u32>) -> bool);
}

#[test]
fn test_drop_works() {
    struct DropCounter<'a> {
        count: &'a mut u32
    }

    impl<'a> Drop for DropCounter<'a> {
        fn drop(&mut self) {
            *self.count += 1;
        }
    }

    let (mut count_x, mut count_y) = (0, 0);
    {
        let mut map = CCHashMap::new();
        map.insert(*b"a", DropCounter { count: &mut count_x });
        map.insert(*b"b", DropCounter { count: &mut count_y });
        drop(map);
    };
    assert_eq!(count_x, 1);
    assert_eq!(count_y, 1);
}

#[test]
fn test_drain_drops() {
    static mut drops: u32 = 0;
    struct Elem(i32);
    impl Drop for Elem {
        fn drop(&mut self) {
            unsafe { drops += 1; }
        }
    }

    let mut map = CCHashMap::new();
    map.insert(*b"a", Elem(1));
    map.insert(*b"b", Elem(2));
    map.insert(*b"c", Elem(3));

    assert_eq!(unsafe { drops }, 0);

    map.drain();

    assert_eq!(unsafe { drops }, 3);

    map.drain();

    assert_eq!(unsafe { drops }, 3);
}

#[test]
#[should_panic]
fn test_drain_fail() {
    struct BadElem(i32);
    impl Drop for BadElem {
        fn drop(&mut self) {
            let BadElem(ref mut x) = *self;
            if *x == 0xbadbeef {
                panic!("BadElem panic: 0xbadbeef")
            }
        }
    }

    let mut map = CCHashMap::new();
    map.insert(*b"a", BadElem(1));
    map.insert(*b"b", BadElem(2));
    map.insert(*b"c", BadElem(0xbadbeef));
    map.insert(*b"d", BadElem(3));

    map.drain();
}
*/
