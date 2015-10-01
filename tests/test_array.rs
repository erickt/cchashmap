#![cfg(fee)]
#![feature(test)]

extern crate cchashmap;
extern crate quickcheck;
extern crate test;

use std::collections::BTreeMap;

use cchashmap::array::ArrayMap;
use cchashmap::util;

fn insert<V>(array: &mut ArrayMap<V>, key: &[u8], value: V) -> Option<V> {
    let hash = util::hash(key);
    array.insert(hash, key, value)
}

fn get<'a, V>(array: &'a ArrayMap<V>, key: &[u8]) -> Option<&'a V> {
    let hash = util::hash(key);
    array.get(hash, key)
}

#[test]
fn quickcheck_from_iter_and_iter() {
    fn prop(map: BTreeMap<Vec<u8>, u32>) -> bool {
        let array = map.iter()
            .map(|(k, v)| (util::hash(&k), &**k, *v))
            .collect::<ArrayMap<_>>();

        if map.len() != array.len() {
            return false;
        }

        let mut len = map.len();
        let mut array_iter = array.iter();

        for (key, value) in map.iter() {
            // Make sure the array length matches the key length.
            if (len, Some(len)) != array_iter.size_hint() {
                return false;
            }

            len -= 1;

            // Make sure every key is in the array.
            match array_iter.next() {
                Some((h, k, v)) if util::hash(&key) == h && &**key == k && value == v => { }
                _ => { return false; }
            }
        }

        true
    }

    quickcheck::quickcheck(prop as fn(BTreeMap<Vec<u8>, u32>) -> bool);
}

#[test]
fn quickcheck_insert_and_get() {
    fn prop(map: BTreeMap<Vec<u8>, u32>) -> bool {
        let mut array = ArrayMap::new();

        for (key, value) in map.iter() {
            insert(&mut array, &**key, *value);
        }

        for (key, value) in map.iter() {
            if get(&array, &**key) != Some(value) {
                return false;
            }
        }

        // Find a key that's not in the map.
        let mut missing_key = Vec::new();
        while map.contains_key(&missing_key) {
            missing_key.push(0);
        }

        get(&array, &missing_key).is_none()
    }

    quickcheck::quickcheck(prop as fn(BTreeMap<Vec<u8>, u32>) -> bool);
}

#[test]
fn test_drain_empty() {
    let mut array = ArrayMap::<u32>::new();

    assert_eq!(array.len(), 0);
    assert!(array.is_empty());

    {
        let mut iter = array.drain();
        assert_eq!(iter.next(), None);
    }

    assert_eq!(array.len(), 0);
    assert!(array.is_empty());
}

#[test]
fn test_drain_one() {
    let mut array = ArrayMap::<u32>::new();
    insert(&mut array, &[], 0);

    assert_eq!(array.len(), 1);
    assert!(!array.is_empty());

    {
        let mut iter = array.drain();
        assert_eq!(iter.next(), Some((util::hash(&[]), &[][..], 0)));
        assert_eq!(iter.next(), None);
    }

    assert_eq!(array.len(), 0);
    assert!(array.is_empty());
}

#[test]
fn quickcheck_drain() {
    fn prop(map: BTreeMap<Vec<u8>, u32>) -> bool {
        let mut array = map.iter()
            .map(|(k, v)| (util::hash(&k), &**k, *v))
            .collect::<ArrayMap<_>>();

        if map.len() != array.len() || map.is_empty() != array.is_empty() {
            return false;
        }

        for ((k1, v1), (h2, k2, v2)) in map.iter().zip(array.drain()) {
            if util::hash(&k1) != h2 || &**k1 != k2 || v1 != &v2 {
                return false;
            }
        }

        array.len() == 0 && array.is_empty()
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
        let mut array = ArrayMap::new();
        insert(&mut array, b"a", DropCounter { count: &mut count_x });
        insert(&mut array, b"b", DropCounter { count: &mut count_y });
        drop(array);
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

    let mut array = ArrayMap::new();
    insert(&mut array, b"a", Elem(1));
    insert(&mut array, b"b", Elem(2));
    insert(&mut array, b"c", Elem(3));

    assert_eq!(unsafe { drops }, 0);

    array.drain();

    assert_eq!(unsafe { drops }, 3);

    array.drain();

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

    let mut array = ArrayMap::new();
    insert(&mut array, b"a", BadElem(1));
    insert(&mut array, b"b", BadElem(2));
    insert(&mut array, b"c", BadElem(0xbadbeef));
    insert(&mut array, b"d", BadElem(3));

    array.drain();
}
