#![feature(test)]

extern crate cchashmap;
extern crate quickcheck;
extern crate test;

use std::collections::BTreeMap;
use std::iter::FromIterator;

use cchashmap::Array;

#[test]
fn quickcheck_array_from_iter_and_iter() {
    fn prop(map: BTreeMap<Vec<u8>, u32>) -> bool {
        let array = Array::from_iter(map.iter().map(|(k, v)| (&**k, *v)));

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
                Some((k, v)) if &**key == k && value == v => { }
                _ => { return false; }
            }
        }

        true
    }

    quickcheck::quickcheck(prop as fn(BTreeMap<Vec<u8>, u32>) -> bool);
}

#[test]
fn quickcheck_array_insert_and_get() {
    fn prop(map: BTreeMap<Vec<u8>, u32>) -> bool {
        let mut array = Array::new();

        for (key, value) in map.iter() {
            array.insert(key, *value);
        }

        for (key, value) in map.iter() {
            if array.get(key) != Some(value) {
                return false;
            }
        }

        // Find a key that's not in the map.
        let mut missing_key = Vec::new();
        while map.contains_key(&missing_key) {
            missing_key.push(0);
        }

        array.get(&missing_key).is_none()
    }

    quickcheck::quickcheck(prop as fn(BTreeMap<Vec<u8>, u32>) -> bool);
}

#[test]
fn test_drain_empty() {
    let mut array = Array::<u32>::new();

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
    let mut array = Array::<u32>::new();
    array.insert(&[], 0);

    assert_eq!(array.len(), 1);
    assert!(!array.is_empty());

    {
        let mut iter = array.drain();
        assert_eq!(iter.next(), Some((&[][..], 0)));
        assert_eq!(iter.next(), None);
    }

    assert_eq!(array.len(), 0);
    assert!(array.is_empty());
}

#[test]
fn quickcheck_array_drain() {
    fn prop(map: BTreeMap<Vec<u8>, u32>) -> bool {
        let mut array = Array::from_iter(map.iter().map(|(k, v)| (&**k, *v)));

        if map.len() != array.len() || map.is_empty() != array.is_empty() {
            return false;
        }

        for ((k1, v1), (k2, v2)) in map.iter().zip(array.drain()) {
            if &**k1 != k2 || v1 != &v2 {
                return false;
            }
        }

        array.len() == 0 && array.is_empty()
    }

    quickcheck::quickcheck(prop as fn(BTreeMap<Vec<u8>, u32>) -> bool);
}
