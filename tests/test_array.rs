#![feature(test)]

extern crate cchashmap;
extern crate quickcheck;
extern crate test;

use std::collections::BTreeMap;
use std::iter::FromIterator;

use cchashmap::array::ArrayMap;

#[test]
fn quickcheck_array_from_iter_and_iter() {
    fn prop(map: BTreeMap<Vec<u8>, u32>) -> bool {
        let array = ArrayMap::from_iter(map.iter().map(|(k, v)| (&**k, *v)));

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
        let mut array = ArrayMap::new();

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
        let mut array = ArrayMap::from_iter(map.iter().map(|(k, v)| (&**k, *v)));

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
        array.insert(b"a", DropCounter { count: &mut count_x });
        array.insert(b"b", DropCounter { count: &mut count_y });
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
    array.insert(b"a", Elem(1));
    array.insert(b"b", Elem(2));
    array.insert(b"c", Elem(3));

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
    array.insert(b"a", BadElem(1));
    array.insert(b"b", BadElem(2));
    array.insert(b"c", BadElem(0xbadbeef));
    array.insert(b"d", BadElem(3));

    array.drain();
}
