#![feature(test)]

extern crate cchashmap;
extern crate quickcheck;
extern crate test;

use std::collections::BTreeSet;
use std::iter::FromIterator;

use cchashmap::CCHashSet;

#[test]
fn test_insert() {
    let mut set = CCHashSet::new();
    assert!(set.is_empty());
    assert_eq!(set.len(), 0);

    set.insert(*b"1234");
    assert!(!set.is_empty());
    assert_eq!(set.len(), 1);

    assert!(set.contains(*b"1234"));
    assert!(!set.contains(*b"1235"));
}

#[test]
fn test_empty_insert() {
    let mut set = CCHashSet::new();
    set.insert(*b"");
    set.insert(*b"");
    assert_eq!(set.len(), 1);

    let mut iter = set.iter();
    assert_eq!(iter.next().unwrap(), b"");
    assert_eq!(iter.next(), None);
}

#[test]
fn test_empty_single_insert() {
    let mut set = CCHashSet::new();
    set.insert(*b"");
    set.insert(*b"\x21");
    assert_eq!(set.len(), 2);

    let set = set.iter().collect::<BTreeSet<&[u8]>>();

    let mut iter = set.into_iter();
    assert_eq!(iter.next().unwrap(), b"");
    assert_eq!(iter.next().unwrap(), b"\x21");
    assert_eq!(iter.next(), None);
}

#[test]
fn quickcheck_bucket_from_iter_and_iter() {
    fn prop(keys: Vec<Vec<u8>>) -> bool {
        let keys = BTreeSet::<Vec<u8>>::from_iter(keys.into_iter());
        let set = CCHashSet::from_iter(keys.iter().map(|v| &**v));

        let mut len = keys.len();
        let mut keys_iter = keys.iter();

        // Convert the set into a BTreeSet so it's sorted.
        let mut set_iter = set.iter().collect::<BTreeSet<&[u8]>>().into_iter();

        while let Some(key) = keys_iter.next() {
            // Make sure the set length matches the key length.
            if (len, Some(len)) != set_iter.size_hint() {
                return false;
            }

            len -= 1;

            // Make sure every key is in the set.
            match set_iter.next() {
                Some(k) if &**key == k => { }
                _ => { return false; }
            }
        }

        true
    }

    quickcheck::quickcheck(prop as fn(Vec<Vec<u8>>) -> bool);
}
