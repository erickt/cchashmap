#![feature(test)]

extern crate cchashmap;
extern crate quickcheck;
extern crate test;

use std::iter::FromIterator;

use cchashmap::Bucket;

#[test]
fn quickcheck_bucket_from_iter_and_iter() {
    fn prop(keys: Vec<Vec<u8>>) -> bool {
        let bucket = Bucket::from_iter(keys.iter().map(|v| &**v));

        let mut len = keys.len();
        let mut keys_iter = keys.iter();
        let mut bucket_iter = bucket.iter();

        while let Some(key) = keys_iter.next() {
            // Make sure the bucket length matches the key length.
            if (len, Some(len)) != bucket_iter.size_hint() {
                return false;
            }

            len -= 1;

            // Make sure every key is in the bucket.
            match bucket_iter.next() {
                Some(k) if &**key == k => { }
                _ => { return false; }
            }
        }

        true
    }

    quickcheck::quickcheck(prop as fn(Vec<Vec<u8>>) -> bool);
}
