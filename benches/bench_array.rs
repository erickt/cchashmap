#![feature(test)]

extern crate test;
extern crate cchashmap;
extern crate byteorder;

use std::collections::{BTreeMap, HashMap};
use std::iter::FromIterator;

use byteorder::{ByteOrder, NativeEndian};
use cchashmap::Array;

static OUTER_LEN: usize = 128;
static INNER_LEN: usize = 8;


fn make_fixture() -> Vec<(Vec<u8>, usize)> {
    let mut haystack = Vec::with_capacity(OUTER_LEN);
    let mut bytes = [0; 8];

    for index in 0 .. OUTER_LEN {
        let mut hay = Vec::with_capacity(8);
        for _ in 0 .. INNER_LEN {
            NativeEndian::write_u64(&mut bytes, index as u64);
            hay.extend(&bytes);
        }
        haystack.push((hay, index));
    }

    haystack
}

macro_rules! bench_insert {
    ($name:ident, $fixture:ident, $ctor:expr) => {
        #[bench]
        fn $name(b: &mut test::Bencher) {
            b.bytes = (OUTER_LEN * INNER_LEN) as u64;
            let $fixture = make_fixture();

            b.iter(|| {
                let haystack = $ctor;
                test::black_box(haystack)
            })
        }

    }
}

bench_insert!(bench_insert_btreemap, fixture, {
    let mut map = BTreeMap::<Vec<u8>, usize>::new();
    for &(ref key, value) in fixture.iter() {
        map.insert(key.clone(), value.clone());
    }
    map
});

bench_insert!(bench_insert_hashmap, fixture, {
    let mut map = HashMap::<Vec<u8>, usize>::new();
    for &(ref key, value) in fixture.iter() {
        map.insert(key.clone(), value.clone());
    }
    map
});

bench_insert!(bench_insert_array, fixture, {
    let mut map = Array::<usize>::new();
    for &(ref key, value) in fixture.iter() {
        map.insert(key, value.clone());
    }
    map
});

macro_rules! bench_iter {
    ($name:ident, $fixture:ident, $ctor:expr) => {
        #[bench]
        fn $name(b: &mut test::Bencher) {
            b.bytes = (OUTER_LEN * INNER_LEN) as u64;
            let $fixture = make_fixture();
            let haystack = $ctor;

            b.iter(|| {
                for key in haystack.iter() {
                    test::black_box(key);
                }
            })
        }

    }
}

bench_iter!(bench_iter_btreemap, fixture, {
    BTreeMap::<Vec<u8>, usize>::from_iter(fixture.into_iter())
});

bench_iter!(bench_iter_hashmap, fixture, {
    HashMap::<Vec<u8>, usize>::from_iter(fixture.into_iter())
});

bench_iter!(bench_iter_array, fixture, {
    Array::<usize>::from_iter(fixture.into_iter())
});

macro_rules! bench_contains_key {
    ($name:ident, $fixture:ident, $ctor:expr) => {
        #[bench]
        fn $name(b: &mut test::Bencher) {
            b.bytes = (OUTER_LEN * INNER_LEN) as u64;
            let $fixture = make_fixture();
            let haystack = $ctor;

            b.iter(|| {
                for &(ref key, _) in $fixture.iter() {
                    test::black_box(haystack.contains_key(&**key));
                }
            })
        }

    }
}

bench_contains_key!(bench_contains_key_btreemap, fixture, {
    BTreeMap::<Vec<u8>, usize>::from_iter(fixture.iter().cloned())
});

bench_contains_key!(bench_contains_key_hashmap, fixture, {
    HashMap::<Vec<u8>, usize>::from_iter(fixture.iter().cloned())
});

bench_contains_key!(bench_contains_key_array, fixture, {
    Array::<usize>::from_iter(fixture.iter().cloned())
});
