/*
#![feature(test)]

extern crate test;
extern crate cchashmap;
extern crate byteorder;

use std::collections::{BTreeSet, HashSet};
use std::iter::FromIterator;
use byteorder::{ByteOrder, NativeEndian};
use cchashmap::CCHashSet;

static OUTER_LEN: usize = 1000000;
static INNER_LEN: usize = 5;


fn make_fixture() -> Vec<Vec<u8>> {
    let mut haystack = Vec::with_capacity(OUTER_LEN);
    let mut bytes = [0; 8];

    for index in 0 .. OUTER_LEN {
        let mut hay = Vec::with_capacity(8);
        NativeEndian::write_u64(&mut bytes, index as u64);
        for _ in 0 .. INNER_LEN {
            hay.extend(&bytes);
        }
        haystack.push(hay);
    }

    haystack
}

fn to_btreeset(fixture: &[Vec<u8>]) -> BTreeSet<Vec<u8>> {
    BTreeSet::from_iter(fixture.iter().map(|key| key.to_vec()))
}

fn to_hashset(fixture: &[Vec<u8>]) -> HashSet<Vec<u8>> {
    HashSet::from_iter(fixture.iter().map(|key| key.to_vec()))
}

fn to_cchashset(fixture: &[Vec<u8>]) -> CCHashSet {
    CCHashSet::from_iter(fixture.iter().map(|key| key.to_vec()))
}

macro_rules! bench_push {
    ($name:ident, $ty:ty, $ctor:ident) => {
        #[bench]
        fn $name(b: &mut test::Bencher) {
            b.bytes = (OUTER_LEN * INNER_LEN) as u64;
            let fixture = make_fixture();

            b.iter(|| {
                let haystack: $ty = $ctor(&fixture);
                test::black_box(haystack)
            })
        }

    }
}

bench_push!(bench_push_btreeset, BTreeSet<Vec<u8>>, to_btreeset);
bench_push!(bench_push_hashset, HashSet<Vec<u8>>, to_hashset);
bench_push!(bench_push_cchashset, CCHashSet, to_cchashset);

macro_rules! bench_iter {
    ($name:ident, $ty:ty, $ctor:ident) => {
        #[bench]
        fn $name(b: &mut test::Bencher) {
            b.bytes = (OUTER_LEN * INNER_LEN) as u64;
            let haystack = $ctor(&make_fixture());

            b.iter(|| {
                for key in haystack.iter() {
                    test::black_box(key);
                }
            })
        }

    }
}

bench_iter!(bench_iter_btreeset, BTreeSet<Vec<u8>>, to_btreeset);
bench_iter!(bench_iter_hashset, HashSet<Vec<u8>>, to_hashset);
bench_iter!(bench_iter_cchashset, Bucket, to_cchashset);

/*
#[bench]
fn bench_contains_vec(b: &mut test::Bencher) {
    b.bytes = (OUTER_LEN * INNER_LEN) as u64;
    let fixture = make_fixture();
    let haystack = fixture.clone();

    b.iter(|| {
        for key in fixture.iter() {
            assert!(haystack.iter().any(|k| key == k));
        }
    })
}

#[bench]
fn bench_contains_bucket(b: &mut test::Bencher) {
    b.bytes = (OUTER_LEN * INNER_LEN) as u64;
    let fixture = make_fixture();
    let haystack = Bucket::from_slice(&fixture);

    b.iter(|| {
        for key in fixture.iter() {
            assert!(haystack.contains(&key));
        }
    })
}
*/
*/
