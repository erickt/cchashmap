/*
#![feature(test)]

extern crate test;
extern crate cchashmap;
extern crate byteorder;

use byteorder::{ByteOrder, NativeEndian};
use cchashmap::Bucket;

static OUTER_LEN: usize = 128;
static INNER_LEN: usize = 128;


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

macro_rules! bench_push {
    ($name:ident, $ty:ty, $fixture:ident, $ctor:expr) => {
        #[bench]
        fn $name(b: &mut test::Bencher) {
            b.bytes = (OUTER_LEN * INNER_LEN) as u64;
            let $fixture = make_fixture();

            b.iter(|| {
                let haystack: $ty = $ctor;
                test::black_box(haystack)
            })
        }

    }
}

bench_push!(bench_push_vec, Vec<Vec<u8>>, fixture, fixture.clone());
bench_push!(bench_push_bucket, Bucket, fixture, Bucket::from_slice(&fixture));

macro_rules! bench_iter {
    ($name:ident, $ty:ty, $fixture:ident, $ctor:expr) => {
        #[bench]
        fn $name(b: &mut test::Bencher) {
            b.bytes = (OUTER_LEN * INNER_LEN) as u64;
            let $fixture = make_fixture();
            let haystack: $ty = $ctor;

            b.iter(|| {
                for key in haystack.iter() {
                    test::black_box(key);
                }
            })
        }

    }
}

bench_iter!(bench_iter_vec, Vec<Vec<u8>>, fixture, fixture.clone());
bench_iter!(bench_iter_bucket, Bucket, fixture, Bucket::from_slice(&fixture));

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
