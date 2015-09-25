//#![cfg(feature = "map")]
#![feature(test)]

extern crate test;
extern crate cchashmap;

use std::collections::{BTreeMap, HashMap};
use std::env;
use std::fs;
use std::io::{BufReader, BufRead};

use cchashmap::CCHashMap;

fn make_fixture() -> (Vec<String>) {
    let filename= env::var("FIXTURE").unwrap();
    let file = fs::File::open(filename).unwrap();

    let mut words = Vec::new();
    for line in BufReader::new(file).lines() {
        for word in line.unwrap().split(' ') {
            let w = word.to_owned();
            words.push(w);
        }
    }

    words
}

fn make_btreemap(fixture: &[String]) -> BTreeMap<Vec<u8>, usize> {
    let mut map = BTreeMap::new();
    for key in fixture.iter() {
        let key = key.as_bytes();

        let found = match map.get_mut(key) {
            Some(count) => { *count = *count + 1; true }
            None => false,
        };

        if !found {
            map.insert(key.to_owned(), 0);
        }
    }
    map
}

fn make_hashmap(fixture: &[String]) -> HashMap<Vec<u8>, usize> {
    let mut map = HashMap::with_capacity(fixture.len());
    for key in fixture.iter() {
        let key = key.as_bytes();

        let found = match map.get_mut(key) {
            Some(count) => { *count = *count + 1; true }
            None => false,
        };

        if !found {
            map.insert(key.to_owned(), 0);
        }
    }
    map
}

fn make_cchashmap(fixture: &[String]) -> CCHashMap<usize> {
    let mut map = CCHashMap::with_capacity(4096);

    for key in fixture.iter() {
        let count = map.entry(key.as_bytes()).or_insert(0);
        *count = *count + 1;
    }
    map
}

#[test]
fn test_hashmap() {
    let fixture = make_fixture();

    let haystack = make_cchashmap(&fixture);
    let buckets = haystack.buckets.iter().map(|b| b.len()).collect::<Vec<_>>();
    println!("{:?}", buckets);
}

macro_rules! bench_insert {
    ($name:ident, $ctor:ident) => {
        #[bench]
        fn $name(b: &mut test::Bencher) {
            let fixture = make_fixture();
            b.bytes = fixture.iter().fold(0, |sum, word| sum + word.len() as u64);

            b.iter(|| {
                let haystack = $ctor(&fixture);
                test::black_box(haystack)
            })
        }

    }
}

bench_insert!(bench_btreemap_insert, make_btreemap);
bench_insert!(bench_hashmap_insert, make_hashmap);
bench_insert!(bench_cchashmap_insert, make_cchashmap);

macro_rules! bench_iter {
    ($name:ident, $ctor:expr) => {
        #[bench]
        fn $name(b: &mut test::Bencher) {
            let fixture = make_fixture();
            b.bytes = fixture.iter().fold(0, |sum, word| sum + word.len() as u64);
            let haystack = $ctor(&fixture);

            b.iter(|| {
                for key in haystack.iter() {
                    test::black_box(key);
                }
            })
        }

    }
}

bench_iter!(bench_btreemap_iter, make_btreemap);
bench_iter!(bench_hashmap_iter, make_hashmap);
bench_iter!(bench_cchashmap_iter, make_cchashmap);

macro_rules! bench_get {
    ($name:ident, $ctor:expr) => {
        #[bench]
        fn $name(b: &mut test::Bencher) {
            let fixture = make_fixture();
            b.bytes = fixture.iter().fold(0, |sum, word| sum + word.len() as u64);
            let haystack = $ctor(&fixture);

            b.iter(|| {
                for key in fixture.iter() {
                    test::black_box(haystack.get(key.as_bytes()));
                }
            })
        }

    }
}

bench_get!(bench_btreemap_get, make_btreemap);
bench_get!(bench_hashmap_get, make_hashmap);
bench_get!(bench_cchashmap_get, make_cchashmap);

macro_rules! bench_contains_key {
    ($name:ident, $ctor:expr) => {
        #[bench]
        fn $name(b: &mut test::Bencher) {
            let fixture = make_fixture();
            b.bytes = fixture.iter().fold(0, |sum, word| sum + word.len() as u64);
            let haystack = $ctor(&fixture);

            b.iter(|| {
                for key in fixture.iter() {
                    test::black_box(haystack.contains_key(key.as_bytes()));
                }
            })
        }

    }
}

bench_contains_key!(bench_key_btreemap_contains, make_btreemap);
bench_contains_key!(bench_key_hashmap_contains, make_hashmap);
bench_contains_key!(bench_key_cchashmap_contains, make_cchashmap);

macro_rules! bench_clone {
    ($name:ident, $ctor:expr) => {
        #[bench]
        fn $name(b: &mut test::Bencher) {
            let fixture = make_fixture();
            b.bytes = fixture.iter().fold(0, |sum, word| sum + word.len() as u64);
            let haystack = $ctor(&fixture);

            b.iter(|| {
                test::black_box(haystack.clone());
            })
        }

    }
}

bench_clone!(bench_btreemap_clone, make_btreemap);
bench_clone!(bench_hashmap_clone, make_hashmap);
bench_clone!(bench_cchashmap_clone, make_cchashmap);

macro_rules! bench_remove {
    ($name:ident, $ctor:expr) => {
        #[bench]
        fn $name(b: &mut test::Bencher) {
            let fixture = make_fixture();
            b.bytes = fixture.iter().fold(0, |sum, word| sum + word.len() as u64);
            let haystack = $ctor(&fixture);

            b.iter(|| {
                let mut haystack = haystack.clone();
                for key in fixture.iter() {
                    test::black_box(haystack.remove(key.as_bytes()));
                }
            })
        }

    }
}

bench_remove!(bench_btreemap_remove, make_btreemap);
bench_remove!(bench_hashmap_remove, make_hashmap);
bench_remove!(bench_cchashmap_remove, make_cchashmap);
