#![feature(test)]

extern crate test;
extern crate cchashmap;

use std::collections::{BTreeMap, HashMap};
use std::env;
use std::fs;
use std::io::{BufReader, BufRead};
use std::thread;

use cchashmap::CCHashMap;
//use cchashmap::array::ArrayMap;

fn make_fixture() -> (Vec<String>) {
    let filename= env::var("FIXTURE").unwrap();
    let file = fs::File::open(filename).unwrap();

    let mut words = Vec::new();
    for line in BufReader::new(file).lines() {
        for word in line.unwrap().split(' ') {
            for suffix in "ab".chars() {
                let mut w = word.to_owned();
                w.push(suffix);
                words.push(w);
            }
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

/*
fn make_arraymap(fixture: &[String]) -> ArrayMap<usize> {
    let mut map = ArrayMap::<usize>::new();
    for key in fixture.iter() {
        let count = map.entry(key.as_bytes()).or_insert(0);
        *count = *count + 1;
    }
    map
}
*/

fn make_cchashmap(fixture: &[String]) -> CCHashMap<usize> {
    let mut map = CCHashMap::<usize>::with_capacity(4096);
    for key in fixture.iter() {
        let count = map.entry(key.as_bytes()).or_insert(0);
        *count = *count + 1;
    }
    map
}

#[test]
fn test_hashmap() {
    let fixture = make_fixture();

    println!("before!");
    thread::sleep_ms(3000);

    let _hashmap = make_hashmap(&fixture);

    println!("after!");
    thread::sleep_ms(3000);
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

bench_insert!(bench_insert_btreemap, make_btreemap);
bench_insert!(bench_insert_hashmap, make_hashmap);
//bench_insert!(bench_insert_arraymap, make_arraymap);
bench_insert!(bench_insert_cchashmap, make_cchashmap);

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

bench_iter!(bench_iter_btreemap, make_btreemap);
bench_iter!(bench_iter_hashmap, make_hashmap);
//bench_iter!(bench_iter_arraymap, make_arraymap);
bench_iter!(bench_iter_cchashmap, make_cchashmap);

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

bench_get!(bench_get_btreemap, make_btreemap);
bench_get!(bench_get_hashmap, make_hashmap);
//bench_get!(bench_get_arraymap, make_arraymap);
bench_get!(bench_get_cchashmap, make_cchashmap);
