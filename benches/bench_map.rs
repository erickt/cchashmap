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
    let filename= env::var("FIXTURE").expect("FIXTURE environment variable not set");
    let file = fs::File::open(filename).expect("FIXTURE file does not exist");

    let mut words = Vec::new();
    for line in BufReader::new(file).lines() {
        for word in line.unwrap().split(' ') {
            let w = word.to_owned();
            words.push(w);
        }
    }

    words
}

fn make_btreemap(fixture: &[String]) -> BTreeMap<Vec<u8>, ()> {
    let mut map = BTreeMap::new();
    for key in fixture.iter() {
        let key = key.as_bytes();

        /*
        let found = match map.get_mut(key) {
            Some(count) => { *count = *count + 1; true }
            None => false,
        };

        if !found {
            map.insert(key.to_owned(), 0);
        }
        */

        map.insert(key.to_owned(), ());
    }
    map
}

fn make_hashmap(fixture: &[String]) -> HashMap<Vec<u8>, ()> {
    let mut map = HashMap::with_capacity(fixture.len());
    for key in fixture.iter() {
        let key = key.as_bytes();

        /*
        let found = match map.get_mut(key) {
            Some(count) => { *count = *count + 1; true }
            None => false,
        };

        if !found {
            map.insert(key.to_owned(), 0);
        }
        */

        map.insert(key.to_owned(), ());
    }
    map
}

fn make_cchashmap(fixture: &[String], cap: usize) -> CCHashMap<()> {
    let mut map = CCHashMap::with_capacity(cap); //1024 * 1);

    for key in fixture.iter() {
        //let count = map.entry(key.as_bytes()).or_insert(0);
        //*count = *count + 1;
        //
        /*
        let inserted = match map.get_mut(key.as_bytes()) {
            Some(count) => {
                *count = *count + 1;
                true
            }
            None => false,
        };

        if !inserted {
            map.insert(key.as_bytes(), 0);
        }
        */
        map.insert(key.as_bytes(), ());
    }
    map
}


/*
#[test]
fn test_hashmap() {
    let fixture = make_fixture();

    let haystack = make_cchashmap(&fixture);
    let buckets = haystack.buckets.iter().map(|b| b.len()).collect::<Vec<_>>();
    println!("{:?}", buckets);
}
*/

macro_rules! bench_insert {
    ($name:ident, $ctor:expr, $haystack:ident, $after:expr) => {
        #[bench]
        fn $name(b: &mut test::Bencher) {
            let fixture = make_fixture();
            b.bytes = fixture.iter().fold(0, |sum, word| sum + word.len() as u64);

            b.iter(|| {
                let $haystack = $ctor(&fixture);
                $after;
                test::black_box($haystack)
            })
        }

    }
}

bench_insert!(bench_btreemap_insert, make_btreemap, haystack, {});
bench_insert!(bench_hashmap_insert, make_hashmap, haystack, {});
//bench_insert!(bench_cchashmap_insert, make_cchashmap);

bench_insert!(bench_cchashmap_insert_00512, (|fixture| make_cchashmap(fixture, 512)), haystack, {
    //assert_eq!(haystack.hits(), (0.0, 0.0, 0, 0, 0, 0, 0));
});

bench_insert!(bench_cchashmap_insert_01024, (|fixture| make_cchashmap(fixture, 1024)), haystack, {
    //assert_eq!(haystack.hits(), (0.0, 0.0, 0, 0, 0, 0, 0));
});

bench_insert!(bench_cchashmap_insert_02048, (|fixture| make_cchashmap(fixture, 2048)), haystack, {
    //assert_eq!(haystack.hits(), (0.0, 0.0, 0, 0, 0, 0, 0));
});

bench_insert!(bench_cchashmap_insert_04096, (|fixture| make_cchashmap(fixture, 4096)), haystack, {
    //assert_eq!(haystack.hits(), (0.0, 0.0, 0, 0, 0, 0, 0));
});

bench_insert!(bench_cchashmap_insert_08192, (|fixture| make_cchashmap(fixture, 8192)), haystack, {
    //assert_eq!(haystack.hits(), (0.0, 0.0, 0, 0, 0, 0, 0));
});

bench_insert!(bench_cchashmap_insert_16384, (|fixture| make_cchashmap(fixture, 16384)), haystack, {
    //assert_eq!(haystack.hits(), (0.0, 0.0, 0, 0, 0, 0, 0));
});

bench_insert!(bench_cchashmap_insert_32768, (|fixture| make_cchashmap(fixture, 32768)), haystack, {
    //assert_eq!(haystack.hits(), (0.0, 0.0, 0, 0, 0, 0, 0));
});

/*
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
*/

macro_rules! bench_get {
    ($name:ident, $ctor:expr, $haystack:ident, $after:expr) => {
        #[bench]
        fn $name(b: &mut test::Bencher) {
            let fixture = make_fixture();
            //let fixture_map = make_hashmap(&fixture);
            b.bytes = fixture.iter().fold(0, |sum, word| sum + word.len() as u64);
            let $haystack = $ctor(&fixture);

            b.iter(|| {
                for key in fixture.iter() {
                    //let fixture_value = fixture_map.get(key.as_bytes());
                    let haystack_value = $haystack.get(key.as_bytes());
                    //assert_eq!(fixture_value, haystack_value);

                    test::black_box(haystack_value);
                }

                $after
            })
        }

    }
}

bench_get!(bench_btreemap_get, make_btreemap, haystack, {});
bench_get!(bench_hashmap_get, make_hashmap, haystack, {});

bench_get!(bench_cchashmap_get_00512, (|fixture| make_cchashmap(fixture, 512)), haystack, {
    //assert_eq!(haystack.hits(), (0.0, 0.0, 0, 0, 0, 0, 0));
});

bench_get!(bench_cchashmap_get_01024, (|fixture| make_cchashmap(fixture, 1024)), haystack, {
    //assert_eq!(haystack.hits(), (0.0, 0.0, 0, 0, 0, 0, 0));
});

bench_get!(bench_cchashmap_get_02048, (|fixture| make_cchashmap(fixture, 2048)), haystack, {
    //assert_eq!(haystack.hits(), (0.0, 0.0, 0, 0, 0, 0, 0));
});

bench_get!(bench_cchashmap_get_04096, (|fixture| make_cchashmap(fixture, 4096)), haystack, {
    //assert_eq!(haystack.hits(), (0.0, 0.0, 0, 0, 0, 0, 0));
});

bench_get!(bench_cchashmap_get_08192, (|fixture| make_cchashmap(fixture, 8192)), haystack, {
    //assert_eq!(haystack.hits(), (0.0, 0.0, 0, 0, 0, 0, 0));
});

bench_get!(bench_cchashmap_get_16384, (|fixture| make_cchashmap(fixture, 16384)), haystack, {
    //assert_eq!(haystack.hits(), (0.0, 0.0, 0, 0, 0, 0, 0));
});

bench_get!(bench_cchashmap_get_32768, (|fixture| make_cchashmap(fixture, 32768)), haystack, {
    //assert_eq!(haystack.hits(), (0.0, 0.0, 0, 0, 0, 0, 0));
});

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

/*
bench_contains_key!(bench_btreemap_contains_key, make_btreemap);
bench_contains_key!(bench_hashmap_contains_key, make_hashmap);
bench_contains_key!(bench_cchashmap_contains_key, make_cchashmap);

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
*/
