extern crate cchashmap;

use cchashmap::array::ArrayMap;

fn main() {
    let (key, value) = {
        let mut array = ArrayMap::new();
        array.insert(b"123", 4);
        array.iter().next().unwrap() //~ Error `array` does not live long enough
    };

    let (key, value) = {
        let mut array = ArrayMap::new();
        array.insert(b"123", 4);
        array.iter_mut().next().unwrap() //~ Error `array` does not live long enough
    };

    let (key, value) = {
        let mut array = ArrayMap::new();
        array.insert(b"123", 4);
        array.drain().next().unwrap() //~ Error `array` does not live long enough
    };

    let value = {
        let mut array = ArrayMap::new();
        array.insert(b"123", 4);
        array.get(b"123") //~ Error `array` does not live long enough
    };
}
