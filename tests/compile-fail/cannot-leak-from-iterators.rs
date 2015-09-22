extern crate cchashmap;

use cchashmap::Array;

fn main() {
    let (key, value) = {
        let mut array = Array::new();
        array.insert(b"123", 4);
        array.iter().next().unwrap() //~ Error `array` does not live long enough
    };

    let (key, value) = {
        let mut array = Array::new();
        array.insert(b"123", 4);
        array.iter_mut().next().unwrap() //~ Error `array` does not live long enough
    };

    let (key, value) = {
        let mut array = Array::new();
        array.insert(b"123", 4);
        array.drain().next().unwrap() //~ Error `array` does not live long enough
    };
}
