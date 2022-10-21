extern crate generator;
use generator::FineFormIter;

fn main() {
    let mut iter = FineFormIter::new(0);
    let mut i: usize = 0;
    while i < 10 {
        println!("iter: {:?}", iter);
        let nnf = iter.next().unwrap();
        println!("index {}, nnf: {}", i, nnf.display_beautiful());
        i += 1;
    }
}
