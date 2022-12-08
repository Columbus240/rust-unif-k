extern crate generator;
use generator::FineFormIter;

fn main() {
    let mut iter = FineFormIter::new(2);
    let mut i: usize = 0;
    while i < 100 {
        let nnf = iter.next().unwrap().simpl();
        println!("index {}, nnf: {}", i, nnf.display_beautiful());
        i += 1;
    }
}
