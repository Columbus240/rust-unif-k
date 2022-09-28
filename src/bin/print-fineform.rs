extern crate generator;
use generator::FineFormIter;

fn main() {
    for (i, nnf) in FineFormIter::new(1).enumerate() {
        println!("index {}: {}", i, nnf.display_beautiful());
        if i > 1600 {
            return;
        }
    }
}
