extern crate generator;
use generator::BasicFineFormIter;
use generator::FineFormIter;

fn main() {
    let mut iter = BasicFineFormIter::new(0);
    let mut i: usize = 0;
    while i < 32 {
        let nnf = iter.next().unwrap().simpl();
        println!(
            "index {}, level {}, nnf: {}",
            i,
            iter.get_curr_level(),
            nnf.display_beautiful()
        );
        i += 1;
    }

    let mut iter = FineFormIter::new(0);
    let mut i: usize = 0;
    while i < 32 {
        let nnf = iter.next().unwrap().simpl();
        println!("index {}, nnf: {}", i, nnf.display_beautiful());
        i += 1;
    }
}
