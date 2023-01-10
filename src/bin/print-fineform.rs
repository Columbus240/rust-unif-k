extern crate generator;
use generator::BasicFineFormNNFIter;
use generator::FineFormNNFIter;

fn main() {
    let mut iter = BasicFineFormNNFIter::new(0);
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

    let mut iter = FineFormNNFIter::new(0);
    let mut i: usize = 0;
    while i < 32 {
        let nnf = iter.next().unwrap().simpl();
        println!("index {}, nnf: {}", i, nnf.display_beautiful());
        i += 1;
    }
}
