extern crate generator;
use generator::{FineFormIter, NnfAtom, NNF};

#[allow(unreachable_code)]
fn main() {
    const MAX_LOOPS: usize = 8000;
    const NUM_VARIABLES: NnfAtom = 1;

    for (i, nnf) in FineFormIter::new(NUM_VARIABLES).enumerate() {
        if i > MAX_LOOPS {
            break;
        }
        let nnf_simpl_new = nnf.clone().simpl();

        if i % 20 == 0 {
            println!("index {}, {}", i, nnf_simpl_new.display_beautiful());
        }
    }
}
