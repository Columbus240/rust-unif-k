extern crate generator;
use generator::{FineFormIter, NnfAtom, NNF};

#[allow(unreachable_code)]
fn main() {
    const MAX_LOOPS: usize = 1625;
    const NUM_VARIABLES: NnfAtom = 0;

    for (i, nnf) in FineFormIter::new(NUM_VARIABLES).enumerate() {
        if i > MAX_LOOPS {
            break;
        }
        let nnf_simpl_new = nnf.clone().simpl();
        assert!(NNF::check_using_spartacus(NNF::equiv_formula(
            nnf,
            nnf_simpl_new
        )));

        //assert!(NNF::equiv_dec(&nnf, &nnf_simpl_new));

        //if i % 20 == 0 {
        //println!("index {}, {}", i, nnf_simpl_new.display_beautiful());
        //}
    }
}
