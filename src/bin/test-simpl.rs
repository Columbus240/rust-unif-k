extern crate generator;
use generator::{arb_nnf_var, FineFormIter, NnfAtom, NNF};

use proptest::prelude::*;

#[allow(unreachable_code)]
fn main() {
    use proptest::prelude::*;
    use proptest::strategy::*;
    use proptest::test_runner::*;

    let mut runner = TestRunner::default();

    const MAX_LOOPS: usize = 5_000_000;
    const NUM_VARIABLES: NnfAtom = 5;

    let mut old_smaller = 0;
    let mut new_smaller = 0;
    let mut equal = 0;

    for i in 0..MAX_LOOPS {
        let nnf_val = arb_nnf_var(NUM_VARIABLES).new_tree(&mut runner).unwrap();

        let nnf = nnf_val.current();
    /*
    for (i, nnf) in FineFormIter::new(NUM_VARIABLES).enumerate() {
        if i > MAX_LOOPS {
            break;
        }
    */
        let nnf_simpl = nnf.clone().simpl();
        let nnf_simpl_new = nnf.clone().simpl_new();

        let eq0 = NNF::equiv_dec(&nnf, &nnf_simpl);
        let eq1 = NNF::equiv_dec(&nnf, &nnf_simpl_new);

        if !eq1 {
            println!(
                "{} into {} and {}",
                nnf.display_beautiful(),
                nnf_simpl.display_beautiful(),
                nnf_simpl_new.display_beautiful()
            );
            panic!();
        }

        match std::cmp::Ord::cmp(&nnf_simpl.len(), &nnf_simpl_new.len()) {
            std::cmp::Ordering::Less => {
                old_smaller += 1;
            }
            std::cmp::Ordering::Equal => {
                equal += 1;
            }
            std::cmp::Ordering::Greater => {
                println!(
                    "{} into {} and {}",
                    nnf.display_beautiful(),
                    nnf_simpl.display_beautiful(),
                    nnf_simpl_new.display_beautiful()
                );
                new_smaller += 1;
            }
        }
        if i % 1000 == 0 {
            println!("stat {} {} {}", old_smaller, equal, new_smaller);
        }
    }
}
