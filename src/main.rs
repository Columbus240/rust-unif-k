#![feature(once_cell)]

#[allow(unused_imports)]
use std::collections::btree_map::BTreeMap;
#[allow(unused_imports)]
use std::collections::btree_set::BTreeSet;

mod decider;
mod fineform;
mod fineform_correct;
//mod lazy_decider;
//mod lazy_nnf;
mod nnf;
mod powerset;

#[allow(unused_imports)]
use fineform::*;

#[allow(unused_imports)]
use crate::decider::*;
use crate::fineform_correct::*;
use crate::nnf::*;

#[allow(unreachable_code)]
fn main() {
    rayon::ThreadPoolBuilder::new()
        .num_threads(16)
        .build_global()
        .unwrap();

    #[allow(unused_variables)]
    #[allow(unused_mut)]
    let mut ff_iter = fineform_correct::FineFormIter::new(1);

    /*
    find_non_decidables(ff_iter);
    return;
    */

    fn find_random_non_decidables() {
        use proptest::prelude::*;
        use proptest::strategy::*;
        use proptest::test_runner::*;

        let mut runner = TestRunner::default();

        let mut i = 0;
        let mut decidables = 0;

        loop {
            let nnf_val = arb_nnf().new_tree(&mut runner).unwrap();
            match nnf_val.current().simpl().check_unifiable() {
                Ok(b) => {
                    /*
                    let nnf_simpl = nnf_val.current().simpl_slow();
                            if !(nnf_simpl == NNF::Top && b)
                                && !(nnf_simpl == NNF::Bot && !b)
                                && !(!b
                                    && match nnf_simpl {
                                        NNF::NnfDia(_) => true,
                                        _ => false,
                                    })
                                && !(!b && nnf_simpl == NNF::NnfBox(Box::new(NNF::Bot)))
                            {
                                println!(
                                    "unif: {}\t {}",
                                    b,
                                    nnf_val.current().simpl_slow().display_beautiful()
                                );
                            }
                    */

                    decidables += 1;
                    i += 1;
                }
                Err(clause_set_irred) => {
                    println!("{}", clause_set_irred.display_beautiful());
                    i += 1;
                }
            }

            if i > 50000 {
                println!("loops {}, dec {}", i, decidables);
                break;
            }
        }
    }

    //find_random_non_decidables();
    find_non_decidables(ff_iter);

    fn find_non_decidables(mut ff_iter: FineFormIter) {
        let mut i = 0;
        while let Some(nnf) = ff_iter.next() {
            match nnf.clone().check_unifiable() {
                Ok(_) => {
                    //println!("unifiable: {}", b)
                }
                Err(clause_set_irred) => {
                    println!();
                    println!("index: {}", i);
                    println!("formula b: {}", nnf.display_beautiful());
                    println!("clause_set: {}", clause_set_irred.display_beautiful());
                    //println!("clause_set b: {}", clause_set_irred.to_nnf_boxed().display_beautiful());
                    //println!("clause_set b: {}", clause_set_irred.display_beautiful());
                    println!(
                        "index: {}, level: {}, curr_level_len: {}",
                        i,
                        ff_iter.get_curr_level(),
                        ff_iter.get_curr_level_len()
                    );
                    println!();
                    return;
                }
            }

            i += 1;
            /*
                if i % 10 == 0 {
                    println!(
                        "current index: {}, current level: {}, current formula: {}, count undec {}",
                        i,
                        ff_iter.get_curr_level(),
                        nnf.display_beautiful(),
                        undec
                    );
                }
            */
            if ff_iter.get_curr_level() > 2 {
                break;
            }
            if i > 1000 {
                break;
            }
        }
        println!("level: {}, count {}", ff_iter.get_curr_level(), i);
    }
}
