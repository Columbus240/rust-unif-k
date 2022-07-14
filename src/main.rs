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

use crate::decider::*;
use crate::fineform_correct::*;
use crate::nnf::*;

#[allow(unreachable_code)]
fn main() {
    rayon::ThreadPoolBuilder::new()
        .num_threads(16)
        .build_global()
        .unwrap();

    /*
    for i in fineform_correct::PowersetIter::new(20).step_by(0xFFFF) {
        println!("{:?}", i);
    }
    */
    /*
    for _ in 0..10000 {
    use nnf::NNF;
    let formula: NNF = nnf::arb_nnf().new_tree(&mut runner).unwrap().current().simpl();
    //let formula: NNF = NNF::And(vec![NNF::AtomPos(0), NNF::NnfBox(Box::new(NNF::Top))]);
    //let formula: NNF = NNF::NnfBox(Box::new(NNF::Top));
    let clause_set_waiting = ClauseSetWaiting::from_nnf(formula.clone());
    let clause_set_disj = clause_set_waiting.process_disjs();
    let clause_set_irred = clause_set_disj.process_atoms();

    // Now, the algorithm is correct if, `clause_set_irred` is valid iff `formula` is valid.
    // I.e. if the formula `(clause_set_irred <-> T) <-> (formula <-> T)` is valid.
    let formula_valid = formula.clone().is_valid();
    let clause_set_valid = clause_set_irred.to_nnf_boxed().is_valid();
    if None == clause_set_irred.is_unifiable() {
    println!("formula b: {}", formula.display_beautiful());
    println!("clause_set: {:?}", clause_set_irred);
    println!("clause_set b: {}", clause_set_irred.to_nnf_boxed().display_beautiful());
    println!("equiv: {}", formula_valid == clause_set_valid);
    println!("unifiability: {:?}", clause_set_irred.is_unifiable());
    }
    assert_eq!(formula_valid, clause_set_valid);
    assert_eq!(formula_valid, clause_set_irred.is_valid());
    }
    */

    #[allow(unused_variables)]
    #[allow(unused_mut)]
    let mut ff_iter = fineform_correct::FineFormIter::new(1);

    /*
    fn decide_unifiability_unsimplified_direct(nnf: NNF) -> Result<bool, ClauseSetIrred> {
        let clause_set_waiting = ClauseSetWaiting::from_nnf(nnf);
        let clause_set_atoms: ClauseSetAtoms = clause_set_waiting.process_conjs();
        let clause_set_irred: ClauseSetIrred = clause_set_atoms.process_atoms();
        let clause_set_irred_simplified: ClauseSetIrred = clause_set_irred.unifiability_simplify();

        let backup = clause_set_irred_simplified.clone();
        clause_set_irred_simplified.is_unifiable().ok_or(backup)
    }

    fn decide_unifiability_simplified_direct(nnf: NNF) -> Result<bool, ClauseSetIrred> {
        decide_unifiability_unsimplified_direct(nnf.simpl())
    }
    */

    fn debug_unifiability(index: usize, mut ff_iter: FineFormIter) {
        for _ in 0..index {
            ff_iter.next();
        }

        /*
            let nnf = ff_iter.next().unwrap();
            let clause_waiting_conj = ClauseWaitingConj::from_nnf(nnf.clone());
            //println!("unsimpl {:?}", clause_waiting_conj);
            let clause_waiting_disj_u = clause_waiting_conj.process_conjs();
            //println!("unsimpl {:?}", clause_waiting_disj_u);
            let clause_set_atoms_u = ClauseSetAtoms::from_clause(clause_waiting_disj_u);
            //println!("unsimpl {:?}", clause_set_atoms_u);
            let clause_set_irred_u: ClauseSetIrred = clause_set_atoms_u.process_atoms();
            println!("unsimpl {:?}", clause_set_irred_u);
            let clause_set_irred_simplified: ClauseSetIrred =
                clause_set_irred_u.clone().unifiability_simplify();
            println!("unsimpl {:?}", clause_set_irred_simplified);
            let unifiable = clause_set_irred_simplified.is_unifiable();
            println!("unsimpl unifiable {:?}", unifiable);

            println!();

            let nnf = nnf.simpl();
            let clause_waiting_conj = ClauseWaitingConj::from_nnf(nnf);
            //println!("simpl {:?}", clause_waiting_conj);
            let clause_waiting_disj_s = clause_waiting_conj.process_conjs();
            //println!("simpl {:?}", clause_waiting_disj_s);
            let clause_set_atoms_s = ClauseSetAtoms::from_clause(clause_waiting_disj_s);
            //println!("simpl {:?}", clause_set_atoms_s);
            let clause_set_irred_s: ClauseSetIrred = clause_set_atoms_s.process_atoms();
            println!("simpl {:?}", clause_set_irred_s);
            assert!(NNF::equiv_dec(
                &clause_set_irred_s.to_nnf_boxed(),
                &clause_set_irred_u.to_nnf_boxed()
            ));
            let clause_set_irred_simplified: ClauseSetIrred =
                clause_set_irred_s.unifiability_simplify();
            println!("simpl {:?}", clause_set_irred_simplified);
            let unifiable = clause_set_irred_simplified.is_unifiable();
            println!("simpl unifiable {:?}", unifiable);
        */
    }
    //debug_unifiability(27, ff_iter);

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
            let mut nnf_val = arb_nnf().new_tree(&mut runner).unwrap();
            match nnf_val.current().check_unifiable() {
                Ok(_) => {
                    decidables += 1;
                    i += 1;
                }
                Err(clause_set_irred) => {
                    println!("{}", clause_set_irred.display_beautiful());
                    i += 1;
                }
            }

            if i - decidables > 50 {
                println!("loops {}, dec {}", i, decidables);
                break;
            }
        }
    }

    find_random_non_decidables();

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
