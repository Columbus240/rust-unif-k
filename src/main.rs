#![feature(once_cell)]
#![allow(dead_code)]

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

fn main() {
    /*
    rayon::ThreadPoolBuilder::new()
        .num_threads(16)
        .build_global()
        .unwrap();
    */

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

    let mut ff_iter = fineform_correct::FineFormIter::new(1);

    let mut i = 0;

    /*
    for nnf in ff_iter {
    i +=1;
    println!("{}", nnf.display_beautiful());
    if i > 10000 { break; }
    }
    panic!();
    */

    fn decide_unifiability_unsimplified_direct(nnf: NNF) -> Result<bool, ClauseSetIrred> {
        let clause_set_waiting = ClauseSetWaiting::from_nnf(nnf);
        let clause_set_atoms: ClauseSetAtoms = clause_set_waiting.process_disjs();
        let clause_set_irred: ClauseSetIrred = clause_set_atoms.process_atoms();
        let clause_set_irred_simplified: ClauseSetIrred = clause_set_irred.simplify_unifiability();

        let backup = clause_set_irred_simplified.clone();
        clause_set_irred_simplified.is_unifiable().ok_or(backup)
    }

    fn decide_unifiability_simplified_direct(nnf: NNF) -> Result<bool, ClauseSetIrred> {
        decide_unifiability_unsimplified_direct(nnf.simpl())
    }

    fn debug_unifiability(index: usize, mut ff_iter: FineFormIter) {
        for _ in 0..index {
            ff_iter.next();
        }

        let nnf = ff_iter.next().unwrap();
        let clause_waiting_conj = ClauseWaitingConj::from_nnf(nnf.clone());
        //println!("unsimpl {:?}", clause_waiting_conj);
        let clause_waiting_disj = clause_waiting_conj.process_conjs();
        //println!("unsimpl {:?}", clause_waiting_disj);
        let clause_set_waiting = ClauseSetWaiting::from_clause(clause_waiting_disj);
        //println!("unsimpl {:?}", clause_set_waiting);
        let clause_set_atoms: ClauseSetAtoms = clause_set_waiting.process_disjs();
        println!("unsimpl {:?}", clause_set_atoms);
        let clause_set_irred: ClauseSetIrred = clause_set_atoms.process_atoms();
        //println!("unsimpl {:?}", clause_set_irred);
        let clause_set_irred_simplified: ClauseSetIrred = clause_set_irred.simplify_unifiability();
        println!("unsimpl {:?}", clause_set_irred_simplified);
        let unifiable = clause_set_irred_simplified.is_unifiable();
        println!("unsimpl unifiable {:?}", unifiable);

        println!();

        let nnf = nnf.simpl();
        let clause_waiting_conj = ClauseWaitingConj::from_nnf(nnf.clone());
        //println!("simpl {:?}", clause_waiting_conj);
        let clause_waiting_disj = clause_waiting_conj.process_conjs();
        //println!("simpl {:?}", clause_waiting_disj);
        let clause_set_waiting = ClauseSetWaiting::from_clause(clause_waiting_disj);
        //println!("simpl {:?}", clause_set_waiting);
        let clause_set_atoms: ClauseSetAtoms = clause_set_waiting.process_disjs();
        println!("simpl {:?}", clause_set_atoms);
        let clause_set_irred: ClauseSetIrred = clause_set_atoms.process_atoms();
        //println!("simpl {:?}", clause_set_irred);
        let clause_set_irred_simplified: ClauseSetIrred = clause_set_irred.simplify_unifiability();
        println!("simpl {:?}", clause_set_irred_simplified);
        let unifiable = clause_set_irred_simplified.is_unifiable();
        println!("simpl unifiable {:?}", unifiable);
    }
    debug_unifiability(10, ff_iter);
    return;

    while let Some(nnf) = ff_iter.next() {
        let unif_ud = decide_unifiability_unsimplified_direct(nnf.clone());
        let unif_sd = decide_unifiability_simplified_direct(nnf.clone());

        match (unif_ud, unif_sd) {
            (Ok(b0), Ok(b1)) => {
                if b0 != b1 {
                    println!("index: {}", i);
                    println!("formula unsimplified: {}", nnf.display_beautiful());
                    println!(
                        "formula simplified: {}",
                        nnf.clone().simpl().display_beautiful()
                    );
                    println!(
                        "formula simplified slow: {}",
                        nnf.simpl_slow().display_beautiful()
                    );
                    println!("unifiability unsimplified: {}", b0);
                    println!("unifiability simplified: {}", b1);
                    return;
                }
            }
            (Ok(b0), Err(clause_set_irred)) => {
                println!("index: {}", i);
                println!("formula b: {}", nnf.display_beautiful());
                println!("unifiability: {}", b0);
                println!(
                    "but the simplifying algorithm returned {:?}",
                    clause_set_irred
                );
                println!(
                    "clause_set b: {}",
                    clause_set_irred.to_nnf_boxed().display_beautiful()
                );
                return;
            }
            (Err(clause_set_irred), _) => {
                println!("index: {}", i);
                println!("formula b: {}", nnf.display_beautiful());
                //println!("clause_set: {:?}", clause_set_irred);
                println!("clause_set : {:?}", clause_set_irred);
                //println!("clause_set b: {}", clause_set_irred.to_nnf_boxed().display_beautiful());
                println!(
                    "clause_set b: {}",
                    clause_set_irred.to_nnf_boxed().display_beautiful()
                );
                println!();
            }
        }

        //TODO: Without simplification and using `ClauseSetIrred::from_nnf`, most problems are solvable.
        // But using simplification, this is not the case anymore.
        // What is the problem?
        // And going via `ClauseSetAtoms::unifiability_simplify` it also doesn't work.
        //let nnf = nnf.simpl();
        //let clause_set_atoms = ClauseSetAtoms::from_nnf(nnf.clone());
        //let clause_set_simpl0 = clause_set_atoms.unifiability_simplify();
        //let clause_set_irred = clause_set_simpl0.process_atoms();
        i += 1;
        if i % 10 == 0 {
            println!(
                "current index: {}, current level: {}",
                i,
                ff_iter.get_curr_level()
            );
        }
        if ff_iter.get_curr_level() > 1 {
            break;
        }
        if i > 1000 {
            break;
        }
    }
    println!("level: {}, count {}", ff_iter.get_curr_level(), i);
    let nnf = ff_iter.next().unwrap();
    println!("formula b: {}", nnf.display_beautiful());
    let clause_set_atoms = ClauseSetAtoms::from_nnf(nnf.clone());
    println!("clause_set_atoms : {:?}\n", clause_set_atoms);
    let clause_set_simpl0 = clause_set_atoms.unifiability_simplify();
    //println!("clause_set: {:?}", clause_set_irred);
    println!("clause_set_simpl0 : {:?}", clause_set_simpl0);
}
