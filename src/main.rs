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

    #[allow(unused_imports)]
    use proptest::strategy::Strategy;
    #[allow(unused_imports)]
    use proptest::strategy::ValueTree;
    #[allow(unused_imports)]
    use proptest::test_runner::TestRunner;
    let mut runner = TestRunner::default();
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

    println!("powerset start");
    let mut i = 0;
    let mut ff_iter = fineform_correct::FineFormIter::new(2);
    while let Some(nnf) = ff_iter.next() {
	let clause_set_irred = ClauseSetWaiting::from_nnf(nnf.clone()).process_disjs().process_atoms();
	if None == clause_set_irred.is_unifiable() {
	    println!("formula b: {}", nnf.display_beautiful());
	    println!("clause_set: {:?}", clause_set_irred);
	    println!("clause_set b: {}", clause_set_irred.to_nnf_boxed().display_beautiful());
	    println!("index: {}", i);
	}
	i += 1;
	if i > 1000 {
	    break;
	}
    }
    println!("level: {}, count {}", ff_iter.get_curr_level(), i);
    println!("powerset end");
}
