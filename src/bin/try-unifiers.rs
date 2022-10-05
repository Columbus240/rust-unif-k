extern crate generator;
use generator::FineFormIter;
use generator::{arb_nnf_var, NnfAtom, NNF};

use std::collections::btree_map::BTreeMap;

fn main() {
    // find the unifiers of the "anti-jerabek formula" p⇒⌷~p
    //let formula = NNF::impli(NNF::AndNNF::AtomPos(0), NNF::boxx(NNF::AtomNeg(0)));

    let formula = FineFormIter::new(1).skip(3736).next().unwrap();
    let formula = formula.simpl();
    println!("formula: {}", formula.display_beautiful());
    let input = generator::fineform::enumerate_unifiers(3);

    let powerset = generator::fineform::TriplePowersetIterator::new(input.as_slice());

    'a: for set in powerset.clone() {
        let ff = set.into_ff();
        let unif = ff.to_nnf().simpl();

        let subst = formula.substitute_all(&unif);
        if subst.is_valid() {
            println!("{}", unif.display_beautiful());
        }
    }
}
