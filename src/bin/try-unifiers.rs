extern crate generator;
use generator::FineFormIter;
use generator::NNF;

fn main() {
    // find the unifiers of the "anti-jerabek formula" p⇒⌷~p
    //let formula = NNF::impli(NNF::AndNNF::AtomPos(0), NNF::boxx(NNF::AtomNeg(0)));

    //let formula = FineFormIter::new(1).skip(3736).next().unwrap();
    //let formula = NNF::Or(vec![NNF::AtomPos(0), NNF::boxx(NNF::AtomPos(0)), NNF::boxx(NNF::AtomNeg(0))]);
    let formula = NNF::impli(
        NNF::And(vec![NNF::AtomPos(0), NNF::boxx(NNF::AtomPos(0))]),
        NNF::Bot,
    );
    let formula = formula.simpl();
    println!("formula: {}", formula.display_beautiful());

    for (i, unif) in FineFormIter::new(0).enumerate() {
        let unif = unif.simpl();
        let subst = formula.substitute_all(&unif);
        if subst.is_valid() {
            println!("index {}, {}", i, unif.display_beautiful());
        }
    }
}
