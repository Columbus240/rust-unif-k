#![allow(unused_imports)]
extern crate generator;
use generator::decider::*;
use generator::nnf_parser;
use generator::nnf_parser::*;
use generator::FineFormNNFIter;
use generator::NNF;
use rayon::prelude::*;
use std::collections::{BTreeMap, BTreeSet};

// The algorithm disagrees on
// index 173, unifier 4 should be fixed now.
// index 189, unifier 4
// index 237, unifier 4
// index 253, unifier 4
// is fixed, because they are now all stuck.

fn main() {
    // find the unifiers of the "anti-jerabek formula" p⇒⌷~p
    //let formula = NNF::impli(NNF::AndNNF::AtomPos(0), NNF::boxx(NNF::AtomNeg(0)));

    // This is the clause (p, ⌷⋄⋄T ⇒ ⌷(¬p∨⌷¬p)) ; ⌷⋄⌷⊥⇒p, ⌷⊥
    // which is unifiable but its only (known) unifiers are 10 of degree 3,
    // which are quite complicated. Can they be written more simply?
    // How to deduce that this formula is unifiable?
    let clause: ClauseIrred = ClauseIrred {
        irreducibles: {
            let mut set = BTreeSet::new();
            set.insert(PSI {
                atoms: {
                    let mut map = BTreeMap::new();
                    map.insert(0, LeftRight::Left);
                    map
                },
                lb: {
                    let mut set = BTreeSet::new();
                    set.insert(NNF::dia(NNF::dia(NNF::Top)));
                    set
                },
                rb: {
                    let mut set = BTreeSet::new();
                    set.insert(NNF::or(NNF::AtomNeg(0), NNF::boxx(NNF::AtomNeg(0))));
                    set
                },
            });
            set.insert(PSI {
                atoms: {
                    let mut map = BTreeMap::new();
                    map.insert(0, LeftRight::Right);
                    map
                },
                lb: {
                    let mut set = BTreeSet::new();
                    set.insert(NNF::dia(NNF::boxx(NNF::Bot)));
                    set
                },
                rb: {
                    let mut set = BTreeSet::new();
                    set.insert(NNF::Bot);
                    set
                },
            });
            set
        },
    };
    /*
    let clause: ClauseIrred = ClauseIrred {
        irreducibles: {
            let mut set = BTreeSet::new();
            set.insert(PSI {
                atoms: {
                    let mut map = BTreeMap::new();
                    map.insert(0, LeftRight::Left);
                    map
                },
                lb: {
                    let mut set = BTreeSet::new();
                    set.insert(NNF::boxx(NNF::boxx(NNF::Bot)));
                    set
                },
                rb: {
                    let mut set = BTreeSet::new();
                    set.insert(NNF::Bot);
                    set
                },
            });
            set.insert(PSI {
                atoms: {
                    let mut map = BTreeMap::new();
                    map.insert(0, LeftRight::Right);
                    map
                },
                lb: {
                    let mut set = BTreeSet::new();
                    set.insert(NNF::dia(NNF::Top));
                    set
                },
                rb: {
                    let mut set = BTreeSet::new();
                    set.insert(NNF::dia(NNF::AtomPos(0)));
                    set
                },
            });
            set
        },
    };
    */
    println!("{}", clause.display_beautiful());
    let formula = clause.to_nnf();

    //let formula = FineFormIter::new(1).nth(125).unwrap();
    //let formula = NNF::Or(vec![NNF::AtomPos(0), NNF::boxx(NNF::AtomPos(0)), NNF::boxx(NNF::AtomNeg(0))]);
    /*let formula = NNF::impli(
        NNF::And(vec![NNF::AtomPos(0), NNF::boxx(NNF::AtomPos(0))]),
        NNF::Bot,
    );*/
    let formula = formula.simpl();
    println!("formula: {}", formula.display_beautiful());
    match formula.clone().check_unifiable() {
        Ok(b) => {
            println!("unifiability-dec {b}");
        }
        Err(e) => {
            println!("unifiability-dec stuck {}", e.display_beautiful());
        }
    }

    FineFormNNFIter::new(0)
        .enumerate()
        //.take(900)
        .par_bridge()
        .for_each(|(i, unif)| {
            let unif = unif.simpl();
            let subst = formula.substitute_all(&unif).simpl();
            if i % 100 == 0 {
                println!("index {} has degree {}", i, unif.degree());
            }
            if subst.is_valid() {
                println!("index {}, {}", i, unif.display_beautiful());
            }
        });
}
