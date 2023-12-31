//! Go through all normal forms and decide unifiability.
#![allow(unused_imports)]
extern crate generator;
use generator::decider::ClauseSet;
use generator::FineFormNNFIter;

use atomic_counter::{AtomicCounter, RelaxedCounter};
use rayon::prelude::*;

use generator::NNF;

fn main() {
	/*
    let jerabeck: NNF = NNF::and(
        NNF::impli(NNF::boxx(NNF::AtomPos(0)), NNF::AtomPos(0)),
        NNF::impli(
            NNF::AtomPos(0),
            NNF::equiv_formula(NNF::AtomPos(1), NNF::boxx(NNF::AtomNeg(1))),
        ),
    );

    let jerabeck_simpl = jerabeck.clone().simpl();
    println!(
        "jerabeck formula: {}\njerabeck simplified: {}",
        jerabeck.display_beautiful(),
        jerabeck_simpl.display_beautiful()
    );
    match jerabeck_simpl.check_unifiable() {
        Ok(b) => {
            println!("decidability of the formula is {b}");
        }
        Err(e) => {
            println!("stuck at:\n{}", e.display_beautiful());
        }
    }
    return;
	*/

    let dec_false = RelaxedCounter::new(0);
    let dec_true = RelaxedCounter::new(0);
    let undecidable = RelaxedCounter::new(0);

    let mut stuck_clauses: Vec<(usize, ClauseSet)> = Vec::new();

    let iter = FineFormNNFIter::new(2).enumerate();

    for (i, nnf) in iter {
        let nnf_simpl = nnf.simpl();
        let deg = nnf_simpl.degree();
        if deg > 1 {
            println!("degree exceeds 1");
            break;
        }
        let nnf_simpl_unif = nnf_simpl.check_unifiable();
        //println!("formula: {}", nnf.display_beautiful());
        match nnf_simpl_unif {
            Ok(b) => {
                if b {
                    dec_true.inc();
                } else {
                    dec_false.inc();
                }
                println!("index {i}, degree {deg}, unifiable: {b}");
            }
            Err(e) => {
                undecidable.inc();
                println!(
                    "index {}, degree {}, gets stuck at:\n{}",
                    i,
                    deg,
                    e.display_beautiful()
                );
                stuck_clauses.push((i, e));
            }
        }
        println!(
            "stuck {} vs. dec true {} dec false {}",
            undecidable.get(),
            dec_true.get(),
            dec_false.get()
        );
    }

    // texify stuck clauses
    println!("\\begin{{tabular}}{{cl}}");
    println!("\\toprule");
    for (i, set) in stuck_clauses.into_iter() {
        println!("{} & ${}$ \\\\", i, set.display_latex());
    }
    println!("\\bottomrule");
    println!("\\end{{tabular}}");
}
