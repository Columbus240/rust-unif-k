//! Go through all normal forms and decide unifiability.
extern crate generator;
use generator::decider::ClauseSet;
use generator::FineFormIter;

use atomic_counter::{AtomicCounter, RelaxedCounter};
use rayon::prelude::*;

fn main() {
    let dec_false = RelaxedCounter::new(0);
    let dec_true = RelaxedCounter::new(0);
    let undecidable = RelaxedCounter::new(0);

    let mut stuck_clauses: Vec<(usize, ClauseSet)> = Vec::new();

    FineFormIter::new(1)
        .take(1000)
        .enumerate()
        //        .par_bridge()
        .for_each(|(i, nnf)| {
            let nnf_simpl = nnf.simpl();
            let deg = nnf_simpl.degree();
            let nnf_simpl_unif = nnf_simpl.check_unifiable();
            //println!("formula: {}", nnf.display_beautiful());
            match nnf_simpl_unif {
                Ok(b) => {
                    if b {
                        dec_true.inc();
                    } else {
                        dec_false.inc();
                    }
                    println!("index {}, degree {}, unifiable: {}", i, deg, b);
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
        });

    // texify stuck clauses
    println!("\\begin{{tabular}}{{cl}}");
    println!("\\toprule");
    for (i, set) in stuck_clauses.into_iter() {
        println!("{} & ${}$ \\\\", i, set.display_latex());
    }
    println!("\\bottomrule");
    println!("\\end{{tabular}}");
}
