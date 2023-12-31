#![allow(unused_imports)]
extern crate generator;
use generator::FineFormNNFIter;
use generator::NNF;
use rayon::prelude::*;

fn main() {
    'a: for (i, nnf) in FineFormNNFIter::new(1).enumerate() {
        let nnf_simpl = nnf.simpl();
        if let Ok(b) = nnf_simpl.clone().check_unifiable() {
            if !b {
                println!("index {i}, non-unif skipped");
                continue 'a;
            }
            let c = FineFormNNFIter::new(0)
                .take(250)
                .enumerate()
                //.par_bridge()
                .any(|(j, unif)| {
                    let unif = unif.simpl();
                    let subst = nnf_simpl.substitute_all(&unif).simpl();
                    if subst.is_valid() {
                        if b {
                            println!("index {i}, unif ok, unif: {}", unif.display_beautiful());
                            return true;
                        } else {
                            println!("index {i}, disagree unif {j}");
                            return true;
                        }
                    }
                    false
                });
            if c {
                continue 'a;
            }
            if b {
                println!("index {i}, disagree non-unif");
            } else {
                println!("index {i}, non-unif ok");
            }
        /*
            if !b {
                println!("index {}, nonunif", i);
                continue 'a;
            }
            let deg = nnf_simpl.degree();
            let mut unif_iter = FineFormIter::new(0);
            while unif_iter.get_curr_level() <= deg {
                let subst = nnf_simpl.clone().substitute_all(&unif_iter.next().unwrap());
                if subst.is_valid() {
                    println!("index {}, unif ok", i);
                    continue 'a;
                }
            }
            panic!("index {}, formula {}", i, nnf_simpl.display_beautiful());
        */
        } else {
            println!("index {i}, non-dec");
        }
    }
}
