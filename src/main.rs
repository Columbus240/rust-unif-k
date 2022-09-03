#![feature(once_cell)]
#![allow(dead_code)]

#[allow(unused_imports)]
use std::collections::btree_map::BTreeMap;
#[allow(unused_imports)]
use std::collections::btree_set::BTreeSet;

#[allow(unused_imports)]
use rayon::prelude::*;

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

/*
/// Conjecture: If `φ` is unifiable, then there exists a unifier of
/// modal degree at most the modal degree of `φ`, for single-variable
/// formulae.
/// This function is looking for counterexamples.
/// TODO: Don't iterate over the whole `unifier_deg_vec` if a "small
/// unifier" (a unifier with degree less or equal to the degree of the
/// formula) has been found. Instead stop iteration early.
fn find_modal_degree_counterexamples() {
    let unifier_max_degree = 3;
    let mut unifier_iter = FineFormIter::new(0);

    // Shall contain all variable free formulae in normal form, indexed by degree.
    // I.e. in `unifier_vec[i]` there are precisely the variable-free
    // formulae of degree `i` in normal form up to equivalence.
    let unifier_vec: Vec<Vec<NNF>> = Vec::with_capacity(unifier_max_degree);

    let mut formula_iter = FineFormIter::new(1);

    let mut curr_level: usize = 0;

    while curr_level <= unifier_max_degree {
        unifier_vec.push(Vec::new());
        // Fill in the next level of unifiers into `unifier_vec`
        while let Some(unif) = unifier_iter.next_curr_level() {
            unifier_vec[curr_level].push(unif);
        }

        // for each formula of the current level...
        while let Some(formula) = formula_iter.next_curr_level() {
            //
        }

        // prepare for the next level
        unifier_iter.prepare_next_level();
        formula_iter.prepare_next_level();
        curr_level += 1;
    }

    let mut unifier_deg_vec = Vec::with_capacity(unifier_vec.len());
    for unif in unifier_vec.into_iter() {
        let degree = unif.degree();
        unifier_deg_vec.push((unif, degree));
    }
    println!("len: {}", unifier_deg_vec.len());

    for (i, formula) in fineform_correct::FineFormIter::new(1).enumerate() {
        //let mut minimal_unifier_degree: Mutex<Option<(usize, &NNF)>> = Mutex::new(None);

        fn min_unifier<'a>(
            acc: Option<&'a (NNF, usize)>,
            unif_deg: &'a (NNF, usize),
        ) -> Option<&'a (NNF, usize)> {
            let (_, degree) = unif_deg;

            match acc {
                None => Some(unif_deg),
                Some((_, deg)) => {
                    if deg > degree {
                        Some(unif_deg)
                    } else {
                        acc
                    }
                }
            }
        }

        fn min_unifier2<'a>(
            acc: Option<&'a (NNF, usize)>,
            unif_deg: Option<&'a (NNF, usize)>,
        ) -> Option<&'a (NNF, usize)> {
            match unif_deg {
                None => acc,
                Some(unif_deg) => min_unifier(acc, unif_deg),
            }
        }

        let minimal_unifier_degree = unifier_deg_vec
            .par_iter()
            .filter(|(unifier, _)| formula.substitute_all(unifier).is_valid())
            .fold(|| None, min_unifier)
            .reduce(|| None, min_unifier2);

        match minimal_unifier_degree {
            None => {}
            Some((unif, degree)) => {
                if degree > &formula.degree() {
                    println!(
                        "\nFound counterexample {}, index: {}, unif: {}",
                        formula.display_beautiful(),
                        i,
                        unif.display_beautiful()
                    );
                }
            }
        }

        //if i % 100 == 0 {
        print!("{} ", i);
        //}
        if formula.degree() > unifier_max_degree {
            return;
        }
    }
}
*/

fn find_random_non_decidables() {
    use proptest::prelude::*;
    use proptest::strategy::*;
    use proptest::test_runner::*;

    let mut runner = TestRunner::default();

    fn increment(map: &mut BTreeMap<usize, usize>, index: usize) {
        match map.get(&index) {
            None => map.insert(index, 1),
            Some(val) => map.insert(index, val + 1),
        };
    }

    // write down how many decidables of which degree there are
    let mut decidables: BTreeMap<usize, usize> = BTreeMap::new();
    const MAX_LOOPS: usize = 50_000;

    for _ in 0..MAX_LOOPS {
        let nnf_val = arb_nnf_var(1).new_tree(&mut runner).unwrap();
        let deg = nnf_val.current().degree();

        match nnf_val.current().simpl().check_unifiable() {
            #[allow(unused_variables)]
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
                increment(&mut decidables, deg);
            }
            Err(clause_set_irred) => {
                println!("{}", clause_set_irred.display_beautiful());
            }
        }
    }
    println!("loops {}, dec {:?}", MAX_LOOPS, decidables);
}

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
                //return;
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

#[allow(unreachable_code)]
fn main() {
    rayon::ThreadPoolBuilder::new()
        .num_threads(16)
        .build_global()
        .unwrap();

    //find_modal_degree_counterexamples();

    #[allow(unused_variables)]
    #[allow(unused_mut)]
    let mut ff_iter = fineform_correct::FineFormIter::new(1);

    find_random_non_decidables();
    /*
    find_non_decidables(ff_iter);
    return;
    */

    //find_random_non_decidables();
    //find_non_decidables(ff_iter);
}
