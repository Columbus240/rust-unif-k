#![feature(once_cell)]
#![feature(btree_drain_filter)]
#![feature(map_first_last)]

#[allow(unused_imports)]
use std::collections::btree_map::BTreeMap;
#[allow(unused_imports)]
use std::collections::btree_set::BTreeSet;

#[allow(unused_imports)]
use rayon::prelude::*;

#[macro_use]
extern crate lalrpop_util;

lalrpop_mod!(#[allow(clippy::all)] pub nnf_parser, "/src/nnf_parser.rs");

mod decider;
mod fineform_correct;
//mod lazy_decider;
//mod lazy_nnf;
mod nnf;
mod powerset;

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

#[allow(dead_code)]
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
    const MAX_LOOPS: usize = 5_000_000;
    const NUM_VARIABLES: NnfAtom = 1;
    const SIMPLIFY_FORMULAE: bool = true;

    for i in 0..MAX_LOOPS {
        if i > 0 && (i % 100 == 0) {
            println!("{}", i);
        }
        let nnf_val = arb_nnf_var(NUM_VARIABLES).new_tree(&mut runner).unwrap();

        let nnf = if SIMPLIFY_FORMULAE {
            nnf_val.current().simpl()
        } else {
            nnf_val.current()
        };
        let deg = nnf.degree();

        match nnf.check_unifiable() {
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

#[allow(dead_code)]
fn find_non_decidables(num_variables: u8) {
    let mut ff_iter = FineFormIter::new(num_variables);
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

    let mut iter = FineFormIter::new(1).enumerate().skip(1650);
    for (i, nnf) in iter {
        println!("{} {}", i, nnf.display_beautiful());
    }

    /*
    let mut i = 0;
    loop {
        let nnf = nnf::rnd_cnf_box_m(
            3,
            1,
            4,
            3,
            vec![vec![vec![1, 0]], vec![vec![1, 2, 0]]],
            vec![vec![1, 1, 1]],
        )
        .unwrap();
        assert_eq!(nnf.is_valid(), nnf.is_valid_new());
        println!("{}", i);
        i += 1;
    }*/

    'a: for (i, nnf) in FineFormIter::new(1).enumerate() {
        let nnf_simpl = nnf.simpl();
        if let Ok(b) = nnf_simpl.clone().check_unifiable() {
            if !b {
                println!("index {}, nonunif", i);
                continue 'a;
            }
            let deg = nnf_simpl.degree();
            let mut unif_iter = fineform_correct::FineFormIter::new(0);
            while unif_iter.get_curr_level() <= deg {
                let subst = nnf_simpl.clone().substitute_all(&unif_iter.next().unwrap());
                if subst.is_valid() {
                    println!("index {}, unif ok", i);
                    continue 'a;
                }
            }
            panic!("index {}, formula {}", i, nnf_simpl.display_beautiful());
        } else {
            println!("index {}, non-dec", i);
        }
    }

    /*
    let formula = NNF::impli(NNF::NnfBox(Box::new(NNF::AtomPos(0))), NNF::AtomPos(0));
    println!("{}", formula.display_beautiful());

    for (i, nnf) in FineFormIter::new(0).enumerate() {
        if formula.substitute_all(&nnf).is_valid_new2() {
            println!("{}", nnf.simpl_slow().display_beautiful());
        }
        if i > 1000 {
            return;
        }
    }
    // old algorithm: real 9.682s, user: 54.089s
    // old algorithm: real 7.847s, user: 48.421s
    // new algorithm: real 5.237s, user: 26.716s
    // new algorithm: real 5.170s, user: 27.617s
    return;

    let formula = nnf_parser::LiteralParser::new()
        .parse("((0&[](0&~0))|(~0&<>~0&[]~0)|(~0&<>0&[]0)|(~0&<>~0&<>0))")
        .unwrap();
    let formula_simpl = formula.clone().simpl_slow();
    println!(
        "{} to {}",
        formula.display_beautiful(),
        formula_simpl.display_beautiful()
    );

    let formula_simpl_unif = formula_simpl.check_unifiable().expect_err("WTF");
    assert!(formula_simpl_unif.irreducibles.is_empty());
    assert!(formula_simpl_unif.waiting_atoms.is_empty());
    assert!(formula_simpl_unif.waiting_conj_disj.is_empty());
    assert_eq!(formula_simpl_unif.cut_clauses.len(), 1);

    let clause = formula_simpl_unif.cut_clauses.into_iter().next().unwrap();
    let clause = ClauseIrred {
        irreducibles: clause.irreducibles,
    };
    println!("irred: {}", clause.display_beautiful());

    return;
    */

    let mut decidable: usize = 0;
    let mut undecidable: usize = 0;
    for (i, nnf) in FineFormIter::new(1).enumerate() {
        let nnf_simpl = nnf.clone().simpl_slow();
        let nnf_unif = nnf.clone().check_unifiable();
        let nnf_simpl_unif = nnf_simpl.check_unifiable();
        match (nnf_unif, nnf_simpl_unif) {
            (Ok(b0), Ok(b1)) => {
                decidable += 1;
                assert_eq!(b0, b1);
                println!("index {} unifiable: {}", i, b0);
            }
            (Err(e), Ok(b1)) => panic!("{} should be {}", e.display_beautiful(), b1),
            (_, Err(e)) => {
                undecidable += 1;
                println!("index {} gets stuck at:\n{}", i, e.display_beautiful())
            }
        }
        println!("stuck {} vs. dec {}", undecidable, decidable);
    }

    #[allow(dead_code)]
    fn check_unifiability_simpl(nnf: NNF) {
        let nnf_simpl = nnf.clone().simpl_slow();
        let nnf_unif = nnf.clone().check_unifiable();
        let nnf_simpl_unif = nnf_simpl.check_unifiable();
        match (nnf_unif, nnf_simpl_unif) {
            (Ok(b0), Ok(b1)) => assert_eq!(b0, b1),
            (Err(e), Ok(b1)) => panic!("{} should be {}", e.display_beautiful(), b1),
            (_, Err(e)) => println!(
                "{}\nparser: {}\n{}",
                nnf.display_beautiful(),
                nnf.display_parser(),
                e.display_beautiful()
            ),
        }
    }

    //find_modal_degree_counterexamples();

    //find_random_non_decidables();
    /*
    find_non_decidables(ff_iter);
    return;
    */

    //find_random_non_decidables();
    //find_non_decidables(ff_iter);
}
