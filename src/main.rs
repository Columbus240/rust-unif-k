#![feature(once_cell)]

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

fn main() {
    rayon::ThreadPoolBuilder::new()
        .num_threads(16)
        .build_global()
        .unwrap();

    for i in fineform_correct::PowersetIter::new(20).step_by(0xFFFF) {
        println!("{:?}", i);
    }

    let literals = {
        let base0 = BTreeMap::new();
        let mut base1 = BTreeMap::new();
        let mut base2 = BTreeMap::new();
        let mut base3 = BTreeMap::new();
        let mut base4 = BTreeMap::new();
        let mut base5 = BTreeMap::new();
        let mut base6 = BTreeMap::new();
        let mut base7 = BTreeMap::new();
        let mut base8 = BTreeMap::new();
        base1.insert(0, true);
        base2.insert(0, false);
        base3.insert(1, true);
        base4.insert(1, false);
        base5.insert(0, true);
        base5.insert(1, true);
        base6.insert(0, false);
        base6.insert(1, false);
        base7.insert(0, true);
        base7.insert(1, false);
        base8.insert(0, false);
        base8.insert(1, true);
        vec![base0, base1, base2, base3, base4, base5, base6, base7, base8]
    };

    /*
    let unifiers = fineform::enumerate_unifiers(1);

    /*
    unifiers
        .into_iter()
        .map(|(ff, nnf)| {
            let string = print_formula_beautiful(&nnf);
            println!("{}", string);
        })
        .for_each(drop);
    */

    let formulae = fineform::enumerate_formulae(literals.into_iter(), 1);

    formulae
        .into_iter()
        .map(|(ff, nnf)| {
	    println!("{}", nnf.display_beautiful());
        })
        .for_each(drop);

    /*
    let mut i = 0;
    let len = formulae.len();

    for (_, nnf) in formulae.into_iter() {
        println!("\\section{{${}$}}", nnf.display_latex());
        for (_, unif) in unifiers.iter() {
            if nnf.substitute(unif).is_valid() {
                println!("${}$ \\\\", unif.display_latex());
            }
        }
        i += 1;
    }
    */
    */
}
