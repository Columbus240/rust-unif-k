#![feature(once_cell)]

#[allow(unused_imports)]
use std::collections::btree_map::BTreeMap;
#[allow(unused_imports)]
use std::collections::btree_set::BTreeSet;

mod decider;
mod fineform;
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

    /*
    let mut bb = BTreeSet::new();
    bb.insert(FineForm::Top.dia());
    bb.insert(FineForm::Node(Box::new(FFNode {
        atoms: BTreeMap::new(),
        dia_branch: Some(FineForm::Top.dia()),
        box_branches: {
            let mut bb = BTreeSet::new();
            bb.insert(FineForm::Top);
            bb
        },
    })));
    let a = FineForm::Node(Box::new(FFNode {
    atoms: BTreeMap::new(),
    dia_branch: None,
    box_branches: bb,
    }));
    println!("a: {}", print_formula_beautiful(&a.to_nnf().simpl_slow()));
    assert_eq!(FineForm::box_n_bot(0), FineForm::bot());
    assert_eq!(FineForm::box_n_bot(1), FineForm::box_bot());
    let b2 = FineForm::box_n_bot(2).to_nnf().simpl_slow();
    let b3 = FineForm::box_n_bot(3).to_nnf().simpl_slow();
    println!("b2: {:?}, {}", print_formula_beautiful(&b2), NNF::equiv_dec(a.to_nnf(), b2.clone()));
    println!("b3: {:?}, {}", print_formula_beautiful(&b3), NNF::equiv_dec(a.to_nnf(), b3.clone()));

    let bbb = NNF::Bot.boxx().boxx();
    let bbbb = bbb.clone().boxx();
    let bdt = NNF::Top.dia().boxx();

    let c = NNF::or( bbb.clone(), NNF::and( bbbb.clone(), bdt.clone() ) );
    println!("c: {:?}, {}", print_formula_beautiful(&c), NNF::equiv_dec(a.to_nnf(), c));
    let d = NNF::and( NNF::or( bbb.clone(), bbbb.clone() ), NNF::or( bbb.clone(), bdt.clone() ) ).simpl_slow();
    println!("d: {:?}, {}", print_formula_beautiful(&d), NNF::equiv_dec(a.to_nnf(), d));
    let e = NNF::and( bbbb.clone(), NNF::or( bbb.clone(), bdt.clone() ) ).simpl_slow();
    println!("e: {:?}, {}", print_formula_beautiful(&e), NNF::equiv_dec(a.to_nnf(), e));
    let f = NNF::or( NNF::and( bbbb.clone(), bbb.clone() ), NNF::and( bbbb.clone(), bdt.clone() ) ).simpl_slow();
    println!("f: {:?}, {}", print_formula_beautiful(&f), NNF::equiv_dec(a.to_nnf(), f));
    let g = NNF::or( bbb.clone(), NNF::and( bbbb.clone(), bdt.clone() ) ).simpl_slow();
    println!("g: {:?}, {}", print_formula_beautiful(&g), NNF::equiv_dec(a.to_nnf(), g));
    */

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
