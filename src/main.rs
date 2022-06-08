use rayon::prelude::*;
use std::collections::btree_set::BTreeSet;
use std::sync::Arc;
use std::sync::Mutex;

mod decider;
mod fineform;
mod nnf;

use nnf::*;

fn print_formula_beautiful(phi: &NNF) -> String {
    match phi {
        NNF::Top => "⊤".to_owned(),
        NNF::Bot => "⊥".to_owned(),
        NNF::AtomPos(_) => "p".to_owned(),
        NNF::AtomNeg(_) => "¬p".to_owned(),
        NNF::And(s) => {
            "(".to_owned()
                + &({
                    let mut set_iter = s.iter();
                    let first = set_iter.next();
                    first.map_or("".to_owned(), |f| print_formula_beautiful(f))
                        + &set_iter
                            .map(|x| print_formula_beautiful(x))
                            .fold(String::new(), |acc: String, x| acc + "∧" + &x)
                })
                + ")"
        }
        NNF::Or(s) => {
            "(".to_owned()
                + &({
                    let mut set_iter = s.iter();
                    let first = set_iter.next();
                    first.map_or("".to_owned(), |f| print_formula_beautiful(f))
                        + &set_iter
                            .map(|x| print_formula_beautiful(x))
                            .fold(String::new(), |acc: String, x| acc + "∨" + &x)
                })
                + ")"
        }
        NNF::NnfBox(phi0) => "(□".to_owned() + &print_formula_beautiful(phi0) + ")",
        NNF::NnfDia(phi0) => "(◇".to_owned() + &print_formula_beautiful(phi0) + ")",
    }
}

fn print_formula(phi: &NNF) -> String {
    match phi {
        NNF::Top => "1".to_owned(),
        NNF::Bot => "0".to_owned(),
        NNF::AtomPos(_) => "p0".to_owned(),
        NNF::AtomNeg(_) => "~p0".to_owned(),
        NNF::And(s) => {
            "(".to_owned()
                + &({
                    let mut set_iter = s.iter();
                    let first = set_iter.next();
                    first.map_or("".to_owned(), |f| print_formula(f))
                        + &set_iter
                            .map(|x| print_formula(x))
                            .fold(String::new(), |acc: String, x| acc + "&" + &x)
                })
                + ")"
        }
        NNF::Or(s) => {
            "(".to_owned()
                + &({
                    let mut set_iter = s.iter();
                    let first = set_iter.next();
                    first.map_or("".to_owned(), |f| print_formula(f))
                        + &set_iter
                            .map(|x| print_formula(x))
                            .fold(String::new(), |acc: String, x| acc + "|" + &x)
                })
                + ")"
        }
        NNF::NnfBox(phi0) => "([a]".to_owned() + &print_formula(phi0) + ")",
        NNF::NnfDia(phi0) => "(<a>".to_owned() + &print_formula(phi0) + ")",
    }
}

fn main() {
    let f = fineform::enumerate_formulae(2);
    f.iter()
        .map(|ff| println!("{}", print_formula_beautiful(&ff.to_nnf().simpl())))
        .for_each(drop);
}
