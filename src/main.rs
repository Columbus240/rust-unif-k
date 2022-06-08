use rayon::prelude::*;
use std::collections::btree_set::BTreeSet;
use std::sync::Arc;
use std::sync::Mutex;

mod decider;
mod fineform;
mod nnf;

use nnf::*;

fn generate_formulae<'a>(mut input: BTreeSet<Arc<NNF>>, steps: usize) -> BTreeSet<Arc<NNF>> {
    if steps == 0 {
        return input;
    }

    let new_set_mutex: Arc<Mutex<BTreeSet<Arc<NNF>>>> = Arc::new(Mutex::new(BTreeSet::new()));

    input
        .par_iter()
        .map(|x: &Arc<NNF>| {
            let mut thread_local_set: BTreeSet<Arc<NNF>> = BTreeSet::new();

            {
                // if `x` is top or a conjunction, then don't add a box.
                match **x {
                    NNF::Top | NNF::And(_) => {}
                    _ => {
                        let boxed = Arc::new(NNF::NnfBox(x.clone()));
                        thread_local_set.insert(boxed);
                    }
                }

                // if `x` is bottom or a disjunction, then don't add a diamond
                match **x {
                    NNF::Bot | NNF::Or(_) => {}
                    _ => {
                        let diamond = Arc::new(NNF::NnfDia(x.clone()));
                        thread_local_set.insert(diamond);
                    }
                }
            }

            for y in &input {
                //		input.par_iter().map(|y : &Arc<NNF> | {
                // if `x` or `y` is top or bottom, then don't perform
                // the join/meet. Or if `x` and `y` are the same or
                // negations of eachother.
                if **x >= **y
                    || **x == y.neg()
                    || **x == NNF::Bot
                    || **x == NNF::Top
                    || **y == NNF::Bot
                    || **y == NNF::Top
                {
                    continue;
                }

                // Generate the meet
                let meet: Option<NNF> = {
                    let xnnf: &NNF = x;
                    let ynnf: &NNF = y;
                    match (xnnf, ynnf) {
                        (NNF::And(ref xx), NNF::And(ref yy)) => {
                            if xx.is_disjoint(&yy) {
                                Some(NNF::And(xx.union(&yy).cloned().collect()))
                            } else {
                                None
                            }
                        }
                        (NNF::And(ref xx), _) => Some(NNF::And({
                            let mut newx = xx.clone();
                            newx.insert(y.clone());
                            newx
                        })),
                        (_, NNF::And(ref yy)) => Some(NNF::And({
                            let mut newy = yy.clone();
                            newy.insert(x.clone());
                            newy
                        })),
                        (_, _) => Some(NNF::And({
                            let mut s: BTreeSet<Arc<NNF>> = BTreeSet::new();
                            s.insert(x.clone());
                            s.insert(y.clone());
                            s
                        })),
                    }
                };

                // Generate the join
                let join: Option<NNF> = {
                    let xnnf: &NNF = x;
                    let ynnf: &NNF = y;
                    match (xnnf, ynnf) {
                        (NNF::Or(ref xx), NNF::Or(ref yy)) => {
                            if xx.is_disjoint(&yy) {
                                Some(NNF::Or(xx.union(&yy).cloned().collect()))
                            } else {
                                None
                            }
                        }
                        (NNF::Or(ref xx), _) => Some(NNF::Or({
                            let mut newx = xx.clone();
                            newx.insert(y.clone());
                            newx
                        })),
                        (_, NNF::Or(ref yy)) => Some(NNF::Or({
                            let mut newy = yy.clone();
                            newy.insert(x.clone());
                            newy
                        })),
                        (_, _) => Some(NNF::Or({
                            let mut s: BTreeSet<Arc<NNF>> = BTreeSet::new();
                            s.insert(x.clone());
                            s.insert(y.clone());
                            s
                        })),
                    }
                };

                meet.map(|m| thread_local_set.insert(Arc::new(m)));
                join.map(|j| thread_local_set.insert(Arc::new(j)));
            }
            // acquire the lock
            let mut new_set = new_set_mutex.lock().unwrap();
            new_set.extend(thread_local_set.into_iter());
            let l = new_set.len();
            if l % 10000 == 0 {
                println!("current size of new_set: {}", new_set.len());
            }
        })
        .for_each(drop);

    let new_set: BTreeSet<_> = Arc::try_unwrap(new_set_mutex)
        .unwrap()
        .into_inner()
        .unwrap();

    input.extend(new_set.into_iter());

    generate_formulae(input, steps - 1)
}

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
    let bot = Arc::new(NNF::Bot);
    let top = Arc::new(NNF::Top);

    let mut variable = BTreeSet::new();
    variable.insert(Arc::new(NNF::AtomPos(0)));
    variable.insert(Arc::new(NNF::AtomNeg(0)));
    #[allow(unused_variables)]
    let variables = generate_formulae(variable, 3);

    let mut constant = BTreeSet::new();
    constant.insert(bot.clone());
    constant.insert(top.clone());
    #[allow(unused_variables)]
    let constants = generate_formulae(constant, 3);

    let f = fineform::enumerate_formulae(2);
    f.iter()
        .map(|ff| println!("{}", print_formula_beautiful(&ff.to_nnf().simpl())))
        .for_each(drop);
}
