use rayon::prelude::*;
use std::collections::btree_set::BTreeSet;
use std::fs::File;
use std::io::prelude::*;
use std::sync::Arc;
use std::sync::Mutex;

#[derive(Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
enum NNF {
    AtomPos(usize),
    AtomNeg(usize),
    Bot,
    Top,
    And(BTreeSet<Arc<NNF>>),
    Or(BTreeSet<Arc<NNF>>),
    NnfBox(Arc<NNF>),
    NnfDia(Arc<NNF>),
}

impl NNF {
    fn neg(&self) -> NNF {
        match self {
            NNF::AtomPos(i) => NNF::AtomNeg(*i),
            NNF::AtomNeg(i) => NNF::AtomPos(*i),
            NNF::Bot => NNF::Top,
            NNF::Top => NNF::Bot,
            NNF::And(a) => NNF::Or(a.iter().clone().map(|x| Arc::new(x.neg())).collect()),
            NNF::Or(a) => NNF::And(a.iter().clone().map(|x| Arc::new(x.neg())).collect()),
            NNF::NnfBox(a) => NNF::NnfDia(Arc::new(a.neg())),
            NNF::NnfDia(a) => NNF::NnfBox(Arc::new(a.neg())),
        }
    }
}

// We check, whether some simplifications would appear, if `phi` would
// be added to `set` and we take the conjunction over `set`.
// We assume that `set` is already simplified.
fn check_for_simplification_conj (phi : &NNF, set : &BTreeSet<Arc<NNF>>) -> bool {
	// If `phi` is implied by `/\ set`, nothing happens if we add it.
	// If `phi` implies any formula in `set`, it would create a new
	// simplification.
}

enum NfBaseAtomsIterState {
    // First return the whole previous level
    Empty(Box<NfBaseAtomsIter>),
    // Then `p` is returned at the end of the previous level.
    // But in state `PosNegVar` return `~p`.
    PosNegVar,
    // Now return the whole previous level, but with `p` added each time
    Pos(Box<NfBaseAtomsIter>),
    // Now return the whole previous level, but with `~p` added each time
    Neg(Box<NfBaseAtomsIter>),
    // Now we're done and won't return anything anymore.
    Done,
}

struct NfBaseAtomsIter {
    // the variable that is added by this level
    curr_var: usize,
    curr_state: NfBaseAtomsIterState,
}

impl NfBaseAtomsIter {
    fn new(num_vars: usize) -> NfBaseAtomsIter {
        if num_vars == 0 {
            return NfBaseAtomsIter {
                curr_var: 0,
                curr_state: NfBaseAtomsIterState::Done,
            };
        }
        let prev_level = NfBaseAtomsIter::new(num_vars - 1);
        NfBaseAtomsIter {
            curr_var: num_vars - 1,
            curr_state: NfBaseAtomsIterState::Empty(Box::new(prev_level)),
        }
    }
}

impl Iterator for NfBaseAtomsIter {
    type Item = Vec<(bool, usize)>;

    fn next(&mut self) -> Option<Vec<(bool, usize)>> {
        match &mut self.curr_state {
            NfBaseAtomsIterState::Empty(prev_level) => match prev_level.next() {
                Some(v) => Some(v),
                None => {
                    // We're done with the previous
                    // level, begin the next phase
                    self.curr_state = NfBaseAtomsIterState::PosNegVar;
                    return Some(vec![(true, self.curr_var)]);
                }
            },
            NfBaseAtomsIterState::PosNegVar => {
                self.curr_state =
                    NfBaseAtomsIterState::Pos(Box::new(NfBaseAtomsIter::new(self.curr_var)));
                return Some(vec![(false, self.curr_var)]);
            }
            NfBaseAtomsIterState::Pos(prev_level) => {
                match prev_level.next() {
                    Some(mut v) => {
                        v.push((true, self.curr_var));
                        return Some(v);
                    }
                    None => {
                        // We're done with this level,
                        // begin the next phase
                        self.curr_state = NfBaseAtomsIterState::Neg(Box::new(
                            NfBaseAtomsIter::new(self.curr_var),
                        ));
                        return self.next();
                    }
                }
            }
            NfBaseAtomsIterState::Neg(prev_level) => {
                match prev_level.next() {
                    Some(mut v) => {
                        v.push((false, self.curr_var));
                        return Some(v);
                    }
                    None => {
                        // We're done with this level,
                        // begin the next phase
                        self.curr_state = NfBaseAtomsIterState::Done;
                        return None;
                    }
                }
            }
            NfBaseAtomsIterState::Done => None,
        }
    }
}

#[derive(Debug)]
struct NfFormula {
	atomar : Vec<(bool, usize)>,
	next_level : Vec<(bool, Box<NfFormula>)>,
}

enum GenerateNfLevelIterState {
	// First output all base formulae
	BaseFormulae(NfBaseAtomsIter),

	// Then do what?
	// Problem: How many conjuncts do we need & when do we know when to
	// stop?

	Done,
}

struct GenerateNfLevelIter {
	num_vars : usize,
	curr_level : usize,

	state : GenerateNfLevelIterState,
}

impl GenerateNfLevelIter {
	fn new(num_vars : usize, level : usize) -> GenerateNfLevelIter {
		GenerateNfLevelIter {
			num_vars : num_vars,
			curr_level : level,

			state: GenerateNfLevelIterState::BaseFormulae(NfBaseAtomsIter::new(num_vars)),
		}
	}
}

impl Iterator for GenerateNfLevelIter {
	type Item = NfFormula;

	fn next(&mut self) -> Option<NfFormula> {
		match &mut self.state {
			GenerateNfLevelIterState::BaseFormulae(i) => {
				match i.next() {
					Some(v) => {
						Some(NfFormula {
							atomar: v,
							next_level: Vec::new(),
						})
					},
					None => {
						// Then do what?
						self.state = GenerateNfLevelIterState::Done;
						None
					}
				}
			},
			GenerateNfLevelIterState::Done => None,
		}
	}
}

/*
fn generate_nf_level(atoms_vec : &Vec<Arc<NNF>>, level : usize) -> Vec<Arc<NNF>> {
    if level == 0 {
        return atoms_vec;
    }

    let prev_level = level-1;
}

fn generate_nf(num_vars : usize) -> Vec<Arc<NNF>> {
    let atoms_vec = generate_nf_base_atoms(num_vars);
}
*/

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

// substitutes each occurrence of a variable by the formula `sigma`
fn substitute(
    phi: &NNF,
    sigma: Arc<NNF>,
    sigma_neg: Arc<NNF>,
    top: Arc<NNF>,
    bot: Arc<NNF>,
) -> Arc<NNF> {
    match phi {
        NNF::Top => top,
        NNF::Bot => bot,
        NNF::AtomPos(_) => sigma,
        NNF::AtomNeg(_) => sigma_neg,
        NNF::And(s) => Arc::new(NNF::And(
            s.iter()
                .cloned()
                .map(|x| {
                    substitute(
                        &x,
                        sigma.clone(),
                        sigma_neg.clone(),
                        top.clone(),
                        bot.clone(),
                    )
                })
                .collect(),
        )),
        NNF::Or(s) => Arc::new(NNF::Or(
            s.iter()
                .cloned()
                .map(|x| {
                    substitute(
                        &x,
                        sigma.clone(),
                        sigma_neg.clone(),
                        top.clone(),
                        bot.clone(),
                    )
                })
                .collect(),
        )),
        NNF::NnfBox(phi0) => Arc::new(NNF::NnfBox(substitute(
            &phi0,
            sigma.clone(),
            sigma_neg.clone(),
            top.clone(),
            bot.clone(),
        ))),
        NNF::NnfDia(phi0) => Arc::new(NNF::NnfDia(substitute(
            &phi0,
            sigma.clone(),
            sigma_neg.clone(),
            top.clone(),
            bot.clone(),
        ))),
    }
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
	/*
	for p in GenerateNfLevelIter::new(5, 0) {
		println!("{:?}", p);
	}
	*/
    let bot = Arc::new(NNF::Bot);
    let top = Arc::new(NNF::Top);

    let mut variable = BTreeSet::new();
    variable.insert(Arc::new(NNF::AtomPos(0)));
    variable.insert(Arc::new(NNF::AtomNeg(0)));
    let variables = generate_formulae(variable, 3);

    let mut constant = BTreeSet::new();
    constant.insert(bot.clone());
    constant.insert(top.clone());
    let constants = generate_formulae(constant, 3);

    constants.iter().map(|f| println!("{}", print_formula_beautiful(f))).for_each(drop);

    /*
    let mut file_1 = File::create("unif_sv_3_4_1").unwrap();
    let mut file_2 = File::create("unif_sv_3_4_2").unwrap();
    let mut file_3 = File::create("unif_sv_3_4_3").unwrap();

    for c in constants {
        let c_neg = Arc::new(c.neg());
        for p in &variables {
            file_1.write_all(print_formula_beautiful(&p).as_bytes());
            file_1.write_all(b"\n");
            file_2.write_all(print_formula_beautiful(&c).as_bytes());
            file_2.write_all(b"\n");
            file_3.write_all(
              print_formula(
              &substitute(&p, c.clone(), c_neg.clone(), top.clone(), bot.clone())).as_bytes());
            file_3.write_all(b"\n");
        }
    }
    */
}
