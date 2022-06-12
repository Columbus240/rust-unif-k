use std::collections::btree_map::BTreeMap;
use std::collections::btree_set::BTreeSet;

use rayon::prelude::*;

use crate::lazy_nnf::*;
use crate::nnf::NNF;

#[derive(Clone)]
enum LeftRight {
    Left,
    Right,
}

// Its possible to replace `la` and `ra` by a single
// `BTreeMap<usize, bool>`, where true/false stand for left/right or similar.
// (use an enum, to simplify remembering the right thing)
// This way (using `try_insert`) its easier to check whether a sequent is valid.
struct PSW {
    // atoms (left or right)
    atoms: BTreeMap<usize, LeftRight>,

    // left boxes
    lb: BTreeSet<LazyNNF>,
    // right boxes
    rb: BTreeSet<LazyNNF>,

    // left disjunctions
    ld: Vec<BTreeSet<LazyNNF>>,
    // right conjunctions
    rc: Vec<BTreeSet<LazyNNF>>,

    // left waiting
    lw: BTreeSet<LazyNNF>,
    // right waiting
    rw: BTreeSet<LazyNNF>,
}

struct PS {
    // atoms (left or right)
    atoms: BTreeMap<usize, LeftRight>,

    // left boxes
    lb: BTreeSet<NNF>,
    // right boxes
    rb: BTreeSet<NNF>,

    // left disjunctions
    ld: Vec<BTreeSet<NNF>>,
    // right conjunctions
    rc: Vec<BTreeSet<NNF>>,
}

struct PSI {
    // left boxes
    lb: BTreeSet<NNF>,
    // right boxes
    rb: BTreeSet<NNF>,
}

enum PSWstepResult {
    Waiting(PSW),
    Next(PS),
    Valid,
}

impl LazyNNF {
    pub fn is_valid(self) -> bool {
        PSW::from_lazynnf(self).is_valid()
    }

    pub fn equiv_dec(phi: &NNF, psi: &NNF) -> bool {
        let mut conj = BTreeSet::new();
        let phi0 = phi; //.simpl();
        let psi0 = psi; //.simpl();
        conj.insert(NNF::impli(&phi0, &psi0));
        conj.insert(NNF::impli(&psi0, &phi0));
        NNF::is_valid(&NNF::And(conj).simpl())
    }
}

impl PSW {
    fn from_lazynnf(phi: LazyNNF) -> PSW {
        let mut rw = BTreeSet::new();
        rw.insert(phi);
        PSW {
            atoms: BTreeMap::new(),
            lb: BTreeSet::new(),
            rb: BTreeSet::new(),
            ld: Vec::new(),
            rc: Vec::new(),
            lw: BTreeSet::new(),
            rw,
        }
    }

    fn step(mut self) -> PSWstepResult {
        let mut new_left_waiting = BTreeSet::new();
        for left_waiting in self.lw.into_iter() {
            match left_waiting.formula {
                LazyNNFFormula::AtomPos(i) => {
                    if left_waiting.negated {
                        match self.atoms.insert(i, LeftRight::Right) {
                            Some(LeftRight::Left) => return PSWstepResult::Valid,
                            _ => {}
                        }
                    } else {
                        match self.atoms.insert(i, LeftRight::Left) {
                            Some(LeftRight::Right) => return PSWstepResult::Valid,
                            _ => {}
                        }
                    }
                }
                LazyNNFFormula::AtomNeg(i) => {
                    if left_waiting.negated {
                        match self.atoms.insert(i, LeftRight::Left) {
                            Some(LeftRight::Right) => return PSWstepResult::Valid,
                            _ => {}
                        }
                    } else {
                        match self.atoms.insert(i, LeftRight::Right) {
                            Some(LeftRight::Left) => return PSWstepResult::Valid,
                            _ => {}
                        }
                    }
                },
                LazyNNFFormula::Bot => {
		    if left_waiting.negated {
			// do nothing
		    } else {
			return PSWstepResult::Valid;
		    }
                }
                LazyNNFFormula::Top => {
		    if left_waiting.negated {
			return PSWstepResult::Valid;
		    } else {
			// do nothing
		    }
                }
                LazyNNFFormula::And(mut conjuncts) => {
		    if left_waiting.negated {
			conjuncts.ma
		    } else {
			new_left_waiting.append(&mut conjuncts);
		    }
                }
                NNF::Or(disjuncts) => {
                    self.ld.push(disjuncts);
                }
                NNF::NnfBox(phi) => {
                    self.lb.insert(*phi);
                }
                NNF::NnfDia(phi) => {
                    self.rb.insert(phi.neg());
                }
            }
        }

        let mut new_right_waiting = BTreeSet::new();
        for right_waiting in self.rw.into_iter() {
            match right_waiting {
                NNF::AtomPos(i) => match self.atoms.insert(i, LeftRight::Right) {
                    Some(LeftRight::Left) => return PSWstepResult::Valid,
                    _ => {}
                },
                NNF::AtomNeg(i) => match self.atoms.insert(i, LeftRight::Left) {
                    Some(LeftRight::Right) => return PSWstepResult::Valid,
                    _ => {}
                },
                NNF::Bot => {
                    // do nothing
                }
                NNF::Top => {
                    return PSWstepResult::Valid;
                }
                NNF::And(conjuncts) => {
                    self.rc.push(conjuncts);
                }
                NNF::Or(mut disjuncts) => {
                    new_right_waiting.append(&mut disjuncts);
                }
                NNF::NnfBox(phi) => {
                    self.rb.insert(*phi);
                }
                NNF::NnfDia(phi) => {
                    self.lb.insert(phi.neg());
                }
            }
        }

        if new_left_waiting.is_empty() && new_right_waiting.is_empty() {
            return PSWstepResult::Next(PS {
                atoms: self.atoms,
                lb: self.lb,
                rb: self.rb,
                ld: self.ld,
                rc: self.rc,
            });
        }
        self.lw = new_left_waiting;
        self.rw = new_right_waiting;
        PSWstepResult::Waiting(self)
    }

    fn to_ps(self) -> Option<PS> {
        match self.step() {
            PSWstepResult::Valid => None,
            PSWstepResult::Waiting(next) => next.to_ps(),
            PSWstepResult::Next(ps) => Some(ps),
        }
    }
}

enum PSstepResult {
    Waiting(Vec<PSW>),
    Next(PSI),
}

impl PS {
    fn step(mut self) -> PSstepResult {
        if let Some(disjuncts) = self.ld.pop() {
            let mut new_psw = Vec::with_capacity(disjuncts.len());
            for disj in disjuncts.into_iter() {
                let mut lw_new = BTreeSet::new();
                lw_new.insert(disj);
                new_psw.push(PSW {
                    atoms: self.atoms.clone(),
                    lb: self.lb.clone(),
                    rb: self.rb.clone(),
                    ld: self.ld.clone(),
                    rc: self.rc.clone(),
                    lw: lw_new,
                    rw: BTreeSet::new(),
                });
            }
            return PSstepResult::Waiting(new_psw);
        }
        if let Some(conjuncts) = self.rc.pop() {
            let mut new_psw = Vec::with_capacity(conjuncts.len());
            for conj in conjuncts.into_iter() {
                let mut rw_new = BTreeSet::new();
                rw_new.insert(conj);
                new_psw.push(PSW {
                    atoms: self.atoms.clone(),
                    lb: self.lb.clone(),
                    rb: self.rb.clone(),
                    ld: self.ld.clone(),
                    rc: self.rc.clone(),
                    lw: BTreeSet::new(),
                    rw: rw_new,
                });
            }
            return PSstepResult::Waiting(new_psw);
        }
        return PSstepResult::Next(PSI {
            lb: self.lb,
            rb: self.rb,
        });
    }

    fn to_psi(self) -> Vec<PSI> {
        match self.step() {
            PSstepResult::Waiting(psw_vec) => {
                let mut output = Vec::with_capacity(psw_vec.len());
                for psw in psw_vec {
                    if let Some(ps) = psw.to_ps() {
                        output.append(&mut ps.to_psi());
                    }
                }
                return output;
            }
            PSstepResult::Next(psi) => vec![psi],
        }
    }
}

impl PSI {
    // returns an empty list, if the formula is contradictory
    fn step(self) -> Vec<PSW> {
        let mut output = Vec::with_capacity(self.rb.len());
        for rb in self.rb.into_iter() {
            let mut new_rw = BTreeSet::new();
            new_rw.insert(rb);
            output.push(PSW {
                atoms: BTreeMap::new(),
                lb: BTreeSet::new(),
                rb: BTreeSet::new(),
                ld: Vec::new(),
                rc: Vec::new(),
                lw: self.lb.clone(),
                rw: new_rw,
            });
        }
        return output;
    }
}

impl PSW {
    fn is_valid(self) -> bool {
        match self.to_ps() {
            None => true,
            Some(ps) => ps.is_valid(),
        }
    }
}

impl PS {
    fn is_valid(self) -> bool {
        self.to_psi()
            //.into_par_iter()
            .into_iter()
            //.map(|psi| psi.is_valid())
            .fold(true, |acc, psi| acc && psi.is_valid())
        //            .reduce(|| true, |a, b| a && b)
    }
}

impl PSI {
    fn is_valid(self) -> bool {
        self.step()
            //.into_par_iter()
            .into_iter()
            //.map(|psi| psi.is_valid())
            .fold(false, |acc, psw| acc || psw.is_valid())
        //           .reduce(|| false, |a, b| a || b)
    }
}
