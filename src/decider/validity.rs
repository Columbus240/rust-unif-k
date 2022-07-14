use std::collections::btree_map::BTreeMap;
use std::fs::OpenOptions;
use std::io::prelude::*;

#[allow(unused_imports)]
use rayon::prelude::*;

use crate::nnf::NNF;

#[derive(Clone)]
enum LeftRight {
    Left,
    Right,
}

#[allow(clippy::upper_case_acronyms)]
struct PSW {
    // atoms (left or right)
    atoms: BTreeMap<usize, LeftRight>,

    // left boxes
    lb: Vec<NNF>,
    // right boxes
    rb: Vec<NNF>,

    // left disjunctions
    ld: Vec<Vec<NNF>>,
    // right conjunctions
    rc: Vec<Vec<NNF>>,

    // left waiting
    lw: Vec<NNF>,
    // right waiting
    rw: Vec<NNF>,
}

struct PS {
    // atoms (left or right)
    atoms: BTreeMap<usize, LeftRight>,

    // left boxes
    lb: Vec<NNF>,
    // right boxes
    rb: Vec<NNF>,

    // left disjunctions
    ld: Vec<Vec<NNF>>,
    // right conjunctions
    rc: Vec<Vec<NNF>>,
}

#[allow(clippy::upper_case_acronyms)]
struct PSI {
    // left boxes
    lb: Vec<NNF>,
    // right boxes
    rb: Vec<NNF>,
}

enum PSWstepResult {
    Waiting(PSW),
    Next(PS),
    Valid,
}

impl NNF {
    pub fn is_valid(&self) -> bool {
        // short circuit
        match self {
            NNF::Bot | NNF::AtomPos(_) | NNF::AtomNeg(_) => {
                return false;
            }
            _ => {}
        }

        let result = PSW::from_nnf(self.clone()).compute_validity();
        if result {
            let mut file = OpenOptions::new()
                .create(true)
                .write(true)
                .append(true)
                .open("valid_formulae")
                .unwrap();
            writeln!(file, "{}", self.display_spartacus()).unwrap();
        } else {
            let mut file = OpenOptions::new()
                .create(true)
                .write(true)
                .append(true)
                .open("invalid_formulae")
                .unwrap();
            writeln!(file, "{}", self.display_spartacus()).unwrap();
        }

        result
    }

    pub fn equiv_dec(phi: &NNF, psi: &NNF) -> bool {
        if phi == psi {
            return true;
        }

        if *phi == NNF::Top {
            return NNF::is_valid(psi);
        }
        if *psi == NNF::Top {
            return NNF::is_valid(phi);
        }

        let mut conj = Vec::with_capacity(2);
        let phi0 = phi; //.simpl();
        let psi0 = psi; //.simpl();
        conj.push(NNF::impli(phi0.clone(), psi0.clone()));
        conj.push(NNF::impli(psi0.clone(), phi0.clone()));
        //        NNF::is_valid(NNF::And(conj).simpl())
        NNF::is_valid(&NNF::And(conj))
    }
}

impl PSW {
    fn from_nnf(phi: NNF) -> PSW {
        PSW {
            atoms: BTreeMap::new(),
            lb: Vec::new(),
            rb: Vec::new(),
            ld: Vec::new(),
            rc: Vec::new(),
            lw: Vec::new(),
            rw: vec![phi],
        }
    }

    fn step(mut self) -> PSWstepResult {
        let mut new_left_waiting = Vec::with_capacity(self.lw.len());
        for left_waiting in self.lw.into_iter() {
            match left_waiting {
                NNF::AtomPos(i) => {
                    if let Some(LeftRight::Right) = self.atoms.insert(i, LeftRight::Left) {
                        return PSWstepResult::Valid;
                    }
                }
                NNF::AtomNeg(i) => {
                    if let Some(LeftRight::Left) = self.atoms.insert(i, LeftRight::Right) {
                        return PSWstepResult::Valid;
                    }
                }
                NNF::Bot => {
                    return PSWstepResult::Valid;
                }
                NNF::Top => {
                    // do nothing
                }
                NNF::And(mut conjuncts) => {
                    new_left_waiting.append(&mut conjuncts);
                }
                NNF::Or(disjuncts) => {
                    self.ld.push(disjuncts);
                }
                NNF::NnfBox(phi) => {
                    self.lb.push(*phi);
                }
                NNF::NnfDia(phi) => {
                    self.rb.push(phi.neg());
                }
            }
        }

        let mut new_right_waiting = Vec::with_capacity(self.rw.len());
        for right_waiting in self.rw.into_iter() {
            match right_waiting {
                NNF::AtomPos(i) => {
                    if let Some(LeftRight::Left) = self.atoms.insert(i, LeftRight::Right) {
                        return PSWstepResult::Valid;
                    }
                }
                NNF::AtomNeg(i) => {
                    if let Some(LeftRight::Right) = self.atoms.insert(i, LeftRight::Left) {
                        return PSWstepResult::Valid;
                    }
                }
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
                    self.rb.push(*phi);
                }
                NNF::NnfDia(phi) => {
                    self.lb.push(phi.neg());
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

    fn into_ps(self) -> Option<PS> {
        match self.step() {
            PSWstepResult::Valid => None,
            PSWstepResult::Waiting(next) => next.into_ps(),
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
                new_psw.push(PSW {
                    atoms: self.atoms.clone(),
                    lb: self.lb.clone(),
                    rb: self.rb.clone(),
                    ld: self.ld.clone(),
                    rc: self.rc.clone(),
                    lw: vec![disj],
                    rw: Vec::new(),
                });
            }
            return PSstepResult::Waiting(new_psw);
        }
        if let Some(conjuncts) = self.rc.pop() {
            let mut new_psw = Vec::with_capacity(conjuncts.len());
            for conj in conjuncts.into_iter() {
                new_psw.push(PSW {
                    atoms: self.atoms.clone(),
                    lb: self.lb.clone(),
                    rb: self.rb.clone(),
                    ld: self.ld.clone(),
                    rc: self.rc.clone(),
                    lw: Vec::new(),
                    rw: vec![conj],
                });
            }
            return PSstepResult::Waiting(new_psw);
        }
        PSstepResult::Next(PSI {
            lb: self.lb,
            rb: self.rb,
        })
    }

    fn into_psi(self) -> Vec<PSI> {
        match self.step() {
            PSstepResult::Waiting(psw_vec) => {
                let mut output = Vec::with_capacity(psw_vec.len());
                for psw in psw_vec {
                    if let Some(ps) = psw.into_ps() {
                        output.append(&mut ps.into_psi());
                    }
                }
                output
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
            output.push(PSW {
                atoms: BTreeMap::new(),
                lb: Vec::new(),
                rb: Vec::new(),
                ld: Vec::new(),
                rc: Vec::new(),
                lw: self.lb.clone(),
                rw: vec![rb],
            });
        }
        output
    }
}

impl PSW {
    fn compute_validity(self) -> bool {
        match self.into_ps() {
            None => true,
            Some(ps) => ps.compute_validity(),
        }
    }
}

impl PS {
    fn compute_validity(self) -> bool {
        self.into_psi()
            //.into_par_iter()
            .into_iter()
            //.map(|psi| psi.is_valid())
            .all(|psi| psi.compute_validity())
        //            .reduce(|| true, |a, b| a && b)
    }
}

impl PSI {
    fn compute_validity(self) -> bool {
        self.step()
            //.into_par_iter()
            .into_iter()
            //.map(|psi| psi.is_valid())
            .any(|psw| psw.compute_validity())
        //.reduce(|| false, |a, b| a || b)
    }
}
