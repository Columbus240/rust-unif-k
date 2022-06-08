use std::collections::btree_set::BTreeSet;
use std::sync::Arc;

use rayon::prelude::*;

use crate::nnf::NNF;

struct PSW {
    // left atoms
    la: BTreeSet<usize>,
    // right atoms
    ra: BTreeSet<usize>,

    // left boxes
    lb: BTreeSet<Arc<NNF>>,
    // right boxes
    rb: BTreeSet<Arc<NNF>>,

    // left disjunctions
    ld: Vec<BTreeSet<Arc<NNF>>>,
    // right conjunctions
    rc: Vec<BTreeSet<Arc<NNF>>>,

    // left waiting
    lw: BTreeSet<Arc<NNF>>,
    // right waiting
    rw: BTreeSet<Arc<NNF>>,
}

struct PS {
    // left atoms
    la: BTreeSet<usize>,
    // right atoms
    ra: BTreeSet<usize>,

    // left boxes
    lb: BTreeSet<Arc<NNF>>,
    // right boxes
    rb: BTreeSet<Arc<NNF>>,

    // left disjunctions
    ld: Vec<BTreeSet<Arc<NNF>>>,
    // right conjunctions
    rc: Vec<BTreeSet<Arc<NNF>>>,
}

struct PSI {
    // left boxes
    lb: BTreeSet<Arc<NNF>>,
    // right boxes
    rb: BTreeSet<Arc<NNF>>,
}

enum PSWstepResult {
    Waiting(PSW),
    Next(PS),
    Valid,
}

impl NNF {
    pub fn is_valid(phi: Arc<NNF>) -> bool {
        PSW::from_nnf(phi).is_valid()
    }

    pub fn is_valid0(phi: &NNF) -> bool {
        NNF::is_valid(Arc::new(phi.clone()))
    }

    pub fn equiv_dec(phi: &NNF, psi: &NNF) -> bool {
        let mut conj = BTreeSet::new();
        conj.insert(Arc::new(NNF::impli(phi, psi)));
        conj.insert(Arc::new(NNF::impli(psi, phi)));
        NNF::is_valid(Arc::new(NNF::And(conj)))
    }
}

impl PSW {
    fn from_nnf(phi: Arc<NNF>) -> PSW {
        let mut rw = BTreeSet::new();
        rw.insert(phi);
        PSW {
            la: BTreeSet::new(),
            ra: BTreeSet::new(),
            lb: BTreeSet::new(),
            rb: BTreeSet::new(),
            ld: Vec::new(),
            rc: Vec::new(),
            lw: BTreeSet::new(),
            rw: rw,
        }
    }

    fn step(mut self) -> PSWstepResult {
        let mut new_left_waiting = BTreeSet::new();
        for left_waiting in self.lw.into_iter() {
            match &*left_waiting {
                NNF::AtomPos(i) => {
                    if self.ra.contains(i) {
                        return PSWstepResult::Valid;
                    }
                    self.la.insert(*i);
                }
                NNF::AtomNeg(i) => {
                    if self.la.contains(i) {
                        return PSWstepResult::Valid;
                    }
                    self.ra.insert(*i);
                }
                NNF::Bot => {
                    return PSWstepResult::Valid;
                }
                NNF::Top => {
                    // do nothing
                }
                NNF::And(conjuncts) => {
                    new_left_waiting.append(&mut conjuncts.clone());
                }
                NNF::Or(disjuncts) => {
                    self.ld.push(disjuncts.clone());
                }
                NNF::NnfBox(phi) => {
                    self.lb.insert(phi.clone());
                }
                NNF::NnfDia(phi) => {
                    self.rb.insert(Arc::new(phi.neg()));
                }
            }
        }

        let mut new_right_waiting = BTreeSet::new();
        for right_waiting in self.rw.into_iter() {
            match &*right_waiting {
                NNF::AtomPos(i) => {
                    if self.la.contains(i) {
                        return PSWstepResult::Valid;
                    }
                    self.ra.insert(*i);
                }
                NNF::AtomNeg(i) => {
                    if self.ra.contains(i) {
                        return PSWstepResult::Valid;
                    }
                    self.la.insert(*i);
                }
                NNF::Bot => {
                    // do nothing
                }
                NNF::Top => {
                    return PSWstepResult::Valid;
                }
                NNF::And(conjuncts) => {
                    self.rc.push(conjuncts.clone());
                }
                NNF::Or(disjuncts) => {
                    new_right_waiting.append(&mut disjuncts.clone());
                }
                NNF::NnfBox(phi) => {
                    self.rb.insert(phi.clone());
                }
                NNF::NnfDia(phi) => {
                    self.lb.insert(Arc::new(phi.neg()));
                }
            }
        }

        if new_left_waiting.is_empty() && new_right_waiting.is_empty() {
            return PSWstepResult::Next(PS {
                la: self.la,
                ra: self.ra,
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
    Valid,
}

impl PS {
    fn step(mut self) -> PSstepResult {
        if let Some(disjuncts) = self.ld.pop() {
            let mut new_psw = Vec::with_capacity(disjuncts.len());
            for disj in disjuncts.into_iter() {
                let mut lw_new = BTreeSet::new();
                lw_new.insert(disj);
                new_psw.push(PSW {
                    la: self.la.clone(),
                    ra: self.ra.clone(),
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
                    la: self.la.clone(),
                    ra: self.ra.clone(),
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
        if self.la.intersection(&self.ra).next().is_none() {
            return PSstepResult::Next(PSI {
                lb: self.lb,
                rb: self.rb,
            });
        } else {
            return PSstepResult::Valid;
        }
    }

    fn to_psi(self) -> Vec<PSI> {
        match self.step() {
            PSstepResult::Valid => Vec::new(),
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
                la: BTreeSet::new(),
                ra: BTreeSet::new(),
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
            .into_par_iter()
            .fold(|| true, |acc, psi| acc && psi.is_valid())
            .reduce(|| true, |a, b| a && b)
    }
}

impl PSI {
    fn is_valid(self) -> bool {
        self.step()
            .into_par_iter()
            .fold(|| false, |acc, psw| acc || psw.is_valid())
            .reduce(|| false, |a, b| a || b)
    }
}
