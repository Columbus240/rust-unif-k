//TODO: Use the same sequents as `crate::decider::sequents`, but verify that
//the checker doesn't change its output.
//TODO: Use the simple validity checker for `PSB` to speed things up.
use std::collections::btree_map::BTreeMap;
use std::collections::btree_set::BTreeSet;

#[allow(unused_imports)]
use rayon::prelude::*;

use super::sequents::*;
use crate::nnf::NNF;

impl NNF {
    pub fn is_valid(&self) -> bool {
        // short circuit
        match self {
            NNF::Bot | NNF::AtomPos(_) | NNF::AtomNeg(_) => {
                return false;
            }
            _ => {}
        }

        psw_compute_validity(PSW::from_nnf(self.clone()))
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

enum PSstepResult {
    Waiting(Vec<PSW>),
    Next(PSB),
}

fn ps_step(mut ps: PS) -> PSstepResult {
    if let Some(disjuncts) = ps.ld.pop() {
        let mut new_psw = Vec::with_capacity(disjuncts.len());
        for disj in disjuncts.into_iter() {
            new_psw.push(PSW {
                atoms: ps.atoms.clone(),
                lb: ps.lb.clone(),
                rb: ps.rb.clone(),
                ld: ps.ld.clone(),
                rc: ps.rc.clone(),
                lw: vec![disj],
                rw: Vec::new(),
            });
        }
        return PSstepResult::Waiting(new_psw);
    }
    if let Some(conjuncts) = ps.rc.pop() {
        let mut new_psw = Vec::with_capacity(conjuncts.len());
        for conj in conjuncts.into_iter() {
            new_psw.push(PSW {
                atoms: ps.atoms.clone(),
                lb: ps.lb.clone(),
                rb: ps.rb.clone(),
                ld: ps.ld.clone(),
                rc: ps.rc.clone(),
                lw: Vec::new(),
                rw: vec![conj],
            });
        }
        return PSstepResult::Waiting(new_psw);
    }
    PSstepResult::Next(PSB {
        lb: ps.lb,
        rb: ps.rb,
    })
}

fn ps_into_psb(ps: PS) -> Vec<PSB> {
    match ps_step(ps) {
        PSstepResult::Waiting(psw_vec) => {
            let mut output = Vec::with_capacity(psw_vec.len());
            for psw in psw_vec {
                if let Some(ps) = psw.into_ps() {
                    output.append(&mut ps_into_psb(ps));
                }
            }
            output
        }
        PSstepResult::Next(psi) => vec![psi],
    }
}

/// returns an empty list, if the formula is contradictory
fn psb_step(psb: PSB) -> Vec<PSW> {
    let mut output = Vec::with_capacity(psb.rb.len());
    for rb in psb.rb.into_iter() {
        output.push(PSW {
            atoms: BTreeMap::new(),
            lb: BTreeSet::new(),
            rb: BTreeSet::new(),
            ld: Vec::new(),
            rc: Vec::new(),
            lw: {
                let mut lw = Vec::with_capacity(psb.lb.len());
                lw.extend(psb.lb.iter().cloned());
                lw
            },
            rw: vec![rb],
        });
    }
    output
}

fn psw_compute_validity(psw: PSW) -> bool {
    match psw.into_ps() {
        None => true,
        Some(ps) => ps_compute_validity(ps),
    }
}

fn ps_compute_validity(ps: PS) -> bool {
    ps_into_psb(ps)
        .into_par_iter()
        //.into_iter()
        //.map(|psi| psi.is_valid())
        .all(psb_compute_validity)
    //            .reduce(|| true, |a, b| a && b)
}

fn psb_compute_validity(psb: PSB) -> bool {
    psb_step(psb)
        .into_par_iter()
        //.into_iter()
        //.map(|psi| psi.is_valid())
        .any(psw_compute_validity)
    //.reduce(|| false, |a, b| a || b)
}
