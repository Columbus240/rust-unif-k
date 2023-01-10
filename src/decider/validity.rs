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
    ps.process_easy_conjs();
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
    let mut psb_vec: Vec<PSB> = Vec::new();
    let mut waiting_stack: Vec<PS> = vec![ps];

    loop {
        if let Some(ps) = waiting_stack.pop() {
            match ps_step(ps) {
                PSstepResult::Waiting(psw_vec) => {
                    for psw in psw_vec {
                        if let Some(ps) = psw.into_ps() {
                            waiting_stack.push(ps);
                        }
                    }
                }
                PSstepResult::Next(psb) => {
                    psb_vec.push(psb);
                }
            }
        } else {
            return psb_vec;
        }
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
        .all(psb_compute_validity)
}

fn psb_compute_validity(psb: PSB) -> bool {
    psb_step(psb)
        .into_par_iter()
        //.into_iter()
        .any(psw_compute_validity)
}

use proptest::proptest;
proptest! {
#[test]
fn test_validity_spartacus0(nnf in crate::nnf::arb_nnf()) {
    assert_eq!(nnf.clone().is_valid(), NNF::check_using_spartacus(nnf));
}
}
#[test]
fn test_validity_spartacus1() {
    for nnf in crate::fineform_iter::FineFormNNFIter::new(2).take(100) {
        assert_eq!(nnf.clone().is_valid(), NNF::check_using_spartacus(nnf));
    }
}

extern crate test;
#[allow(unused_imports)]
use test::Bencher;

#[bench]
fn bench_is_valid(b: &mut Bencher) {
    b.iter(|| {
        crate::fineform_iter::FineFormNNFIter::new(5)
            .take(200)
            .map(|phi| phi.is_valid())
            .for_each(drop);
    });
}
