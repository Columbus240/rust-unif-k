use std::collections::btree_set::BTreeSet;
use std::ops::Deref;

#[derive(Clone, Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum NNF {
    AtomPos(usize),
    AtomNeg(usize),
    Bot,
    Top,
    And(BTreeSet<NNF>),
    Or(BTreeSet<NNF>),
    NnfBox(Box<NNF>),
    NnfDia(Box<NNF>),
}

impl NNF {
    pub fn neg(&self) -> NNF {
        match self {
            NNF::AtomPos(i) => NNF::AtomNeg(*i),
            NNF::AtomNeg(i) => NNF::AtomPos(*i),
            NNF::Bot => NNF::Top,
            NNF::Top => NNF::Bot,
            NNF::And(a) => NNF::Or(a.iter().clone().map(|x| x.neg()).collect()),
            NNF::Or(a) => NNF::And(a.iter().clone().map(|x| x.neg()).collect()),
            NNF::NnfBox(a) => NNF::NnfDia(Box::new(a.neg())),
            NNF::NnfDia(a) => NNF::NnfBox(Box::new(a.neg())),
        }
    }

    pub fn impli(phi: &NNF, psi: &NNF) -> NNF {
        let mut set = BTreeSet::new();
        set.insert(phi.neg());
        set.insert(psi.clone());
        NNF::Or(set)
    }

    #[allow(dead_code)]
    pub fn simpl(&self) -> NNF {
        match self {
            NNF::AtomPos(i) => NNF::AtomPos(*i),
            NNF::AtomNeg(i) => NNF::AtomNeg(*i),
            NNF::Bot => NNF::Bot,
            NNF::Top => NNF::Top,
            NNF::And(conjuncts) => {
                let simpl_conjuncts: BTreeSet<NNF> = conjuncts
                    .iter()
                    .filter_map(|x| {
                        let s = x.simpl();
                        if s == NNF::Top {
                            None
                        } else {
                            Some(s)
                        }
                    })
                    .collect();
                if simpl_conjuncts.is_empty() {
                    return NNF::Top;
                }
                if simpl_conjuncts.len() == 1 {
                    return simpl_conjuncts.iter().next().unwrap().deref().clone();
                }
                let mut new_conjuncts = simpl_conjuncts.clone();
                for phi in simpl_conjuncts.iter().cloned() {
                    for psi in simpl_conjuncts.iter().cloned() {
                        if phi == psi {
                            continue;
                        }
                        if NNF::impli(&phi, &psi).is_valid() {
                            new_conjuncts.remove(&psi);
                        }
                        if NNF::impli(&phi, &psi.neg()).is_valid() {
                            return NNF::Bot;
                        }
                    }
                }
                if new_conjuncts.is_empty() {
                    NNF::Top
                } else {
                    NNF::And(new_conjuncts)
                }
            }
            NNF::Or(disjuncts) => {
                let simpl_disjuncts: BTreeSet<NNF> = disjuncts
                    .iter()
                    .filter_map(|x| {
                        let s = x.simpl();
                        if s == NNF::Bot {
                            None
                        } else {
                            Some(s)
                        }
                    })
                    .collect();
                if simpl_disjuncts.is_empty() {
                    return NNF::Bot;
                }
                if simpl_disjuncts.len() == 1 {
                    return simpl_disjuncts.iter().next().unwrap().clone();
                }
                let mut new_disjuncts = simpl_disjuncts.clone();
                for phi in disjuncts.iter().cloned() {
                    for psi in disjuncts.iter().cloned() {
                        if phi == psi {
                            continue;
                        }
                        if NNF::impli(&phi, &psi).is_valid() {
                            new_disjuncts.remove(&phi);
                        }
                        if NNF::impli(&phi.neg(), &psi).is_valid() {
                            return NNF::Top;
                        }
                    }
                }
                if new_disjuncts.is_empty() {
                    NNF::Bot
                } else {
                    NNF::Or(new_disjuncts)
                }
            }
            NNF::NnfBox(phi) => NNF::NnfBox(Box::new(phi.simpl())),
            NNF::NnfDia(phi) => NNF::NnfDia(Box::new(phi.simpl())),
        }
    }

    // substitutes each occurrence of a variable by the formula `sigma`
    pub fn substitute(&self, sigma: &NNF) -> NNF {
        let sigma_neg = sigma.neg();
	// this indirection is, so we don't need to recompute `sigma.neg()`
	// multiple times
	self.substitute1(sigma, &sigma_neg)
    }

    fn substitute1(&self, sigma: &NNF, sigma_neg: &NNF) -> NNF {
        match self {
            NNF::Top => NNF::Top,
            NNF::Bot => NNF::Bot,
            NNF::AtomPos(_) => sigma.clone(),
            NNF::AtomNeg(_) => sigma_neg.clone(),
            NNF::And(s) => NNF::And(
                s.iter()
                    .map(|x| {
                        x.substitute1(sigma, sigma_neg)
                    })
                    .collect(),
            ),
            NNF::Or(s) => NNF::Or(
                s.iter()
                    .map(|x| {
                        x.substitute1(sigma, sigma_neg)
                    })
                    .collect(),
            ),
            NNF::NnfBox(phi0) => NNF::NnfBox(Box::new(phi0.substitute1(sigma, sigma_neg))),
            NNF::NnfDia(phi0) => NNF::NnfDia(Box::new(phi0.substitute1(sigma, sigma_neg))),
        }
    }
}
