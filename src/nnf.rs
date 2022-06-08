use std::collections::btree_set::BTreeSet;

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
                    return simpl_conjuncts.iter().next().unwrap().clone();
                }
                if simpl_conjuncts.contains(&NNF::Bot) {
                    return NNF::Bot;
                }

                // If any two formulae in `simpl_conjuncts` are complements
                // of eachother, return `NNF::Bot`.
                for phi in simpl_conjuncts.iter() {
                    for psi in simpl_conjuncts.iter() {
                        if *phi == psi.neg() {
                            return NNF::Bot;
                        }
                    }
                }
                NNF::And(simpl_conjuncts)
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
                if simpl_disjuncts.contains(&NNF::Top) {
                    return NNF::Top;
                }

                // If any two formulae in `simpl_disjuncts` are complements
                // of eachother, return `NNF::Top`.
                for phi in simpl_disjuncts.iter() {
                    for psi in simpl_disjuncts.iter() {
                        if *phi == psi.neg() {
                            return NNF::Top;
                        }
                    }
                }
                NNF::Or(simpl_disjuncts)
            }
            NNF::NnfBox(phi) => NNF::NnfBox(Box::new(phi.simpl())),
            NNF::NnfDia(phi) => NNF::NnfDia(Box::new(phi.simpl())),
        }
    }

    #[allow(dead_code)]
    pub fn simpl_slow(&self) -> NNF {
        match self {
            NNF::AtomPos(i) => NNF::AtomPos(*i),
            NNF::AtomNeg(i) => NNF::AtomNeg(*i),
            NNF::Bot => NNF::Bot,
            NNF::Top => NNF::Top,
            NNF::And(conjuncts) => {
                let mut new_conjuncts = BTreeSet::new();

                'outer: for phi in conjuncts.iter() {
                    let phi0 = phi.simpl_slow();
                    if phi0 == NNF::Top {
                        continue;
                    }

                    for psi in new_conjuncts.iter() {
                        if phi0 == *psi {
                            continue;
                        }
                        if NNF::impli(&psi, &phi0).is_valid() {
                            continue 'outer;
                        }
                        if NNF::impli(&phi0, &psi.neg()).is_valid() {
                            return NNF::Bot;
                        }
                    }
                    new_conjuncts.insert(phi0.clone());
                }
                if new_conjuncts.is_empty() {
                    return NNF::Top;
                }
                if new_conjuncts.len() == 1 {
                    return new_conjuncts.iter().next().unwrap().clone();
                }
                NNF::And(new_conjuncts)
            }
            NNF::Or(disjuncts) => {
                let mut new_disjuncts = BTreeSet::new();

                'outer: for phi in disjuncts.iter() {
                    let phi0 = phi.simpl_slow();
                    if phi0 == NNF::Bot {
                        continue;
                    }

                    for psi in new_disjuncts.iter() {
                        if phi0 == *psi {
                            continue;
                        }
                        if NNF::impli(&phi0, &psi).is_valid() {
                            continue 'outer;
                        }
                        if NNF::impli(&phi0.neg(), &psi).is_valid() {
                            return NNF::Top;
                        }
                    }
                    new_disjuncts.insert(phi0.clone());
                }
                if new_disjuncts.is_empty() {
                    return NNF::Bot;
                }
                if new_disjuncts.len() == 1 {
                    return new_disjuncts.iter().next().unwrap().clone();
                }
                NNF::Or(new_disjuncts)
            }
            NNF::NnfBox(phi) => NNF::NnfBox(Box::new(phi.simpl_slow())),
            NNF::NnfDia(phi) => NNF::NnfDia(Box::new(phi.simpl_slow())),
        }
    }

    // substitutes each occurrence of a variable by the formula `sigma`
    #[allow(dead_code)]
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
            NNF::And(s) => NNF::And(s.iter().map(|x| x.substitute1(sigma, sigma_neg)).collect()),
            NNF::Or(s) => NNF::Or(s.iter().map(|x| x.substitute1(sigma, sigma_neg)).collect()),
            NNF::NnfBox(phi0) => NNF::NnfBox(Box::new(phi0.substitute1(sigma, sigma_neg))),
            NNF::NnfDia(phi0) => NNF::NnfDia(Box::new(phi0.substitute1(sigma, sigma_neg))),
        }
    }
}

use proptest::prelude::*;

#[allow(dead_code)]
fn arb_nnf() -> impl Strategy<Value = NNF> {
    let leaf = prop_oneof![
        Just(NNF::Top),
        Just(NNF::Bot),
        any::<usize>().prop_map(NNF::AtomPos),
        any::<usize>().prop_map(NNF::AtomNeg),
    ];
    leaf.prop_recursive(
        8,   // 8 levels deep
        256, // Maximum 256 nodes
        10,  // Up to 10 items per collection
        |inner| {
            prop_oneof![
                prop::collection::btree_set(inner.clone(), 0..10).prop_map(NNF::And),
                prop::collection::btree_set(inner.clone(), 0..10).prop_map(NNF::Or),
                inner.clone().prop_map(|x| NNF::NnfBox(Box::new(x))),
                inner.clone().prop_map(|x| NNF::NnfDia(Box::new(x))),
            ]
        },
    )
}

proptest! {
    #[test]
    fn simpl_equiv(a in arb_nnf()) {
	// simplification returns equivalent formulae
	assert!(NNF::equiv_dec(&a, &a.simpl()));
	assert!(NNF::equiv_dec(&a, &a.simpl_slow()));

	// every formula is equivalent to itself, but not to its negation
	assert!(NNF::equiv_dec(&a, &a));
	assert!(!NNF::equiv_dec(&a, &a.neg()));
    }

    #[test]
    fn modal_conj_disj_prop(a in prop::collection::btree_set(arb_nnf(), 0..10)) {
	assert!(
	    NNF::Or(a.iter().map(|x| NNF::NnfBox(Box::new(x.clone()))).collect()).is_valid()
		== (a.iter().fold(false, |acc, phi| acc || phi.is_valid()))
	);
	assert!(
	    NNF::And(a.clone()).is_valid() == (a.iter().fold(true, |acc, phi| acc && phi.is_valid()))
	);
    }
}
