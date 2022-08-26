use rayon::prelude::*;

use std::collections::{BTreeMap, BTreeSet};

mod display;
pub use display::*;

#[derive(Clone, Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum NNF {
    AtomPos(usize),
    AtomNeg(usize),
    Bot,
    Top,
    And(Vec<NNF>),
    Or(Vec<NNF>),
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

    pub fn len(&self) -> usize {
        match self {
            NNF::AtomPos(_) => 2,
            NNF::AtomNeg(_) => 2,
            NNF::Bot => 1,
            NNF::Top => 1,
            NNF::And(a) | NNF::Or(a) => {
                a.par_iter()
                    .map(NNF::len)
                    .fold(|| 0, |acc: usize, x: usize| acc + x)
                    .reduce(|| 0, |acc, n| acc + n)
                    + 1
            }
            NNF::NnfBox(a) | NNF::NnfDia(a) => a.len() + 1,
        }
    }

    pub fn degree(&self) -> usize {
        match self {
            NNF::AtomPos(_) => 0,
            NNF::AtomNeg(_) => 0,
            NNF::Bot => 0,
            NNF::Top => 0,
            NNF::And(a) | NNF::Or(a) => a.par_iter().map(NNF::degree).max().unwrap_or(0),
            NNF::NnfBox(a) | NNF::NnfDia(a) => a.len() + 1,
        }
    }

    #[allow(dead_code)]
    pub fn and(phi: NNF, psi: NNF) -> NNF {
        NNF::And(vec![phi, psi])
    }

    #[allow(dead_code)]
    pub fn or(phi: NNF, psi: NNF) -> NNF {
        NNF::Or(vec![phi, psi])
    }

    #[allow(dead_code)]
    pub fn boxx(self) -> NNF {
        NNF::NnfBox(Box::new(self))
    }

    #[allow(dead_code)]
    pub fn dia(self) -> NNF {
        NNF::NnfDia(Box::new(self))
    }

    pub fn impli(phi: NNF, psi: NNF) -> NNF {
        NNF::Or(vec![phi.neg(), psi])
    }

    pub fn equiv_formula(phi: NNF, psi: NNF) -> NNF {
        NNF::And(vec![
            NNF::impli(phi.clone(), psi.clone()),
            NNF::impli(psi, phi),
        ])
    }

    // the actual implementation of `simpl` and `simpl_slow`
    fn simpl_actual(self, slow: bool) -> NNF {
        match self {
            NNF::AtomPos(i) => NNF::AtomPos(i),
            NNF::AtomNeg(i) => NNF::AtomNeg(i),
            NNF::Bot => NNF::Bot,
            NNF::Top => NNF::Top,
            NNF::And(conjuncts) => {
                let mut new_conjuncts = Vec::with_capacity(conjuncts.len());

                'outer: for phi in conjuncts
                    .into_iter()
                    .filter_map(|phi| {
                        let phi0 = phi.simpl_actual(slow);
                        if phi0 == NNF::Top {
                            return None::<std::vec::IntoIter<NNF>>;
                        }
                        if let NNF::And(conj) = phi0 {
                            Some(conj.into_iter())
                        } else {
                            Some(vec![phi0].into_iter())
                        }
                    })
                    .flatten()
                {
                    if phi == NNF::Bot {
                        return NNF::Bot;
                    }
                    let phi_neg = phi.neg();

                    for psi in new_conjuncts.iter() {
                        if phi == *psi {
                            continue 'outer;
                        }
                        if slow {
                            if NNF::impli(psi.clone(), phi.clone()).is_valid() {
                                continue 'outer;
                            }
                            if NNF::impli(phi.clone(), psi.neg()).is_valid() {
                                return NNF::Bot;
                            }
                        } else if phi_neg == *psi {
                            return NNF::Bot;
                        }
                    }
                    new_conjuncts.push(phi);
                }
                if new_conjuncts.is_empty() {
                    return NNF::Top;
                }
                if new_conjuncts.len() == 1 {
                    return new_conjuncts.into_iter().next().unwrap();
                }
                NNF::And(new_conjuncts)
            }
            NNF::Or(disjuncts) => {
                let mut new_disjuncts = Vec::with_capacity(disjuncts.len());

                'outer: for phi in disjuncts
                    .into_iter()
                    .filter_map(|phi| {
                        let phi0 = phi.simpl_actual(slow);
                        if phi0 == NNF::Bot {
                            return None::<std::vec::IntoIter<NNF>>;
                        }
                        if let NNF::Or(disj) = phi0 {
                            Some(disj.into_iter())
                        } else {
                            Some(vec![phi0].into_iter())
                        }
                    })
                    .flatten()
                {
                    if phi == NNF::Top {
                        return NNF::Top;
                    }
                    let phi_neg = phi.neg();

                    for psi in new_disjuncts.iter() {
                        if phi == *psi {
                            continue 'outer;
                        }
                        if slow {
                            if NNF::impli(phi.clone(), psi.clone()).is_valid() {
                                continue 'outer;
                            }
                            if NNF::impli(phi_neg.clone(), psi.clone()).is_valid() {
                                return NNF::Top;
                            }
                        } else if phi_neg == *psi {
                            return NNF::Top;
                        }
                    }
                    new_disjuncts.push(phi);
                }

                if new_disjuncts.is_empty() {
                    return NNF::Bot;
                }
                if new_disjuncts.len() == 1 {
                    return new_disjuncts.into_iter().next().unwrap();
                }

                NNF::Or(new_disjuncts)
            }
            NNF::NnfBox(phi) => {
                let phi = phi.simpl_actual(slow);
                if phi == NNF::Top {
                    NNF::Top
                } else {
                    NNF::NnfBox(Box::new(phi))
                }
            }
            NNF::NnfDia(phi) => {
                let phi = phi.simpl_actual(slow);
                if phi == NNF::Bot {
                    NNF::Bot
                } else {
                    NNF::NnfDia(Box::new(phi))
                }
            }
        }
    }

    pub fn simpl(self) -> NNF {
        self.simpl_actual(false)
    }

    #[allow(dead_code)]
    pub fn simpl_slow(self) -> NNF {
        self.simpl_actual(true)
    }

    /// Requires `subst_top` and `subst_bot` to be disjoint.
    /// Every variable in `subst_top` that occurs in `self` is replaced by `NNF::Top`,
    /// and every variable in `subst_bot` that occurs in `self` is replaced by `NNF::Bot`.
    /// The result is returned.
    pub fn substitute_top_bot(
        self,
        subst_top: &BTreeSet<usize>,
        subst_bot: &BTreeSet<usize>,
    ) -> NNF {
        // if the two sets intersect, abort
        if !subst_top.is_disjoint(subst_bot) {
            panic!("substitute_top_bot requires disjoint sets as arguments");
        }

        match self {
            NNF::Top => NNF::Top,
            NNF::Bot => NNF::Bot,
            NNF::AtomPos(i) => {
                if subst_top.contains(&i) {
                    NNF::Top
                } else if subst_bot.contains(&i) {
                    NNF::Bot
                } else {
                    NNF::AtomPos(i)
                }
            }
            NNF::AtomNeg(i) => {
                if subst_top.contains(&i) {
                    NNF::Bot
                } else if subst_bot.contains(&i) {
                    NNF::Top
                } else {
                    NNF::AtomNeg(i)
                }
            }
            NNF::And(mut conjuncts) => {
                for conjunct in conjuncts.iter_mut() {
                    *conjunct = conjunct.clone().substitute_top_bot(subst_top, subst_bot);
                }
                NNF::And(conjuncts)
            }
            NNF::Or(mut disjuncts) => {
                for disjunct in disjuncts.iter_mut() {
                    *disjunct = disjunct.clone().substitute_top_bot(subst_top, subst_bot);
                }
                NNF::Or(disjuncts)
            }
            NNF::NnfBox(phi) => NNF::NnfBox(Box::new(phi.substitute_top_bot(subst_top, subst_bot))),
            NNF::NnfDia(phi) => NNF::NnfDia(Box::new(phi.substitute_top_bot(subst_top, subst_bot))),
        }
    }

    pub fn substitute(&mut self, substitution: &BTreeMap<usize, NNF>) {
        match self {
            NNF::Top => {}
            NNF::Bot => {}
            NNF::AtomPos(atom) => {
                if let Some(nnf) = substitution.get(atom) {
                    *self = nnf.clone();
                }
            }
            NNF::AtomNeg(atom) => {
                if let Some(nnf) = substitution.get(atom) {
                    *self = nnf.neg();
                }
            }
            NNF::And(s) => {
                for phi in s.iter_mut() {
                    phi.substitute(substitution);
                }
            }
            NNF::Or(s) => {
                for phi in s.iter_mut() {
                    phi.substitute(substitution);
                }
            }
            NNF::NnfBox(phi0) => {
                phi0.substitute(substitution);
            }
            NNF::NnfDia(phi0) => {
                phi0.substitute(substitution);
            }
        }
    }

    // substitutes each occurrence of a variable by the formula `sigma`
    #[allow(dead_code)]
    pub fn substitute_all(&self, sigma: &NNF) -> NNF {
        let sigma_neg = sigma.neg();
        // this indirection is, so we don't need to recompute `sigma.neg()`
        // multiple times
        self.substitute_all1(sigma, &sigma_neg)
    }

    fn substitute_all1(&self, sigma: &NNF, sigma_neg: &NNF) -> NNF {
        match self {
            NNF::Top => NNF::Top,
            NNF::Bot => NNF::Bot,
            NNF::AtomPos(_) => sigma.clone(),
            NNF::AtomNeg(_) => sigma_neg.clone(),
            NNF::And(s) => NNF::And(
                s.iter()
                    .map(|x| x.substitute_all1(sigma, sigma_neg))
                    .collect(),
            ),
            NNF::Or(s) => NNF::Or(
                s.iter()
                    .map(|x| x.substitute_all1(sigma, sigma_neg))
                    .collect(),
            ),
            NNF::NnfBox(phi0) => NNF::NnfBox(Box::new(phi0.substitute_all1(sigma, sigma_neg))),
            NNF::NnfDia(phi0) => NNF::NnfDia(Box::new(phi0.substitute_all1(sigma, sigma_neg))),
        }
    }
}
impl<'a> NNF {
    pub fn iter_atoms(&'a self) -> Box<dyn Iterator<Item = usize> + 'a> {
        use std::iter;
        match self {
            NNF::Top => Box::new(iter::empty()),
            NNF::Bot => Box::new(iter::empty()),
            NNF::AtomPos(i) => Box::new(iter::once(*i)),
            NNF::AtomNeg(i) => Box::new(iter::once(*i)),
            NNF::And(vec) => Box::new(vec.iter().flat_map(NNF::iter_atoms)),
            NNF::Or(vec) => Box::new(vec.iter().flat_map(NNF::iter_atoms)),
            NNF::NnfBox(phi) => Box::new(phi.iter_atoms()),
            NNF::NnfDia(phi) => Box::new(phi.iter_atoms()),
        }
    }
}

use proptest::prelude::*;

#[allow(dead_code)]
pub fn arb_nnf() -> impl Strategy<Value = NNF> {
    let leaf = prop_oneof![
        Just(NNF::Top),
        Just(NNF::Bot),
        any::<usize>().prop_map(|i| NNF::AtomPos(i % 1)),
        any::<usize>().prop_map(|i| NNF::AtomNeg(i % 1)),
    ];
    leaf.prop_recursive(
        8,   // 8 levels deep
        512, // Maximum 256 nodes
        10,  // Up to 10 items per collection
        |inner| {
            prop_oneof![
                prop::collection::vec(inner.clone(), 0..10).prop_map(NNF::And),
                prop::collection::vec(inner.clone(), 0..10).prop_map(NNF::Or),
                inner.clone().prop_map(|x| NNF::NnfBox(Box::new(x))),
                inner.prop_map(|x| NNF::NnfDia(Box::new(x))),
            ]
        },
    )
}

proptest! {
    #[test]
    fn simpl_equiv(a in arb_nnf()) {
    // simplification returns equivalent formulae
    assert!(NNF::equiv_dec(&a, &a.clone().simpl()));
    assert!(NNF::equiv_dec(&a, &a.clone().simpl_slow()));

    // every formula is equivalent to itself, but not to its negation
    assert!(NNF::equiv_dec(&a, &a));
    assert!(!NNF::equiv_dec(&a, &a.neg()));
    }

    #[test]
    fn necessitation(a in arb_nnf()) {
    assert_eq!(a.clone().is_valid(), NNF::NnfBox(Box::new(a)).is_valid());
    }

    #[test]
    fn modal_conj_disj_prop(a in prop::collection::vec(arb_nnf(), 0..10)) {
    assert!(
        NNF::Or(a.iter().map(|x| NNF::NnfBox(Box::new(x.clone()))).collect()).is_valid()
        == (a.iter().cloned().fold(false, |acc, phi| acc || phi.is_valid()))
    );
    assert!(
        NNF::And(a.clone()).is_valid() == (a.iter().cloned().fold(true, |acc, phi| acc && phi.is_valid()))
    );
    }
}
