use super::NNF;

impl NNF {
    // the actual implementation of `simpl` and `simpl_slow`
    fn simpl_actual(self, slow: bool) -> NNF {
        match self {
            NNF::AtomPos(i) => NNF::AtomPos(i),
            NNF::AtomNeg(i) => NNF::AtomNeg(i),
            NNF::Bot => NNF::Bot,
            NNF::Top => NNF::Top,
            NNF::And(conjuncts) => {
                let mut new_conjuncts = Vec::with_capacity(conjuncts.len());
                let mut boxed_conjuncts = Vec::new();

                // Given the formula `p /\ []q` then store `p` in
                // `new_conjuncts` and `q` in `boxed_conjuncts`.

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

                    match phi {
                        NNF::NnfBox(phi_inner) => {
                            boxed_conjuncts.push(phi_inner);
                        }
                        _ => {
                            new_conjuncts.push(phi);
                        }
                    }
                }
                match (new_conjuncts.len(), boxed_conjuncts.len()) {
                    (0, 0) => NNF::Top,
                    (1, 0) => new_conjuncts.into_iter().next().unwrap(),
                    (0, 1) => NNF::NnfBox(boxed_conjuncts.into_iter().next().unwrap()),
                    (nc_len, 0) if nc_len > 1 => NNF::And(new_conjuncts),
                    (nc_len, 1) if nc_len >= 1 => {
                        new_conjuncts
                            .push(NNF::NnfBox(boxed_conjuncts.into_iter().next().unwrap()));
                        NNF::And(new_conjuncts)
                    }
                    (_, _) => {
                        let mut new_boxed_conjuncts: Vec<NNF> =
                            Vec::with_capacity(boxed_conjuncts.len());
                        for bc in boxed_conjuncts.into_iter() {
                            new_boxed_conjuncts.push(*bc);
                        }
                        let boxed_conjuncts = NNF::And(new_boxed_conjuncts);
                        new_conjuncts.push(NNF::NnfBox(Box::new(boxed_conjuncts)));
                        NNF::And(new_conjuncts)
                    }
                }
            }
            NNF::Or(disjuncts) => {
                let mut new_disjuncts = Vec::with_capacity(disjuncts.len());
                let mut diamond_disjuncts = Vec::new();

                // Given the formula `p \/ <>q` store `p` in
                // `new_disjuncts` and `q` in `diamond_disjuncts`.

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

                    match phi {
                        NNF::NnfDia(phi_inner) => {
                            diamond_disjuncts.push(phi_inner);
                        }
                        _ => {
                            new_disjuncts.push(phi);
                        }
                    }
                }

                match (new_disjuncts.len(), diamond_disjuncts.len()) {
                    (0, 0) => NNF::Bot,
                    (1, 0) => new_disjuncts.into_iter().next().unwrap(),
                    (0, 1) => NNF::NnfDia(diamond_disjuncts.into_iter().next().unwrap()),
                    (nd_len, 0) if nd_len > 1 => NNF::Or(new_disjuncts),
                    (nd_len, 1) if nd_len >= 1 => {
                        new_disjuncts
                            .push(NNF::NnfDia(diamond_disjuncts.into_iter().next().unwrap()));
                        NNF::Or(new_disjuncts)
                    }
                    (_, _) => {
                        let mut new_diamond_disjuncts: Vec<NNF> =
                            Vec::with_capacity(diamond_disjuncts.len());
                        for dd in diamond_disjuncts.into_iter() {
                            new_diamond_disjuncts.push(*dd);
                        }
                        let diamond_disjuncts = NNF::Or(new_diamond_disjuncts);
                        new_disjuncts.push(NNF::NnfDia(Box::new(diamond_disjuncts)));
                        NNF::Or(new_disjuncts)
                    }
                }
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
}

use proptest::prelude::*;

proptest! {
    #[test]
    fn simpl_equiv(a in super::arb_nnf()) {
    // simplification returns equivalent formulae
    assert!(NNF::equiv_dec(&a, &a.clone().simpl()));
    assert!(NNF::equiv_dec(&a, &a.clone().simpl_slow()));

    // every formula is equivalent to itself, but not to its negation
    assert!(NNF::equiv_dec(&a, &a));
    assert!(!NNF::equiv_dec(&a, &a.neg()));
    }
}
