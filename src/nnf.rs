use std::collections::btree_set::BTreeSet;
use std::sync::Arc;

#[derive(Clone, Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum NNF {
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
    pub fn neg(&self) -> NNF {
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

    pub fn impli(phi: &NNF, psi: &NNF) -> NNF {
        let mut set = BTreeSet::new();
        set.insert(Arc::new(phi.neg()));
        set.insert(Arc::new(psi.clone()));
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
                let mut simpl_conjuncts: BTreeSet<Arc<_>> =
                    conjuncts.iter().map(|x| Arc::new(x.simpl())).collect();
                let mut new_conjuncts = simpl_conjuncts.clone();
                for phi in simpl_conjuncts.iter().cloned() {
                    for psi in simpl_conjuncts.iter().cloned() {
                        if phi == psi {
                            continue;
                        }
                        if NNF::is_valid0(&NNF::impli(&phi, &psi)) {
                            new_conjuncts.remove(&psi);
                        }
                        if NNF::is_valid0(&NNF::impli(&phi, &psi.neg())) {
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
                let mut simpl_disjuncts: BTreeSet<Arc<_>> =
                    disjuncts.iter().map(|x| Arc::new(x.simpl())).collect();
                let mut new_disjuncts = simpl_disjuncts.clone();
                for phi in disjuncts.iter().cloned() {
                    for psi in disjuncts.iter().cloned() {
                        if phi == psi {
                            continue;
                        }
                        if NNF::is_valid0(&NNF::impli(&phi, &psi)) {
                            new_disjuncts.remove(&phi);
                        }
                        if NNF::is_valid0(&NNF::impli(&phi.neg(), &psi)) {
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
            NNF::NnfBox(phi) => NNF::NnfBox(Arc::new(phi.simpl())),
            NNF::NnfDia(phi) => NNF::NnfDia(Arc::new(phi.simpl())),
        }
    }

    // substitutes each occurrence of a variable by the formula `sigma`
    pub fn substitute(&self, sigma: Arc<NNF>) -> Arc<NNF> {
        let sigma_neg = Arc::new(sigma.neg());
        let top = Arc::new(NNF::Top);
        let bot = Arc::new(NNF::Bot);
        self.substitute1(sigma, sigma_neg, top, bot)
    }

    fn substitute1(
        &self,
        sigma: Arc<NNF>,
        sigma_neg: Arc<NNF>,
        top: Arc<NNF>,
        bot: Arc<NNF>,
    ) -> Arc<NNF> {
        match self {
            NNF::Top => top,
            NNF::Bot => bot,
            NNF::AtomPos(_) => sigma,
            NNF::AtomNeg(_) => sigma_neg,
            NNF::And(s) => Arc::new(NNF::And(
                s.iter()
                    .cloned()
                    .map(|x| {
                        x.substitute1(sigma.clone(), sigma_neg.clone(), top.clone(), bot.clone())
                    })
                    .collect(),
            )),
            NNF::Or(s) => Arc::new(NNF::Or(
                s.iter()
                    .cloned()
                    .map(|x| {
                        x.substitute1(sigma.clone(), sigma_neg.clone(), top.clone(), bot.clone())
                    })
                    .collect(),
            )),
            NNF::NnfBox(phi0) => Arc::new(NNF::NnfBox(phi0.substitute1(
                sigma.clone(),
                sigma_neg.clone(),
                top.clone(),
                bot.clone(),
            ))),
            NNF::NnfDia(phi0) => Arc::new(NNF::NnfDia(phi0.substitute1(
                sigma.clone(),
                sigma_neg.clone(),
                top.clone(),
                bot.clone(),
            ))),
        }
    }
}
