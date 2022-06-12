use std::collections::btree_set::BTreeSet;

use crate::nnf::NNF;

// Like `NNF` but stores additional information, to (hopefully) speed
// up computations.
// - Which subformulae are simplified already?
// - Don't compute negations, if they aren't necessary.

// whether a formula has been
// - not simplified
// - simplified using the fast algorithm
// - simplified using the slow algorithm
enum LazyNNFSimpl {
    None,
    Fast,
    Slow,
}

#[derive(Clone, Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum LazyNNFFormula {
    AtomPos(usize),
    AtomNeg(usize),
    Bot,
    Top,
    And(Vec<LazyNNF>),
    Or(Vec<LazyNNF>),
    NnfBox(Box<LazyNNF>),
    NnfDia(Box<LazyNNF>),
}

#[derive(Clone, Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct LazyNNF {
    pub formula: LazyNNFFormula,
    pub negated: bool,
    pub simplified: bool,
}

impl LazyNNF {
    fn from_nnf(phi: NNF) -> LazyNNF {
        match phi {
            NNF::Top => LazyNNF {
                formula: LazyNNFFormula::Top,
                negated: false,
                simplified: true,
            },
            NNF::Bot => LazyNNF {
                formula: LazyNNFFormula::Bot,
                negated: false,
                simplified: true,
            },
            NNF::AtomPos(i) => LazyNNF {
                formula: LazyNNFFormula::AtomPos(i),
                negated: false,
                simplified: true,
            },
            NNF::AtomNeg(i) => LazyNNF {
                formula: LazyNNFFormula::AtomNeg(i),
                negated: false,
                simplified: true,
            },
            NNF::And(s) => LazyNNF {
                formula: LazyNNFFormula::And(s.into_iter().map(Self::from_nnf).collect()),
                negated: false,
                simplified: false,
            },
            NNF::Or(s) => LazyNNF {
                formula: LazyNNFFormula::Or(s.into_iter().map(Self::from_nnf).collect()),
                negated: false,
                simplified: false,
            },
            NNF::NnfBox(phi) => LazyNNF {
                formula: LazyNNFFormula::NnfBox(Box::new(Self::from_nnf(*phi))),
                negated: false,
                simplified: false,
            },
            NNF::NnfDia(phi) => LazyNNF {
                formula: LazyNNFFormula::NnfDia(Box::new(Self::from_nnf(*phi))),
                negated: false,
                simplified: false,
            },
        }
    }

    fn into_nnf(self) -> NNF {
        match self.formula {
            LazyNNFFormula::Top => {
                if self.negated {
                    NNF::Bot
                } else {
                    NNF::Top
                }
            }
            LazyNNFFormula::Bot => {
                if self.negated {
                    NNF::Top
                } else {
                    NNF::Bot
                }
            }
            LazyNNFFormula::AtomPos(i) => {
                if self.negated {
                    NNF::AtomNeg(i)
                } else {
                    NNF::AtomPos(i)
                }
            }
            LazyNNFFormula::AtomNeg(i) => {
                if self.negated {
                    NNF::AtomPos(i)
                } else {
                    NNF::AtomNeg(i)
                }
            }
            LazyNNFFormula::And(conjuncts) => {
                if self.negated {
                    NNF::Or(
                        conjuncts
                            .into_iter()
                            .map(|mut c| {
                                c.negated = !c.negated;
                                c.into_nnf()
                            })
                            .collect(),
                    )
                } else {
                    NNF::And(conjuncts.into_iter().map(|c| c.into_nnf()).collect())
                }
            }
            LazyNNFFormula::Or(disjuncts) => {
                if self.negated {
                    NNF::And(
                        disjuncts
                            .into_iter()
                            .map(|mut d| {
                                d.negated = !d.negated;
                                d.into_nnf()
                            })
                            .collect(),
                    )
                } else {
                    NNF::Or(disjuncts.into_iter().map(|d| d.into_nnf()).collect())
                }
            }
            LazyNNFFormula::NnfBox(mut phi) => {
                if self.negated {
                    NNF::NnfDia({
                        phi.negated = !phi.negated;
                        Box::new(phi.into_nnf())
                    })
                } else {
                    NNF::NnfBox(Box::new(phi.into_nnf()))
                }
            }
            LazyNNFFormula::NnfDia(mut phi) => {
                if self.negated {
                    NNF::NnfBox({
                        phi.negated = !phi.negated;
                        Box::new(phi.into_nnf())
                    })
                } else {
                    NNF::NnfDia(Box::new(phi.into_nnf()))
                }
            }
        }
    }
}
