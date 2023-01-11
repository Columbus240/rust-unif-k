use std::collections::{BTreeMap, BTreeSet};

mod display;
pub use display::*;
mod random;
pub use random::*;
mod simpl;
pub use simpl::*;

/// Represents propositional variables in `NNF`.
pub type NnfAtom = u8;

/// A datatype to model the syntax of modal logic.
///
/// It is called "negation normal form" because negation signs may only occur
/// in front of propositional variables. This is analogous to the similar
/// notion in classical propositional logic.
#[derive(Clone, Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum NNF {
    AtomPos(NnfAtom),
    AtomNeg(NnfAtom),
    Bot,
    Top,
    And(Vec<NNF>),
    Or(Vec<NNF>),
    NnfBox(Box<NNF>),
    NnfDia(Box<NNF>),
}

impl NNF {
    /// Returns the negation of the formula.
    /// It is computed by switching `AtomPos` with `AtomNeg`, `Bot` with
    /// `Top`, `And` with `Or` and `NnfBox` with `NnfDia`.
    pub fn neg(&self) -> NNF {
        match self {
            NNF::AtomPos(i) => NNF::AtomNeg(*i),
            NNF::AtomNeg(i) => NNF::AtomPos(*i),
            NNF::Bot => NNF::Top,
            NNF::Top => NNF::Bot,
            NNF::And(a) => NNF::Or(a.iter().map(|x| x.neg()).collect()),
            NNF::Or(a) => NNF::And(a.iter().map(|x| x.neg()).collect()),
            NNF::NnfBox(a) => NNF::NnfDia(Box::new(a.neg())),
            NNF::NnfDia(a) => NNF::NnfBox(Box::new(a.neg())),
        }
    }

    /// Returns the modal degree of the formula.
    pub fn degree(&self) -> usize {
        match self {
            NNF::AtomPos(_) => 0,
            NNF::AtomNeg(_) => 0,
            NNF::Bot => 0,
            NNF::Top => 0,
            NNF::And(a) | NNF::Or(a) => {
                //a.par_iter().map(NNF::degree).max().unwrap_or(0)
                a.iter().map(NNF::degree).max().unwrap_or(0)
            }
            NNF::NnfBox(a) | NNF::NnfDia(a) => a.degree() + 1,
        }
    }

    /// Returns `true` if `AtomPos(atom)` or `AtomNeg(atom)` appears
    /// somewhere in the formula.
    pub fn contains_atom(&self, atom: NnfAtom) -> bool {
        match self {
            NNF::AtomPos(i) | NNF::AtomNeg(i) => *i == atom,
            NNF::Bot | NNF::Top => false,
            NNF::And(a) | NNF::Or(a) => {
                //a.par_iter().any(|x| x.contains_atom(atom))
                a.iter().any(|x| x.contains_atom(atom))
            }
            NNF::NnfBox(a) | NNF::NnfDia(a) => a.contains_atom(atom),
        }
    }

    /// Returns `true` if this is a ground formula. I.e. if no variable appears
    /// in it.
    pub fn is_ground(&self) -> bool {
        match self {
            NNF::AtomPos(_) | NNF::AtomNeg(_) => false,
            NNF::Bot | NNF::Top => true,
            NNF::And(a) | NNF::Or(a) => a.iter().all(|x| x.is_ground()),
            NNF::NnfBox(a) | NNF::NnfDia(a) => a.is_ground(),
        }
    }

    /// Shorthand for conjunction of two formulas.
    #[allow(dead_code)]
    pub fn and(phi: NNF, psi: NNF) -> NNF {
        NNF::And(vec![phi, psi])
    }

    /// Shorthand for disjunction of two formulas.
    #[allow(dead_code)]
    pub fn or(phi: NNF, psi: NNF) -> NNF {
        NNF::Or(vec![phi, psi])
    }

    /// Shorthand for prefixing a formula with a box.
    #[allow(dead_code)]
    pub fn boxx(self) -> NNF {
        NNF::NnfBox(Box::new(self))
    }

    /// Shorthand for prefixing a formula with a diamond.
    #[allow(dead_code)]
    pub fn dia(self) -> NNF {
        NNF::NnfDia(Box::new(self))
    }

    /// Shorthand for material implication.
    pub fn impli(phi: NNF, psi: NNF) -> NNF {
        NNF::Or(vec![phi.neg(), psi])
    }

    /// Shorthand for material equivalence.
    pub fn equiv_formula(phi: NNF, psi: NNF) -> NNF {
        NNF::And(vec![
            NNF::impli(phi.clone(), psi.clone()),
            NNF::impli(psi, phi),
        ])
    }

    /// Every variable in `subst_top` that occurs in `self` is replaced by `NNF::Top`,
    /// and every variable in `subst_bot` that occurs in `self` is replaced by `NNF::Bot`.
    /// The result is returned.
    /// Requires `subst_top` and `subst_bot` to be disjoint.
    pub fn substitute_top_bot(
        self,
        subst_top: &BTreeSet<NnfAtom>,
        subst_bot: &BTreeSet<NnfAtom>,
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
                NNF::And(conjuncts).simpl()
            }
            NNF::Or(mut disjuncts) => {
                for disjunct in disjuncts.iter_mut() {
                    *disjunct = disjunct.clone().substitute_top_bot(subst_top, subst_bot);
                }
                NNF::Or(disjuncts).simpl()
            }
            NNF::NnfBox(phi) => {
                NNF::NnfBox(Box::new(phi.substitute_top_bot(subst_top, subst_bot))).simpl()
            }
            NNF::NnfDia(phi) => {
                NNF::NnfDia(Box::new(phi.substitute_top_bot(subst_top, subst_bot))).simpl()
            }
        }
    }

    /// Every variable in `self` that occurs in `substitution` is
    /// replaced by the corresponding formula in `substitution.
    /// Variables that occur in `self` but not in `substitution` are not affected.
    pub fn substitute(&mut self, substitution: &BTreeMap<NnfAtom, NNF>) {
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

    /// Substitute all variables that occur in `self` with the formula `sigma`.
    #[allow(dead_code)]
    pub fn substitute_all(&self, sigma: &NNF) -> NNF {
        let sigma_neg = sigma.neg();
        // this indirection is, so we don't need to recompute `sigma.neg()`
        // multiple times
        self.substitute_all1(sigma, &sigma_neg)
    }

    /// Substitute all `AtomPos` that occur in `self` with `sigma` and
    /// all `AtomNeg` with `sigma_neg`.
    ///
    /// Invariant: assumes `sigma_neg` to be the negation of `sigma`.
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

    /// Returns an iterator over all variables that appear in `self`,
    /// with multiplicities/repetitions.
    pub fn iter_atoms<'a>(&'a self) -> Box<dyn Iterator<Item = NnfAtom> + 'a> {
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

    /// Returns true if `nnf` is valid in K and `false` otherwise.
    /// Uses an externally provided binary of Spartacus.
    /// The path to the binary is currently hardcoded.
    pub fn check_using_spartacus(nnf: NNF) -> bool {
        use std::process::Command;
        // Path to the spartacus binary
        const SPARTACUS_BIN: &str = "/home/steve/doc/uni/MA/spartacus/spartacus";
        let c = Command::new(SPARTACUS_BIN)
            .args([
                "--negate",
                &format!("--formula={}", nnf.display_spartacus()),
            ])
            .output()
            .expect("failed to run spartacus");
        if !c.status.success() {
            panic!("spartacus had an error");
        }

        // Determine what spartacus spat out.
        let sat: &[u8] = "satisfiable".as_bytes();
        let unsat: &[u8] = "unsatisfiable".as_bytes();

        let mut lines = c.stdout.rsplit(|b| *b == b'\n');
        lines.next();
        let last_line = lines.next().expect("output of spartacus too short");

        if last_line == unsat {
            return true;
        } else if last_line == sat {
            return false;
        }
        panic!("output of spartacus not understood");
    }
}

use proptest::prelude::*;

pub fn arb_nnf() -> impl Strategy<Value = NNF> {
    const DEFAULT_NUM_VARIABLES: NnfAtom = 1;
    arb_nnf_var(DEFAULT_NUM_VARIABLES)
}

#[allow(dead_code)]
pub fn arb_nnf_var(num_variables: NnfAtom) -> impl Strategy<Value = NNF> {
    let leaf = prop_oneof![
        Just(NNF::Top),
        Just(NNF::Bot),
        any::<NnfAtom>().prop_map(move |i| if num_variables > 0 {
            NNF::AtomPos(i % num_variables)
        } else {
            NNF::Top
        }),
        any::<NnfAtom>().prop_map(move |i| if num_variables > 0 {
            NNF::AtomNeg(i % num_variables)
        } else {
            NNF::Bot
        }),
    ];
    leaf.prop_recursive(
        8,   // 8 levels deep
        512, // Maximum 256 nodes
        10,  // Up to 10 items per collection
        |inner: BoxedStrategy<NNF>| {
            prop_oneof![
                prop::collection::vec(inner.clone(), 0..10).prop_map(NNF::And),
                prop::collection::vec(inner.clone(), 0..10).prop_map(NNF::Or),
                inner.clone().prop_map(NNF::boxx),
                inner.prop_map(NNF::dia),
            ]
        },
    )
}

proptest! {
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

    #[test]
    fn parser_compatibility(a in arb_nnf()) {
    use crate::nnf_parser::LiteralParser;
    println!("{}", a.display_parser());
    assert!(NNF::equiv_dec(&a, &LiteralParser::new().parse(&format!("{}", a.display_parser())).unwrap()));
    }
}
