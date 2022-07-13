use std::collections::{BTreeMap, BTreeSet};

#[allow(unused_imports)]
use proptest::prelude::*;
use proptest_derive::Arbitrary;

use super::sequents::*;
use crate::nnf::NNF;

pub fn push_if_not_exists<T: PartialEq>(vec: &mut Vec<T>, t: T) {
    let mut exists = false;

    for t0 in vec.iter() {
        if t == *t0 {
            exists = true;
            break;
        }
    }

    if !exists {
        vec.push(t);
    }
}

/// Processing Sequent Disjunctions
/// contains only left-disjunctions (besides boxes and atoms)
#[derive(Clone, Debug)]
pub struct PSD {
    // atoms (left or right)
    atoms: BTreeMap<usize, LeftRight>,

    // left boxes
    lb: Vec<NNF>,
    // right boxes
    rb: Vec<NNF>,

    // left disjunctions
    ld: Vec<Vec<NNF>>,
}

impl PSD {
    fn is_empty(&self) -> bool {
        self.atoms.is_empty() && self.lb.is_empty() && self.rb.is_empty() && self.ld.is_empty()
    }
}

impl TryFrom<PS> for PSD {
    type Error = PS;

    fn try_from(value: PS) -> Result<Self, Self::Error> {
        if !value.rc.is_empty() {
            Err(value)
        } else {
            Ok(PSD {
                atoms: value.atoms,
                lb: value.lb,
                rb: value.rb,
                ld: value.ld,
            })
        }
    }
}

/// Processing Sequent Boxes
/// a `PSI` for which `atoms` is empty. I.e. it contains no atoms on either side.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PSB {
    pub lb: Vec<NNF>,
    pub rb: Vec<NNF>,
}

impl PSB {
    fn new_contradictory() -> PSB {
	PSB {
	    lb: Vec::new(),
	    rb: Vec::new(),
	}
    }
    fn is_empty(&self) -> bool {
        self.lb.is_empty() && self.rb.is_empty()
    }
}

impl TryFrom<PS> for PSB {
    type Error = PS;

    fn try_from(value: PS) -> Result<Self, Self::Error> {
        if !value.atoms.is_empty() || !value.ld.is_empty() || !value.rc.is_empty() {
            Err(value)
        } else {
            Ok(PSB {
                lb: value.lb,
                rb: value.rb,
            })
        }
    }
}

#[derive(Clone, Debug)]
pub struct ClauseWaitingConj {
    // Sequents that contain at least one atom
    irreducibles: Vec<PSI>,

    // Sequents that do not contain atoms
    atom_sequents: Vec<PSB>,

    // sequents that only contain left-disjunctions
    disj_sequents: Vec<PSD>,
    // sequents that contain both right-conjunctions and left-disjunctions
    conj_disj_sequents: Vec<PS>,
}

#[derive(Clone, Debug)]
pub struct ClauseWaitingDisj {
    // Sequents that contain at least one atom
    irreducibles: Vec<PSI>,

    // Sequents that do not contain atoms
    atom_sequents: Vec<PSB>,

    // sequents that only contain left-disjunctions
    disj_sequents: Vec<PSD>,
}

impl ClauseWaitingDisj {
    fn new_valid() -> ClauseWaitingDisj {
        ClauseWaitingDisj {
            irreducibles: Vec::new(),
            atom_sequents: Vec::new(),
            disj_sequents: Vec::new(),
        }
    }
    fn new_contradictory() -> ClauseWaitingDisj {
	ClauseWaitingDisj {
	    irreducibles: Vec::new(),
	    atom_sequents: vec![PSB::new_contradictory()],
	    disj_sequents: Vec::new(),
	}
    }
    fn is_empty(&self) -> bool {
        self.irreducibles.is_empty() && self.disj_sequents.is_empty()
    }

    /// Returns `Some(false)` if the clause contains an empty sequent.
    /// Returns `Some(true)` if the clause is empty
    /// Returns `None` otherwise
    fn simple_check_validity(&self) -> Option<bool> {
        if self.irreducibles.is_empty()
            && self.atom_sequents.is_empty()
            && self.disj_sequents.is_empty()
        {
            return Some(true);
        }
        for psi in self.irreducibles.iter() {
            if psi.is_empty() {
                return Some(false);
            }
        }
        for psi in self.atom_sequents.iter() {
            if psi.is_empty() {
                return Some(false);
            }
        }
        for psi in self.disj_sequents.iter() {
            if psi.is_empty() {
                return Some(false);
            }
        }
        return None;
    }
}

impl From<ClauseWaitingDisj> for ClauseWaitingConj {
    fn from(value: ClauseWaitingDisj) -> Self {
        ClauseWaitingConj {
            irreducibles: value.irreducibles,
            atom_sequents: value.atom_sequents,
            disj_sequents: value.disj_sequents,
            conj_disj_sequents: Vec::new(),
        }
    }
}

impl From<ClauseAtoms> for ClauseWaitingConj {
    fn from(value: ClauseAtoms) -> Self {
        ClauseWaitingConj {
            irreducibles: value.irreducibles,
            atom_sequents: value.atom_sequents,
            disj_sequents: Vec::new(),
            conj_disj_sequents: Vec::new(),
        }
    }
}

impl ClauseWaitingConj {
    fn new_empty() -> ClauseWaitingConj {
        ClauseWaitingConj {
            irreducibles: Vec::new(),
            atom_sequents: Vec::new(),
            disj_sequents: Vec::new(),
            conj_disj_sequents: Vec::new(),
        }
    }
    fn new_contradictory() -> ClauseWaitingConj {
        ClauseWaitingConj {
            irreducibles: Vec::new(),
            atom_sequents: vec![PSB::new_contradictory()],
            disj_sequents: Vec::new(),
            conj_disj_sequents: Vec::new(),
        }
    }

    pub fn from_nnf(nnf: NNF) -> ClauseWaitingConj {
        ClauseWaitingConj::from_psw(PSW::from_nnf(nnf))
    }

    fn is_empty(&self) -> bool {
        self.irreducibles.is_empty()
            && self.disj_sequents.is_empty()
            && self.conj_disj_sequents.is_empty()
    }

    fn from_psw(psw: PSW) -> ClauseWaitingConj {
        // Sort the sequents into the right category.
        let mut irreducibles: Vec<PSI> = Vec::new();
        let mut atom_sequents: Vec<PSB> = Vec::new();
        let mut disj_sequents: Vec<PSD> = Vec::new();
        let mut conj_disj_sequents: Vec<PS> = Vec::new();

        for sequent in psw.to_ps().into_iter() {
            if sequent.rc.is_empty() {
                // it is at least a `disj_sequent`
                if sequent.ld.is_empty() {
                    if sequent.atoms.is_empty() {
                        atom_sequents.push(sequent.try_into().unwrap());
                    } else {
                        irreducibles.push(sequent.try_into().unwrap());
                    }
                } else {
                    disj_sequents.push(sequent.try_into().unwrap());
                }
            } else {
                conj_disj_sequents.push(sequent);
            }
        }
        ClauseWaitingConj {
            irreducibles,
            atom_sequents,
            disj_sequents,
            conj_disj_sequents,
        }
    }

    /// Only processes the `atom_sequents` which have at most a single boxed term on the right.
    /// This way we can avoid doing work twice in all branches.
    pub fn process_clause_easy_atoms(&mut self) {
        let mut i = 0;
        while i < self.atom_sequents.len() {
            let sequent = &self.atom_sequents[i];

            // If the sequent has no boxed formulae on the right, it is contradictory.
            // Making the whole clause contradictory.
            if sequent.rb.len() == 0 {
                *self = ClauseWaitingConj::new_contradictory();
                return;
            }

            // If the sequent has more than one boxed formula on the
            // right, applying the box-rule causes a branching, i.e. new clauses.
            // This is "too complicated", so don't deal with these here.
            if sequent.rb.len() > 1 {
                i += 1;
                continue;
            }

            // Remove `sequent` from `clause.atom_sequents`
            let sequent = self.atom_sequents.swap_remove(i);

            let new_sequent: PSW = PSW {
                atoms: BTreeMap::new(),
                lb: Vec::new(),
                rb: Vec::new(),
                ld: Vec::new(),
                rc: Vec::new(),
                lw: sequent.lb,
                rw: sequent.rb,
            };

            // if `to_ps` returns `None`, the sequent was valid and
            // imposes no further restriction on `clause`.
            if let Some(new_sequent) = new_sequent.to_ps() {
                self.conj_disj_sequents.push(new_sequent);
            }

            // Don't increment `i` here, so the new value of
            // `clause.atom_sequents[i]` can be treated as well.
            // Or if `i` was the last element, break out of this loop.
        }
    }

    pub fn process_conjs(mut self) -> ClauseWaitingDisj {
        let mut new_psw: Vec<PSW> = Vec::new();
        for mut ps in self.conj_disj_sequents.into_iter() {
            if let Some(conjuncts) = ps.rc.pop() {
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
            } else {
                // If by chance, the sequent `ps` has no
                // left-disjunctions, store it as such.
                if ps.ld.is_empty() {
                    // If by chance, the sequent `ps` also has some atoms,
                    // store it as irreducible.
                    let new_psi : PSI = ps.try_into().unwrap();
                    if new_psi.atoms.is_empty() {
                        // This sequent does not have any atoms on either side.
                        // If it has no boxed formula on the right, it is contradictory,
                        // making the whole clause contradictory.
                        if new_psi.rb.is_empty() {
                            return ClauseWaitingDisj::new_contradictory();
                        }
                        push_if_not_exists(&mut self.atom_sequents, new_psi.to_psb());
                    } else {
                        push_if_not_exists(&mut self.irreducibles, new_psi);
                    }
                } else {
                    self.disj_sequents.push(PSD {
                        atoms: ps.atoms,
                        lb: ps.lb,
                        rb: ps.rb,
                        ld: ps.ld,
                    });
                }
            }
        }
        self.conj_disj_sequents = new_psw.into_iter().filter_map(PSW::to_ps).collect();
        if self.conj_disj_sequents.is_empty() {
            ClauseWaitingDisj {
                irreducibles: self.irreducibles,
                atom_sequents: self.atom_sequents,
                disj_sequents: self.disj_sequents,
            }
        } else {
            self.process_conjs()
        }
    }
}

#[derive(Debug)]
pub struct ClauseAtoms {
    irreducibles: Vec<PSI>,

    // Sequents that might not contain atoms
    atom_sequents: Vec<PSB>,
}

impl ClauseAtoms {
    fn new_empty() -> ClauseAtoms {
        ClauseAtoms {
            irreducibles: Vec::new(),
            atom_sequents: Vec::new(),
        }
    }

    fn new_contradictory() -> ClauseAtoms {
        ClauseAtoms {
            irreducibles: Vec::new(),
            atom_sequents: vec![PSB::new_contradictory()],
        }
    }

    /// Returns `Some(false)` if the clause contains an empty sequent.
    /// Returns `Some(true)` if the clause is empty
    /// Returns `None` otherwise
    fn simple_check_validity(&self) -> Option<bool> {
        if self.irreducibles.is_empty() && self.atom_sequents.is_empty() {
            return Some(true);
        }
        for psi in self.irreducibles.iter() {
            if psi.is_empty() {
                return Some(false);
            }
        }
        for psi in self.atom_sequents.iter() {
            if psi.is_empty() {
                return Some(false);
            }
        }
        return None;
    }

    fn unifiability_simplify(mut self) -> ClauseAtoms {
        // if there is a sequent of the form `p ⇒ ø`, then replace `p` everywhere by `⊥`.
        // if there is a sequent of the form `ø ⇒ p`, then replace `p` everywhere by `T`.

        let mut require_top: BTreeSet<usize> = BTreeSet::new();
        let mut require_bot: BTreeSet<usize> = BTreeSet::new();

        for sequent in self.irreducibles.iter() {
            if sequent.atoms.len() == 1 && sequent.rb.is_empty() && sequent.lb.is_empty() {
                match sequent.atoms.iter().next().unwrap() {
                    (i, LeftRight::Left) => require_bot.insert(*i),
                    (i, LeftRight::Right) => require_top.insert(*i),
                };
            }
        }

        // If the two sets are both empty, there is nothing to do.
        if require_top.is_empty() && require_bot.is_empty() {
            return self;
        }

        // If the two sets overlap, then we are contradictory.
        if !require_top.is_disjoint(&require_bot) {
            return ClauseAtoms::new_contradictory();
        }

        let mut new_irreducibles = Vec::with_capacity(self.irreducibles.len());

        // is true, if further simplifications are possible
        let mut simplify_further = false;

        // Otherwise, perform the substitutions. Because the
        // substitutions are so simple, a lot of simplifications can
        // happen now.
        for sequent in self.irreducibles.into_iter() {
            if let Some(seq) = sequent.substitute_top_bot(&require_top, &require_bot) {
                if seq.atoms.len() == 1 && seq.lb.is_empty() && seq.rb.is_empty() {
                    simplify_further = true;
                }
                if seq.atoms.is_empty() {
                    self.atom_sequents.push(seq.to_psb());
                } else {
                    new_irreducibles.push(seq);
                }
            }
        }
        self.irreducibles = new_irreducibles;

        if simplify_further {
            self.unifiability_simplify()
        } else {
            self
        }
    }
}

/// A clause that only consists of irreducible sequents.
/// I.e. each sequent has at least one atom on each side.
#[derive(Clone, Debug)]
pub struct ClauseIrred {
    irreducibles: Vec<PSI>,
}

impl TryFrom<ClauseAtoms> for ClauseIrred {
    type Error = ClauseAtoms;
    fn try_from(value: ClauseAtoms) -> Result<Self, Self::Error> {
        if !value.atom_sequents.is_empty() {
            Err(value)
        } else {
            Ok(ClauseIrred {
                irreducibles: value.irreducibles,
            })
        }
    }
}

impl ClauseIrred {
    fn new_empty() -> ClauseIrred {
        ClauseIrred {
            irreducibles: Vec::new(),
        }
    }

    fn is_empty(&self) -> bool {
        self.irreducibles.is_empty()
    }

    fn to_nnf(&self) -> NNF {
        NNF::And(self.irreducibles.iter().map(PSI::to_nnf).collect())
    }

    fn simplify(mut self) -> ClauseIrred {
        let mut new_sequents: Vec<PSI> = Vec::with_capacity(self.irreducibles.len());

        'sequent: for sequent in self.irreducibles.into_iter() {
            if sequent.is_empty() {
                // This sequent is contradictory, making the whole clause contradictory.
                new_sequents.clear();
                new_sequents.push(sequent);
                break;
            }

            // Remove trivially valid sequents
            // namely those which have a boxed formula occurring on both sides.
            for left_box in sequent.lb.iter() {
                for right_box in sequent.rb.iter() {
                    if left_box == right_box {
                        continue 'sequent;
                    }
                }
            }

            // Remove duplicate sequents
            push_if_not_exists(&mut new_sequents, sequent);
        }

        self.irreducibles = new_sequents;
        self
    }

    fn unifiability_simplify(self) -> ClauseAtoms {
        ClauseAtoms {
            irreducibles: self.irreducibles,
            atom_sequents: Vec::new(),
        }
        .unifiability_simplify()
    }

    /// Returns `Some(false)` if the clause contains an empty sequent.
    /// Returns `Some(true)` if the clause is empty
    /// Returns `None` otherwise
    fn simple_check_validity(&self) -> Option<bool> {
        if self.irreducibles.is_empty() {
            return Some(true);
        }
        for sequent in self.irreducibles.iter() {
            if sequent.is_empty() {
                return Some(false);
            }
        }
        return None;
    }

    fn simple_check_unifiability(&self) -> Option<bool> {
        if let Some(b) = self.simple_check_validity() {
            return Some(b);
        }

        // Check whether the left/right atoms are all disjoint.
        let mut atoms = self.irreducibles[0].atoms.clone();
        for sequent in &self.irreducibles[1..] {
            for (k, v) in atoms.clone().iter() {
                if sequent.atoms.get(k) != Some(v) {
                    atoms.remove(k);
                }
            }
        }
        if !atoms.is_empty() {
            // We found some intersection, so * -> top or * -> bot are unifiers.
            return Some(true);
        }

        return None;
    }

    pub fn display_beautiful<'a>(&'a self) -> ClauseIrredDisplayBeautiful<'a> {
        ClauseIrredDisplayBeautiful { clause: self }
    }

    pub fn display_spartacus<'a>(&'a self) -> ClauseIrredDisplaySpartacus<'a> {
        ClauseIrredDisplaySpartacus { clause: self }
    }
}

fn arb_psi() -> impl Strategy<Value = PSI> {
    (
	prop::collection::btree_map(any::<usize>(), any::<LeftRight>(), 0..10),
        prop::collection::vec(crate::nnf::arb_nnf(), 0..10),
        prop::collection::vec(crate::nnf::arb_nnf(), 0..10),
    )
        .prop_map(|(atoms, lb, rb)| PSI { atoms: atoms, lb: lb, rb: rb })
}

#[allow(dead_code)]
fn arb_clause_irred() -> impl Strategy<Value = ClauseIrred> {
    prop::collection::vec(arb_psi(), 0..10).prop_map(|irreducibles| ClauseIrred {
        irreducibles: irreducibles,
    })
}

proptest! {
 #[test]
 fn simplify_equiv(clause in arb_clause_irred()) {
     assert!(NNF::equiv_dec(clause.clone().to_nnf(), clause.simplify().to_nnf()));
 }
}

pub struct ClauseIrredDisplayBeautiful<'a> {
    clause: &'a ClauseIrred,
}

impl<'a> std::fmt::Display for ClauseIrredDisplayBeautiful<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut sequent_iter = self.clause.irreducibles.iter();

        if let Some(seq) = sequent_iter.next() {
            write!(f, "{}", seq.display_beautiful())?;
        } else {
            write!(f, "⊤")?;
        }
        for seq in sequent_iter {
            write!(f, " ; {}", seq.display_beautiful())?;
        }
        Ok(())
    }
}

pub struct ClauseIrredDisplaySpartacus<'a> {
    clause: &'a ClauseIrred,
}

impl<'a> std::fmt::Display for ClauseIrredDisplaySpartacus<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            NNF::And(self.clause.irreducibles.iter().map(PSI::to_nnf).collect())
                .display_spartacus()
        )
    }
}

#[derive(Debug)]
pub struct ClauseSetWaiting {
    irreducibles: Vec<ClauseIrred>,
    waiting_atoms: Vec<ClauseAtoms>,
    waiting_disj: Vec<ClauseWaitingDisj>,
}

#[derive(Debug)]
pub struct ClauseSetAtoms {
    irreducibles: Vec<ClauseIrred>,
    waiting_atoms: Vec<ClauseAtoms>,
}

#[derive(Clone, Debug)]
pub struct ClauseSetIrred {
    pub irreducibles: Vec<ClauseIrred>,
}

impl ClauseSetIrred {
    fn new_valid() -> ClauseSetIrred {
        ClauseSetIrred {
            irreducibles: vec![ClauseIrred::new_empty()],
        }
    }

    fn new_contradictory() -> ClauseSetIrred {
        ClauseSetIrred {
            irreducibles: Vec::new(),
        }
    }

    pub fn from_nnf(nnf: NNF) -> ClauseSetIrred {
        ClauseSetAtoms::from_nnf(nnf).process_atoms()
    }

    pub fn to_nnf_boxed(&self) -> NNF {
        NNF::Or(
            self.irreducibles
                .iter()
                .map(|clause| NNF::NnfBox(Box::new(ClauseIrred::to_nnf(clause))))
                .collect(),
        )
    }

    pub fn is_valid(self) -> bool {
        if self.irreducibles.is_empty() {
            return false;
        }

        let mut new_clauses = Vec::with_capacity(self.irreducibles.len());

        // Remove all atoms from all sequents and start anew.
        'a: for clause in self.irreducibles.into_iter() {
            if clause.is_empty() {
                // We found a trivial clause, so this clause set is valid.
                return true;
            }

            let mut new_sequents: Vec<PSB> = Vec::with_capacity(clause.irreducibles.len());

            for sequent in clause.irreducibles.into_iter() {
                // Note that we forget `sequent.atoms` here.
                // For validity checking this is permitted.
                let sequent = PSB {
                    lb: sequent.lb,
                    rb: sequent.rb,
                };
                if sequent.is_empty() {
                    // We found an un-satisfiable sequent. So this clause is contradictory
                    // and can be skipped
                    continue 'a;
                }
                new_sequents.push(sequent);
            }

            new_clauses.push(ClauseAtoms {
                irreducibles: Vec::new(),
                atom_sequents: new_sequents,
            });
        }

        let new_clause_set: ClauseSetAtoms = ClauseSetAtoms {
            irreducibles: Vec::new(),
            waiting_atoms: new_clauses,
        };

        new_clause_set.process_atoms().is_valid()
    }

    pub fn simplify_unifiability(self) -> ClauseSetIrred {
        let initial_length = self.irreducibles.len();
        let mut new_clauses = Vec::with_capacity(initial_length);
        for clause in self.irreducibles.into_iter() {
            let clause = clause.simplify().unifiability_simplify();
            new_clauses.push(clause);
        }
        let new_clause_set = ClauseSetAtoms {
            irreducibles: Vec::new(),
            waiting_atoms: new_clauses,
        }
        .process_atoms();
        if new_clause_set.irreducibles.len() != initial_length {
            new_clause_set.simplify_unifiability()
        } else {
            new_clause_set
        }
    }

    /// Tries to check for unifiability, without making further simplifications.
    /// Try calling `simplify_unifiability` beforehand, for better results.
    pub fn is_unifiable(&self) -> Option<bool> {
        if self.irreducibles.is_empty() {
            return Some(false);
        }

        let mut maybe_unifiable = false;

        for clause in self.irreducibles.iter() {
            match clause.simple_check_unifiability() {
                None => {
                    maybe_unifiable = true;
                }
                Some(true) => return Some(true),
                Some(false) => {}
            }
        }
        if maybe_unifiable {
            return None;
        } else {
            return Some(false);
        }
    }
}

impl ClauseSetWaiting {
    pub fn from_clause(clause: ClauseWaitingDisj) -> ClauseSetWaiting {
        ClauseSetWaiting {
            irreducibles: Vec::new(),
            waiting_atoms: Vec::new(),
            waiting_disj: vec![clause],
        }
    }

    pub fn from_nnf(nnf: NNF) -> ClauseSetWaiting {
        ClauseSetWaiting::from_clause(ClauseWaitingConj::from_nnf(nnf).process_conjs())
    }

    pub fn process_disjs(mut self) -> ClauseSetAtoms {
        let mut new_waiting_disj = Vec::new();

        for mut clause in self.waiting_disj.into_iter() {
            if let Some(mut waiting_disj_sequent) = clause.disj_sequents.pop() {
                // Go through the next waiting disjunction.
                if let Some(disjuncts) = waiting_disj_sequent.ld.pop() {
                    new_waiting_disj.extend(disjuncts.into_iter().map(|disjunct| {
                        // Write down the new sequent
                        let new_psw = PSW {
                            atoms: waiting_disj_sequent.atoms.clone(),
                            lb: waiting_disj_sequent.lb.clone(),
                            rb: waiting_disj_sequent.rb.clone(),
                            ld: waiting_disj_sequent.ld.clone(),
                            rc: Vec::new(),
                            lw: vec![disjunct],
                            rw: Vec::new(),
                        };
                        let new_clause_waiting_conj = ClauseWaitingConj::from_psw(new_psw);
                        new_clause_waiting_conj.process_conjs()
                    }));
                } else {
                    // There are no remaining disjunctions on the left for this sequent,
                    // so it is irreducible
                    let new_psi = PSI {
                        atoms: waiting_disj_sequent.atoms,
                        lb: waiting_disj_sequent.lb,
                        rb: waiting_disj_sequent.rb,
                    };

                    push_if_not_exists(&mut clause.irreducibles, new_psi);
                }
            } else {
                // `clause` is irreducible
                let clause = ClauseAtoms {
                    irreducibles: clause.irreducibles,
                    atom_sequents: clause.atom_sequents,
                };
                // if the clause is trivially valid, the whole clause set is valid
                // if the clause is trivially contradictory, we can omit this clause
                match clause.simple_check_validity() {
                    Some(true) => {
                        self.irreducibles.clear();
                        self.irreducibles.push(ClauseIrred::new_empty());
                        self.waiting_atoms.clear();
                        new_waiting_disj.clear();
                        break;
                    }
                    Some(false) => {}
                    None => {
                        self.waiting_atoms.push(clause);
                    }
                }
            }
        }
        self.waiting_disj = new_waiting_disj;
        if self.waiting_disj.is_empty() {
            ClauseSetAtoms {
                irreducibles: self.irreducibles,
                waiting_atoms: self.waiting_atoms,
            }
        } else {
            self.process_disjs()
        }
    }
}

impl ClauseSetAtoms {
    pub fn from_nnf(nnf: NNF) -> ClauseSetAtoms {
        ClauseSetWaiting::from_nnf(nnf).process_disjs()
    }

    fn from_psw(psw: PSW) -> ClauseSetAtoms {
        let clause_waiting_disj = ClauseWaitingConj::from_psw(psw).process_conjs();
        let clause_set_waiting = ClauseSetWaiting {
            irreducibles: Vec::new(),
            waiting_atoms: Vec::new(),
            waiting_disj: vec![clause_waiting_disj],
        };
        clause_set_waiting.process_disjs()
    }

    pub fn unifiability_simplify(self) -> ClauseSetAtoms {
        let mut new_clause_atoms =
            Vec::with_capacity(self.irreducibles.len() + self.waiting_atoms.len());

        for clause_irred in self.irreducibles.into_iter() {
            new_clause_atoms.push(clause_irred.unifiability_simplify());
        }
        for clause_atom in self.waiting_atoms.into_iter() {
            new_clause_atoms.push(clause_atom.unifiability_simplify());
        }
        ClauseSetAtoms {
            irreducibles: Vec::new(),
            waiting_atoms: new_clause_atoms,
        }
    }

    pub fn process_atoms(mut self) -> ClauseSetIrred {
        let mut new_waiting_atoms: Vec<ClauseAtoms> = Vec::new();

        for clause in self.waiting_atoms.into_iter() {
            // Shortcut if the clause has no `atom_sequents`.
            if clause.atom_sequents.is_empty() {
                // `clause` is irreducible

                let clause: ClauseIrred = clause.try_into().unwrap();
                let clause = clause.simplify();

                // if the clause is trivially valid, the whole clause set is valid
                // if the clause is trivially contradictory, we can omit this clause
                match clause.simple_check_validity() {
                    Some(true) => {
                        return ClauseSetIrred::new_valid();
                    }
                    Some(false) => {}
                    None => {
                        self.irreducibles.push(clause);
                    }
                }
                continue;
            }

            // first process the easy atom sequents.
            let mut clause = ClauseWaitingConj::from(clause);
	    println!("\t{:?}", clause);
            clause.process_clause_easy_atoms();
	    println!("\t{:?}", clause);
            let mut clause: ClauseWaitingDisj = clause.process_conjs();

            // Shortcut, if the clause is valid or contradictory.
            if let Some(b) = clause.simple_check_validity() {
                if b {
                    return ClauseSetIrred::new_valid();
                } else {
                    return ClauseSetIrred::new_contradictory();
                }
            }

            // Shortcut if the clause has no `atom_sequents`.
            if clause.atom_sequents.is_empty() {
                // Simplify the new clause until it becomes a `ClauseAtoms`.
                let new_clause_set_atoms = ClauseSetWaiting::from_clause(clause).process_disjs();
                let ClauseSetAtoms {
                    irreducibles: mut new_irred,
                    waiting_atoms: mut newest_waiting_atoms,
                } = new_clause_set_atoms;

                // Extend the current clause set with the new one.
                self.irreducibles.append(&mut new_irred);
                new_waiting_atoms.append(&mut newest_waiting_atoms);
                continue;
            }

            let waiting_atoms_sequent = clause.atom_sequents.pop().unwrap();
            // If the sequent has no atoms, split it up.

            // It is possible, that one of the newly generated sequents will be "trivially" true.
            // In such a case it suffices to add only the rest of the clause.
            let mut delta_waiting_atoms = Vec::with_capacity(waiting_atoms_sequent.rb.len());
            let mut early_exit = false;

            'delta: for delta in waiting_atoms_sequent.rb.into_iter() {
                // Write down the new sequent
                let new_psw = PSW {
                    // recall that `waiting_atoms_sequent.atoms` is empty
                    atoms: BTreeMap::new(),
                    lb: Vec::new(),
                    rb: Vec::new(),
                    ld: Vec::new(),
                    rc: Vec::new(),
                    // the currently boxed left formulae, but without their boxes
                    lw: waiting_atoms_sequent.lb.clone(),
                    rw: vec![delta],
                };

                if let Some(new_ps) = new_psw.to_ps() {
                    // Add the sequent to the current clause.
		    let mut new_clause : ClauseWaitingConj = clause.clone().into();
		    new_clause.conj_disj_sequents.push(new_ps);
                    let new_clause_disj = new_clause.process_conjs();

                    // Simplify the new clause until it becomes a `ClauseAtoms`.
                    let new_clause_set_atoms =
                        ClauseSetWaiting::from_clause(new_clause_disj).process_disjs();

                    let ClauseSetAtoms {
                        irreducibles: mut new_irred,
                        waiting_atoms: mut newest_waiting_atoms,
                    } = new_clause_set_atoms;

                    // Extend the current clause set with the new one.
                    self.irreducibles.append(&mut new_irred);
                    delta_waiting_atoms.append(&mut newest_waiting_atoms);
                } else {
                    // We have found a "trivial" branch which adds no further condition.
                    // Remove all other `delta` branches, because they are more difficult.
                    // This is done by forgetting about `delta_waiting_atoms`
                    new_waiting_atoms.push(ClauseAtoms {
                        irreducibles: clause.irreducibles.clone(),
                        atom_sequents: clause.atom_sequents.clone(),
                    });
                    early_exit = true;
                    break 'delta;
                }
            }
            if !early_exit {
                new_waiting_atoms.append(&mut delta_waiting_atoms);
            }
        }
        self.waiting_atoms = new_waiting_atoms;
        if self.waiting_atoms.is_empty() {
            ClauseSetIrred {
                irreducibles: self.irreducibles,
            }
        } else {
            self.process_atoms()
        }
    }
}

use proptest::proptest;

proptest! {
    #[test]
    fn clause_validity_simplifier(formula in crate::nnf::arb_nnf()) {
    use crate::nnf::NNF;

    let clause_set_irred = ClauseSetWaiting::from_nnf(formula.clone()).process_disjs().process_atoms();
    let formula_valid = formula.clone().is_valid();
    let clause_set_valid = clause_set_irred.to_nnf_boxed().is_valid();
    // Now, the algorithm is correct if, `clause_set_irred` is valid iff `formula` is valid.
    assert_eq!(formula_valid, clause_set_valid);
    assert_eq!(formula_valid, clause_set_irred.is_valid());
    }
}
