use std::collections::{BTreeMap, BTreeSet};

#[allow(unused_imports)]
use proptest::prelude::*;

use super::sequents::*;
use crate::nnf::{NnfAtom, NNF};

#[derive(Clone, Debug, Eq, PartialEq, PartialOrd, Ord)]
pub struct ClauseWaiting {
    // Sequents that contain at least one atom
    pub irreducibles: BTreeSet<PSI>,

    // Sequents that do not contain atoms
    pub atom_sequents: BTreeSet<PSB>,

    // Sequents that contain both right-conjunctions and left-disjunctions
    pub conj_disj_sequents: BTreeSet<PS>,
}

impl ClauseWaiting {
    fn new_valid() -> ClauseWaiting {
        ClauseWaiting {
            irreducibles: BTreeSet::new(),
            atom_sequents: BTreeSet::new(),
            conj_disj_sequents: BTreeSet::new(),
        }
    }

    fn new_contradictory() -> ClauseWaiting {
        let mut set = BTreeSet::new();
        set.insert(PSB::new_contradictory());
        ClauseWaiting {
            irreducibles: BTreeSet::new(),
            atom_sequents: set,
            conj_disj_sequents: BTreeSet::new(),
        }
    }

    fn is_empty(&self) -> bool {
        self.irreducibles.is_empty()
            && self.atom_sequents.is_empty()
            && self.conj_disj_sequents.is_empty()
    }

    pub fn from_nnf(nnf: NNF) -> ClauseWaiting {
        ClauseWaiting::from_psw(PSW::from_nnf(nnf))
    }

    fn from_psw(psw: PSW) -> ClauseWaiting {
        if let Some(sequent) = psw.into_ps() {
            // Sort the sequents into the right category.
            let mut irreducibles: BTreeSet<PSI> = BTreeSet::new();
            let mut atom_sequents = BTreeSet::new();
            let mut conj_disj_sequents: BTreeSet<PS> = BTreeSet::new();

            if sequent.rc.is_empty() && sequent.ld.is_empty() {
                if sequent.atoms.is_empty() {
                    atom_sequents.insert(sequent.try_into().unwrap());
                } else {
                    irreducibles.insert(sequent.try_into().unwrap());
                }
            } else {
                conj_disj_sequents.insert(sequent);
            }

            ClauseWaiting {
                irreducibles,
                atom_sequents,
                conj_disj_sequents,
            }
        } else {
            ClauseWaiting::new_valid()
        }
    }
    pub fn display_beautiful(&self) -> ClauseWaitingDisplayBeautiful {
        ClauseWaitingDisplayBeautiful { clause: self }
    }

    pub fn from_sequent(ps: PS) -> ClauseWaiting {
        let mut cw = ClauseWaiting {
            irreducibles: BTreeSet::new(),
            atom_sequents: BTreeSet::new(),
            conj_disj_sequents: BTreeSet::new(),
        };
        cw.conj_disj_sequents.insert(ps);
        cw
    }

    pub fn from_psw_vec(psw: Vec<PSW>) -> ClauseWaiting {
        ClauseWaiting {
            irreducibles: BTreeSet::new(),
            atom_sequents: BTreeSet::new(),
            conj_disj_sequents: psw.into_iter().filter_map(PSW::into_ps).collect(),
        }
    }

    /// Returns `Some(false)` if the clause contains an empty sequent,
    /// or a variable-free sequent which is not valid.
    /// Returns `Some(true)` if the clause is empty
    /// Returns `None` otherwise
    fn simple_check_validity(&self) -> Option<bool> {
        if self.is_empty() {
            return Some(true);
        }
        for psi in self.irreducibles.iter() {
            if psi.is_empty() {
                return Some(false);
            }
        }
        for psb in self.atom_sequents.iter() {
            if psb.is_varfree() && !psb.to_nnf().is_valid() {
                return Some(false);
            }
        }
        for ps in self.conj_disj_sequents.iter() {
            if ps.is_empty() {
                return Some(false);
            }
        }
        None
    }

    /// Notice that this function is not called by `process_easy_boxes`.
    fn insert_psb(&mut self, psb: PSB) {
        match psb.step_if_easy() {
            PsbEasyResult::InValid => *self = ClauseWaiting::new_contradictory(),
            PsbEasyResult::Hard(psb) => {
                self.atom_sequents.insert(psb);
            }
            PsbEasyResult::Psi(psi) => {
                self.insert_psi(psi);
            }
            PsbEasyResult::Ps(ps) => {
                self.insert_ps(ps);
            }
            PsbEasyResult::Valid => {}
        }
    }

    fn insert_psi(&mut self, psi: PSI) {
        // Check for redundant sequents.
        // If two sequents have the same premise/conclusion but their
        // conclusions/premises are subsets of eachother, we can
        // remove the sequent with the larger set of
        // conclusions/premises.

        let mut remove_current_sequent: bool = false;

        self.irreducibles.drain_filter(|other_sequent| {
            // return true, if `other_sequent` is the larger sequent to remove it.
            // return false otherwise to keep that `other_sequent` in the set.
            match PSI::check_subset(other_sequent, &psi) {
                Some(LeftRight::Left) => {
                    remove_current_sequent = true;
                    false
                }
                Some(LeftRight::Right) => true,
                None => false,
            }
        });

        if remove_current_sequent {
            return;
        }

        self.irreducibles.insert(psi);
    }

    fn insert_ps(&mut self, ps: PS) {
        self.conj_disj_sequents.insert(ps);
    }

    pub fn process_easy_conjs(&mut self) {
        let cd_sequents = std::mem::take(&mut self.conj_disj_sequents);
        for mut sequent in cd_sequents.into_iter() {
            sequent.process_easy_conjs();
            self.insert_ps(sequent);
        }
    }

    /// Only processes the `atom_sequents` which have at most a single boxed term on the right.
    /// This way we can avoid doing work twice in all branches.
    /// Notice the similarity to `insert_psb` and that this function does not call `insert_psb`.
    pub fn process_easy_boxes(mut self) -> Self {
        let mut waiting_atoms: BTreeSet<PSB> = std::mem::take(&mut self.atom_sequents);

        while let Some(sequent) = waiting_atoms.pop_first() {
            match sequent.step_if_easy() {
                PsbEasyResult::InValid => return ClauseWaiting::new_contradictory(),
                PsbEasyResult::Hard(sequent) => {
                    self.atom_sequents.insert(sequent);
                }
                PsbEasyResult::Psi(psi) => {
                    self.insert_psi(psi);
                }
                PsbEasyResult::Ps(ps) => {
                    self.insert_ps(ps);
                }
                PsbEasyResult::Valid => {}
            }
        }
        self
    }

    pub fn process_conjs_step(&mut self) {
        // Move `self.conj_disj_sequents` into `old_ps_vec` and replace it with a new vector.
        let old_ps_vec: BTreeSet<PS> = std::mem::take(&mut self.conj_disj_sequents);

        // Then process those sequents and insert the resulting sequents in `self` again.
        for ps in old_ps_vec.into_iter() {
            match ps.process_conjs_step() {
                PSConjsResult::Boxes(psb) => {
                    self.insert_psb(psb);
                }
                PSConjsResult::Irred(psi) => {
                    self.insert_psi(psi);
                }
                PSConjsResult::NewPS(new_ps) => {
                    for ps in new_ps.into_iter() {
                        self.insert_ps(ps);
                    }
                }
            }
        }
    }

    pub fn process_conjs(mut self) -> ClauseAtoms {
        loop {
            match self.try_into() {
                Ok(clause_atoms) => return clause_atoms,
                Err(mut clause_next) => {
                    clause_next.process_conjs_step();
                    self = clause_next;
                }
            }
        }
    }

    pub fn to_nnf(&self) -> NNF {
        let irreducibles = self.irreducibles.iter().map(|psi| psi.to_nnf());
        let atom_sequents = self.atom_sequents.iter().map(|psb| psb.to_nnf());
        let conj_disj_sequents = self.conj_disj_sequents.iter().map(|ps| ps.to_nnf());
        NNF::And(
            irreducibles
                .chain(atom_sequents)
                .chain(conj_disj_sequents)
                .collect(),
        )
    }

    pub fn simple_check_unifiability(&self) -> Option<bool> {
        if let Some(b) = self.simple_check_validity() {
            return Some(b);
        }

        // Check whether the left/right atoms are all disjoint.
        // But this only works if there are no `atom_sequents`.
        // Those trivially make the left/right atom-sets disjoint.
        if self.atom_sequents.is_empty() {
            // First create an iterator over all atoms.
            let mut atom_iter = {
                let irred = self.irreducibles.iter().map(|psi| &psi.atoms);
                let waiting = self.conj_disj_sequents.iter().map(|ps| &ps.atoms);
                irred.chain(waiting)
            };

            let mut atoms = {
                if let Some(atoms) = atom_iter.next() {
                    atoms.clone()
                } else {
                    // Edge case:
                    // If the clause contains only `PSB`. Then we can't tell.
                    return None;
                }
            };

            for other_atoms in atom_iter {
                if atoms.is_empty() {
                    break;
                }
                for (k, v) in atoms.clone().iter() {
                    if other_atoms.get(k) != Some(v) {
                        atoms.remove(k);
                    }
                }
            }

            if !atoms.is_empty() {
                // We found some intersection, so * -> top or * -> bot are unifiers.
                return Some(true);
            }
        }

        None
    }

    /// Thoroughly checks the validity of this clause using the validity checker.
    pub fn check_valid(&self) -> bool {
        self.to_nnf().is_valid()
    }

    pub fn substitute(&mut self, substitution: &BTreeMap<NnfAtom, NNF>) {
        let irreducibles = std::mem::take(&mut self.irreducibles);
        let irreducibles = irreducibles
            .into_iter()
            .filter_map(|sequent| sequent.substitute(substitution).into_ps());
        let atom_sequents = std::mem::take(&mut self.atom_sequents);
        for mut sequent in atom_sequents.into_iter() {
            sequent.substitute(substitution);
            self.atom_sequents.insert(sequent);
        }
        let conj_disj_sequents = std::mem::take(&mut self.conj_disj_sequents);
        for mut sequent in conj_disj_sequents.into_iter() {
            sequent.substitute(substitution);
            self.conj_disj_sequents.insert(sequent);
        }

        for sequent in irreducibles {
            match TryInto::<PSI>::try_into(sequent) {
                Err(ps) => {
                    self.conj_disj_sequents.insert(ps);
                }
                Ok(psi) => {
                    match TryInto::<PSB>::try_into(psi) {
                        Err(psi) => self.irreducibles.insert(psi),
                        Ok(psb) => self.atom_sequents.insert(psb),
                    };
                }
            }
        }
    }

    pub fn unifiability_simplify_empty(&mut self) {
        // if there is a sequent of the form `p ⇒ ø`, then replace `p` everywhere by `⊥`.
        // if there is a sequent of the form `ø ⇒ p`, then replace `p` everywhere by `T`.

        let mut require_top: BTreeSet<NnfAtom> = BTreeSet::new();
        let mut require_bot: BTreeSet<NnfAtom> = BTreeSet::new();

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
            return;
        }

        // If the two sets overlap, then we are contradictory.
        if !require_top.is_disjoint(&require_bot) {
            *self = ClauseWaiting::new_contradictory();
            return;
        }

        // is true, if further simplifications are possible
        let mut simplify_further = false;

        let old_irreducibles = std::mem::take(&mut self.irreducibles);
        let old_atom_sequents = std::mem::take(&mut self.atom_sequents);
        let old_conj_disj = std::mem::take(&mut self.conj_disj_sequents);

        // Perform the substitutions. Because the substitutions are so
        // simple, a lot of simplifications can happen now.
        for sequent in old_irreducibles.into_iter() {
            if let Some(seq) = sequent.substitute_top_bot(&require_top, &require_bot) {
                if seq.atoms.len() == 1 && seq.lb.is_empty() && seq.rb.is_empty() {
                    simplify_further = true;
                }
                if seq.atoms.is_empty() {
                    self.insert_psb(seq.try_into().unwrap());
                } else {
                    self.irreducibles.insert(seq);
                }
            }
        }
        for psb in old_atom_sequents.into_iter() {
            if let Some(psb) = psb.substitute_top_bot(&require_top, &require_bot) {
                self.insert_psb(psb);
            }
        }
        for ps in old_conj_disj.into_iter() {
            if let Some(ps) = ps.substitute_top_bot(&require_top, &require_bot) {
                self.insert_ps(ps);
            }
        }

        if simplify_further {
            self.unifiability_simplify_empty();
        }
    }
}

impl TryFrom<ClauseWaiting> for ClauseAtoms {
    type Error = ClauseWaiting;
    fn try_from(value: ClauseWaiting) -> Result<Self, Self::Error> {
        if !value.conj_disj_sequents.is_empty() {
            Err(value)
        } else {
            Ok(ClauseAtoms {
                irreducibles: value.irreducibles,
                atom_sequents: value.atom_sequents.into_iter().collect(),
            })
        }
    }
}

impl From<ClauseAtoms> for ClauseWaiting {
    fn from(value: ClauseAtoms) -> Self {
        ClauseWaiting {
            irreducibles: value.irreducibles.into_iter().collect(),
            atom_sequents: value.atom_sequents.into_iter().collect(),
            conj_disj_sequents: BTreeSet::new(),
        }
    }
}

impl From<ClauseIrred> for ClauseWaiting {
    fn from(value: ClauseIrred) -> Self {
        From::<ClauseAtoms>::from(value.into())
    }
}

#[derive(Clone, Debug, Eq, PartialEq, PartialOrd, Ord)]
pub struct ClauseAtoms {
    pub irreducibles: BTreeSet<PSI>,

    // Sequents that might not contain atoms
    pub atom_sequents: Vec<PSB>,
}

impl ClauseAtoms {
    pub fn to_nnf(&self) -> NNF {
        Into::<ClauseWaiting>::into(self.clone()).to_nnf()
    }

    /// Returns `Some(false)` if the clause contains an empty sequent.
    /// Returns `Some(true)` if the clause is empty
    /// Returns `None` otherwise
    pub fn simple_check_validity(&self) -> Option<bool> {
        if self.irreducibles.is_empty() && self.atom_sequents.is_empty() {
            return Some(true);
        }
        for psi in self.irreducibles.iter() {
            if psi.is_empty() {
                return Some(false);
            }
        }
        for psb in self.atom_sequents.iter() {
            if psb.is_empty() {
                return Some(false);
            }
        }
        None
    }

    pub fn simple_check_unifiability(&self) -> Option<bool> {
        if let Some(b) = self.simple_check_validity() {
            return Some(b);
        }

        // Edge case:
        // If the clause contains any atom-sequents. Then we can't tell.
        if !self.atom_sequents.is_empty() {
            return None;
        }

        // Check whether the left/right atoms are all disjoint.
        let mut atom_iter = self.irreducibles.iter().map(|psi| &psi.atoms);

        let mut atoms = {
            if let Some(atoms) = atom_iter.next() {
                atoms.clone()
            } else {
                return None;
            }
        };
        for other_atom in atom_iter {
            for (k, v) in atoms.clone().iter() {
                if other_atom.get(k) != Some(v) {
                    atoms.remove(k);
                }
            }
        }

        if !atoms.is_empty() {
            // We found some intersection, so * -> top or * -> bot are unifiers.
            return Some(true);
        }

        None
    }

    pub fn process_atoms_step(self) -> ProcessAtomsResult {
        // Shortcut if the clause has no `atom_sequents`.
        if self.atom_sequents.is_empty() {
            // `clause` is irreducible

            let clause: ClauseIrred = self.try_into().unwrap();
            let clause = clause.simplify();

            // if the clause is trivially valid, the whole clause set is valid
            // if the clause is trivially contradictory, we can omit this clause
            match clause.simple_check_validity() {
                Some(true) => {
                    return ProcessAtomsResult::Valid;
                }
                Some(false) => {
                    return ProcessAtomsResult::Contradictory;
                }
                None => {
                    return ProcessAtomsResult::Irred(clause);
                }
            }
        }

        // first process the easy atom sequents.
        let clause = ClauseWaiting::from(self);
        let clause = clause.process_easy_boxes();
        let mut clause: ClauseAtoms = clause.process_conjs();

        // Shortcut, if the clause is valid or contradictory.
        if let Some(b) = clause.simple_check_validity() {
            if b {
                return ProcessAtomsResult::Valid;
            } else {
                // This clause is contradictory, so ignore it.
                return ProcessAtomsResult::Contradictory;
            }
        }

        // Shortcut if the clause has no `atom_sequents`.
        if clause.atom_sequents.is_empty() {
            return ProcessAtomsResult::Irred(clause.try_into().unwrap());
        }

        let waiting_atoms_sequent = clause.atom_sequents.pop().unwrap();

        // It is possible, that one of the newly generated sequents will be "trivially" true.
        // In such a case it suffices to add only the rest of the clause.
        let mut delta_waiting_conj: Vec<ClauseWaiting> =
            Vec::with_capacity(waiting_atoms_sequent.rb.len());

        let mut right_box_iter = waiting_atoms_sequent.rb.into_iter();
        // Put aside an element, so we can treat it last, and don't have to clone stuff.
        let right_box_aside = right_box_iter.next();

        for delta in right_box_iter {
            // Write down the new sequent
            let new_psw = PSW {
                // recall that `waiting_atoms_sequent.atoms` is empty
                atoms: BTreeMap::new(),
                lb: BTreeSet::new(),
                rb: BTreeSet::new(),
                ld: Vec::new(),
                rc: Vec::new(),
                // the currently boxed left formulae, but without their boxes
                lw: waiting_atoms_sequent.lb.iter().cloned().collect(),
                rw: vec![delta],
            };

            if let Some(new_ps) = new_psw.into_ps() {
                // Add the sequent to the current clause.
                let mut new_clause: ClauseWaiting = clause.clone().into();
                new_clause.conj_disj_sequents.insert(new_ps);
                delta_waiting_conj.push(new_clause);
            } else {
                // If the new sequent is "trivially" valid, then the
                // atom-sequent we started with is also valid, so we
                // can forget about it and simply return the `clause`.
                return ProcessAtomsResult::Clause(clause);
            }
        }

        if let Some(delta) = right_box_aside {
            // Write down the new sequent
            let new_psw = PSW {
                // recall that `waiting_atoms_sequent.atoms` is empty
                atoms: BTreeMap::new(),
                lb: BTreeSet::new(),
                rb: BTreeSet::new(),
                ld: Vec::new(),
                rc: Vec::new(),
                // the currently boxed left formulae, but without their boxes
                lw: waiting_atoms_sequent.lb.into_iter().collect(),
                rw: vec![delta],
            };

            if let Some(new_ps) = new_psw.into_ps() {
                // Add the sequent to the current clause.
                let mut new_clause: ClauseWaiting = clause.into();
                new_clause.conj_disj_sequents.insert(new_ps);
                delta_waiting_conj.push(new_clause);
            } else {
                // If the new sequent is "trivially" valid, then the
                // atom-sequent we started with is also valid, so we
                // can forget about it and simply return the `clause`.
                return ProcessAtomsResult::Clause(clause);
            }
        }

        ProcessAtomsResult::Waiting(delta_waiting_conj)
    }
}

/// An irreducible clause, to which the cut rule has been applied, without significant effect.
#[derive(Clone, Debug, Eq, PartialEq, PartialOrd, Ord)]
pub struct ClauseCut {
    pub irreducibles: BTreeSet<PSI>,
}

impl From<ClauseCut> for ClauseIrred {
    fn from(value: ClauseCut) -> Self {
        ClauseIrred {
            irreducibles: value.irreducibles,
        }
    }
}

impl From<ClauseCut> for ClauseWaiting {
    fn from(value: ClauseCut) -> Self {
        Into::<ClauseIrred>::into(value).into()
    }
}

/// A clause that only consists of irreducible sequents.
/// I.e. each sequent has at least one atom on each side.
#[derive(Clone, Debug, Eq, PartialEq, PartialOrd, Ord)]
pub struct ClauseIrred {
    pub irreducibles: BTreeSet<PSI>,
}

impl TryFrom<ClauseWaiting> for ClauseIrred {
    type Error = ClauseWaiting;
    fn try_from(value: ClauseWaiting) -> Result<Self, Self::Error> {
        if !value.atom_sequents.is_empty() || !value.conj_disj_sequents.is_empty() {
            Err(value)
        } else {
            Ok(ClauseIrred {
                irreducibles: value.irreducibles.into_iter().collect(),
            })
        }
    }
}

impl TryFrom<ClauseAtoms> for ClauseIrred {
    type Error = ClauseAtoms;
    fn try_from(value: ClauseAtoms) -> Result<Self, Self::Error> {
        if !value.atom_sequents.is_empty() {
            Err(value)
        } else {
            Ok(ClauseIrred {
                irreducibles: value.irreducibles.into_iter().collect(),
            })
        }
    }
}

impl From<ClauseIrred> for ClauseAtoms {
    fn from(value: ClauseIrred) -> ClauseAtoms {
        ClauseAtoms {
            irreducibles: value.irreducibles.into_iter().collect(),
            atom_sequents: Vec::new(),
        }
    }
}

impl ClauseIrred {
    fn new_contradictory() -> ClauseIrred {
        ClauseIrred {
            irreducibles: {
                let mut set = BTreeSet::new();
                set.insert(PSI::new_empty());
                set
            },
        }
    }

    fn is_empty(&self) -> bool {
        self.irreducibles.is_empty()
    }

    pub fn to_nnf(&self) -> NNF {
        NNF::And(self.irreducibles.iter().map(PSI::to_nnf).collect())
    }

    pub fn simplify(mut self) -> ClauseIrred {
        let mut new_sequents: BTreeSet<PSI> = BTreeSet::new();

        for mut sequent in self.irreducibles.into_iter() {
            // Simplify the sequent.
            sequent.simplify();

            // Check whether the sequent is trivially valid or contradictory
            match sequent.simple_check_validity() {
                Some(true) => {
                    continue;
                }
                Some(false) => {
                    return ClauseIrred::new_contradictory();
                }
                None => {}
            };

            // Check for the following situation:
            // An existing sequent has "p, Γ⇒Δ" and the new sequent has "Γ⇒p,Δ",
            // or the other way around, or with a boxed formula instead of an atom.
            //TODO:

            // Check for redundant sequents.
            // If two sequents have the same premise/conclusion but their
            // conclusions/premises are subsets of eachother, we can
            // remove the sequent with the larger set of
            // conclusions/premises.

            let mut remove_current_sequent: bool = false;

            new_sequents.drain_filter(|other_sequent| {
                // return true, if `other_sequent` is the larger sequent to remove it.
                // return false otherwise to keep that `other_sequent` in the set.
                match PSI::check_subset(other_sequent, &sequent) {
                    Some(LeftRight::Left) => {
                        remove_current_sequent = true;
                        false
                    }
                    Some(LeftRight::Right) => true,
                    None => false,
                }
            });

            if remove_current_sequent {
                continue;
            }

            new_sequents.insert(sequent);
        }

        self.irreducibles = new_sequents;

        //TODO: Replace any instance of `φ⇒ψ,θ ; φ,ψ⇒θ ; φ,θ⇒ψ` with `φ⇒ψ ; φ⇒θ`
        // This currently only treats the special case with `φ := p`, `ψ := ⌷p` and `θ := ⌷~p`.
        // It replaces these three sequents with `p ⇒ ⌷Bot` because this holds in this case.
        let test_set: BTreeSet<PSI> = {
            let mut set = BTreeSet::new();
            set.insert(PSI {
                atoms: {
                    let mut map = BTreeMap::new();
                    map.insert(0, LeftRight::Left);
                    map
                },
                lb: BTreeSet::new(),
                rb: {
                    let mut set = BTreeSet::new();
                    set.insert(NNF::AtomPos(0));
                    set.insert(NNF::AtomNeg(0));
                    set
                },
            });
            set.insert(PSI {
                atoms: {
                    let mut map = BTreeMap::new();
                    map.insert(0, LeftRight::Left);
                    map
                },
                lb: {
                    let mut set = BTreeSet::new();
                    set.insert(NNF::AtomNeg(0));
                    set
                },
                rb: {
                    let mut set = BTreeSet::new();
                    set.insert(NNF::AtomPos(0));
                    set
                },
            });
            set.insert(PSI {
                atoms: {
                    let mut map = BTreeMap::new();
                    map.insert(0, LeftRight::Left);
                    map
                },
                lb: {
                    let mut set = BTreeSet::new();
                    set.insert(NNF::AtomPos(0));
                    set
                },
                rb: {
                    let mut set = BTreeSet::new();
                    set.insert(NNF::AtomNeg(0));
                    set
                },
            });
            set
        };

        if self.irreducibles.is_superset(&test_set) {
            for seq in test_set.iter() {
                self.irreducibles.remove(seq);
            }
            self.irreducibles.insert(PSI {
                atoms: {
                    let mut map = BTreeMap::new();
                    map.insert(0, LeftRight::Left);
                    map
                },
                lb: BTreeSet::new(),
                rb: {
                    let mut set = BTreeSet::new();
                    set.insert(NNF::Bot);
                    set
                },
            });
        }

        //TODO: Replace any instance of `φ⇒ψ ; φ,ψ⇒θ` with `φ⇒θ`.
        // This currently only treats the special case with `φ := p`, `ψ := ⌷Bot` and `θ := Bot`.
        let test_set: BTreeSet<PSI> = {
            let mut set = BTreeSet::new();
            set.insert(PSI {
                atoms: {
                    let mut map = BTreeMap::new();
                    map.insert(0, LeftRight::Left);
                    map
                },
                rb: BTreeSet::new(),
                lb: {
                    let mut set = BTreeSet::new();
                    set.insert(NNF::Bot);
                    set
                },
            });
            set.insert(PSI {
                atoms: {
                    let mut map = BTreeMap::new();
                    map.insert(0, LeftRight::Left);
                    map
                },
                lb: {
                    let mut set = BTreeSet::new();
                    set.insert(NNF::Bot);
                    set
                },
                rb: BTreeSet::new(),
            });
            set
        };

        if self.irreducibles.is_superset(&test_set) {
            for seq in test_set.iter() {
                self.irreducibles.remove(seq);
            }
            self.irreducibles.insert(PSI {
                atoms: {
                    let mut map = BTreeMap::new();
                    map.insert(0, LeftRight::Left);
                    map
                },
                lb: BTreeSet::new(),
                rb: BTreeSet::new(),
            });
        }

        self
    }

    /// Thoroughly checks the validity of this clause using the validity checker.
    pub fn check_valid(&self) -> bool {
        self.to_nnf().is_valid()
    }

    fn unifiability_simplify_empty(mut self) -> Result<ClauseIrred, ClauseAtoms> {
        // if there is a sequent of the form `p ⇒ ø`, then replace `p` everywhere by `⊥`.
        // if there is a sequent of the form `ø ⇒ p`, then replace `p` everywhere by `T`.

        let mut require_top: BTreeSet<NnfAtom> = BTreeSet::new();
        let mut require_bot: BTreeSet<NnfAtom> = BTreeSet::new();

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
            return Ok(self);
        }

        // If the two sets overlap, then we are contradictory.
        if !require_top.is_disjoint(&require_bot) {
            return Ok(ClauseIrred::new_contradictory());
        }

        // is true, if further simplifications are possible
        let mut simplify_further = false;

        let old_irreducibles = std::mem::take(&mut self.irreducibles);
        let mut new_atom_sequents = BTreeSet::new();

        // Perform the substitutions. Because the substitutions are so
        // simple, a lot of simplifications can happen now.
        for sequent in old_irreducibles.into_iter() {
            if let Some(seq) = sequent.substitute_top_bot(&require_top, &require_bot) {
                if seq.atoms.len() == 1 && seq.lb.is_empty() && seq.rb.is_empty() {
                    simplify_further = true;
                }
                if seq.atoms.is_empty() {
                    new_atom_sequents.insert(seq.try_into().unwrap());
                } else {
                    self.irreducibles.insert(seq);
                }
            }
        }

        if new_atom_sequents.is_empty() {
            if simplify_further {
                return self.unifiability_simplify_empty();
            } else {
                return Ok(self);
            }
        }

        Err(ClauseAtoms {
            irreducibles: self.irreducibles,
            atom_sequents: new_atom_sequents.into_iter().collect(),
        })
    }

    /// Whenever a variable occurs freely on the same side, in each sequent in which it occurs,
    /// then bottom or top are unifiers for this variable and all
    /// sequents in which it occurs can be removed.
    fn unifiability_simplify_free_atoms(&mut self) {
        #[derive(Eq, PartialEq)]
        enum Status {
            // if the rule doesn't apply to this atom
            NonMatching,
            MatchesLeft,
            MatchesRight,
        }
        let mut candidates: BTreeMap<NnfAtom, Status> = BTreeMap::new();
        for seq in self.irreducibles.iter() {
            let mut atoms_here = BTreeSet::new();
            for (atom, lr) in seq.atoms.iter() {
                match (candidates.get(atom), lr) {
                    (Some(Status::NonMatching), _) => {
                        continue;
                    }
                    (Some(Status::MatchesLeft), LeftRight::Right)
                    | (Some(Status::MatchesRight), LeftRight::Left) => {
                        candidates.insert(*atom, Status::NonMatching);
                        continue;
                    }
                    (_, LeftRight::Left) => {
                        candidates.insert(*atom, Status::MatchesLeft);
                        atoms_here.insert(atom);
                    }
                    (_, LeftRight::Right) => {
                        candidates.insert(*atom, Status::MatchesRight);
                        atoms_here.insert(atom);
                    }
                }
            }

            // Now step through all variables that occur boxed, and if
            // any of them does not occur in the atoms lists, then
            // remove them.
            for occurring_atom in seq
                .lb
                .iter()
                .flat_map(NNF::iter_atoms)
                .chain(seq.rb.iter().flat_map(NNF::iter_atoms))
            {
                if !atoms_here.contains(&occurring_atom) {
                    candidates.insert(occurring_atom, Status::NonMatching);
                }
            }
        }

        let candidates: Vec<NnfAtom> = candidates
            .into_iter()
            .filter_map(|(atom, status)| {
                if status == Status::NonMatching {
                    None
                } else {
                    Some(atom)
                }
            })
            .collect();

        // Now remove all sequents which contain any `candidates` that match.
        self.irreducibles.retain(|sequent| {
            for candidate in candidates.iter() {
                if sequent.atoms.contains_key(candidate) {
                    return false;
                }
            }
            true
        });
    }

    //TODO: This code is probably not correct. Re-implement it for
    // `ClauseIrred` or `ClauseCut`.
    /*
    #[allow(dead_code)]
    fn unifiability_simplify_box_bot(&mut self) {
        // If there are clauses of the form `p ⇒ ⌷φ` and `p ⇒ ⌷~φ`
        // then `p` must have the form `⌷\bot \land p`.

        // First search for the relevant atoms.
        // maps to `None` if the simplification applies to that atom.
        let mut atoms: BTreeMap<NnfAtom, Option<Vec<NNF>>> = BTreeMap::new();

        for sequent in self.irreducibles.iter() {
            if sequent.atoms.len() != 1 || !sequent.lb.is_empty() || sequent.rb.len() != 1 {
                continue;
            }
            let (atom, place) = sequent.atoms.iter().next().unwrap();
            if *place == LeftRight::Right {
                // The atom is on the right.
                continue;
            }
            if atoms.get(atom) == Some(&None) {
                // We already know that this atom can be simplified.
                continue;
            }
            let formula = sequent.rb.first().unwrap();

            // If there are some stored formulae, check for equivalence (to the negation).
            let mut found_match = false;
            if let Some(Some(formulae)) = atoms.get(atom) {
                let formula_neg = formula.neg();
                for other_formula in formulae.iter() {
                    if NNF::equiv_dec(other_formula, &formula_neg) {
                        found_match = true;
                        break;
                    }
                }
            }
            if found_match {
                atoms.insert(*atom, None);
            } else {
                // Insert the formula into the set.
                if let Some(Some(formulae)) = atoms.get_mut(atom) {
                    formulae.push(formula.clone());
                } else {
                    atoms.insert(*atom, Some(vec![formula.clone()]));
                }
            }
        }

        // Now replace all atoms `p` in `atoms` which get mapped to
        // `None` by `p /\ [] \bot` in the whole clause.
        let substitution: BTreeMap<NnfAtom, NNF> = atoms
            .into_iter()
            .filter_map(|(atom, value)| {
                if value.is_some() {
                    None
                } else {
                    Some((
                        atom,
                        NNF::And(vec![NNF::NnfBox(Box::new(NNF::Bot)), NNF::AtomPos(atom)]),
                    ))
                }
            })
            .collect();
        self.substitute(&substitution)
    }
    */

    /// A sequent of the form `⌷p ⇒ p` has only `T` as unifier.
    /// So whenever we find a sequent of this form, substitute `p` with `T`.
    fn unifiability_simplify_box_p_impl_p(self) -> Result<ClauseIrred, ClauseWaiting> {
        let mut true_variables: BTreeMap<NnfAtom, NNF> = BTreeMap::new();
        for sequent in self.irreducibles.iter() {
            if !sequent.rb.is_empty() {
                continue;
            }
            if sequent.lb.len() != 1 {
                continue;
            }
            if sequent.atoms.len() != 1 {
                continue;
            }
            if let Some(NNF::AtomPos(i)) = sequent.lb.iter().next() {
                if sequent.atoms.get(i) == Some(&LeftRight::Right) {
                    true_variables.insert(*i, NNF::Top);
                }
            }
        }
        if true_variables.is_empty() {
            return Ok(self);
        }
        let mut clause: ClauseWaiting = self.into();
        clause.substitute(&true_variables);
        Err(clause)
    }

    /// If `p⇒φ ; φ⇒p` occurs, with `φ` not containing `p`, then substitute `p` by `φ`.
    fn unifiability_simplify_equivalents(mut self) -> Result<ClauseIrred, ClauseWaiting> {
        // First create iterators of sequents which have on their left/right only a free atom.

        let left_atom_sequents = self.irreducibles.iter().filter_map(|psi| {
            let left_atoms = psi.left_atoms();
            if psi.lb.is_empty() && psi.rb.len() == 1 && left_atoms.len() == 1 {
                Some((
                    psi,
                    *left_atoms.iter().next().unwrap(),
                    psi.to_nnf_lr().1.simpl(),
                ))
            } else {
                None
            }
        });
        let right_atom_sequents = self.irreducibles.iter().filter_map(|psi| {
            let right_atoms = psi.right_atoms();
            if psi.rb.is_empty() && psi.lb.len() == 1 && right_atoms.len() == 1 {
                Some((
                    psi,
                    *right_atoms.iter().next().unwrap(),
                    psi.to_nnf_lr().0.simpl(),
                ))
            } else {
                None
            }
        });

        // Now "intersect" the two iterators
        // This has n^2 time complexity...

        let mut data: Option<(BTreeMap<u8, NNF>, PSI, PSI)> = None;

        'a: for (left_psi, left_atom, left_right_formula) in left_atom_sequents {
            for (right_psi, right_atom, right_left_formula) in right_atom_sequents.clone() {
                if left_atom == right_atom && left_right_formula == right_left_formula {
                    // An assert here, because it is noteworthy, if
                    // some other formula appears in this situation.
                    //assert_eq!(left_right_formula, NNF::boxx(NNF::Bot));
                    // We found a match. Remove `left_psi` and `right_psi` and perform the substitution of `left_atom` by `left_right_formula`.

                    let mut substitution = BTreeMap::new();
                    substitution.insert(left_atom, left_right_formula);
                    data = Some((substitution, left_psi.clone(), right_psi.clone()));
                    break 'a;
                }
            }
        }

        if let Some((substitution, left_psi, right_psi)) = data {
            self.irreducibles.remove(&left_psi);
            self.irreducibles.remove(&right_psi);

            let mut clause: ClauseWaiting = self.into();
            clause.substitute(&substitution);
            Err(clause)
        } else {
            // no substitution has been performed
            Ok(self)
        }
    }

    fn unifiability_simplify_p_impl_box_bot(&mut self) {
        // if the sequent `p ⇒ ⌷bot` occurs in the clause,
        // then all (other) sequents of the form `p, Γ ⇒ Δ, ⌷φ` can be
        // removed.

        let mut atoms_implying_box_bot: BTreeSet<NnfAtom> = BTreeSet::new();

        let test_rb = {
            let mut set = BTreeSet::new();
            set.insert(NNF::Bot);
            set
        };

        for sequent in self.irreducibles.iter() {
            if sequent.lb.is_empty() && sequent.atoms.len() == 1 && sequent.rb == test_rb {
                if let (atom, LeftRight::Left) = sequent.atoms.iter().next().unwrap() {
                    atoms_implying_box_bot.insert(*atom);
                }
            }
        }

        let mut psi: PSI = PSI {
            atoms: BTreeMap::new(),
            lb: BTreeSet::new(),
            rb: test_rb,
        };

        if atoms_implying_box_bot.is_empty() {
            return;
        }

        if cfg!(debug) {
            for atom in atoms_implying_box_bot.iter() {
                psi.atoms.clear();
                psi.atoms.insert(*atom, LeftRight::Left);
                assert!(self.irreducibles.contains(&psi));
            }
        }

        self.irreducibles.drain_filter(|sequent| {
            // return true to remove the element. return false to keep it.
            let left_atoms = sequent.left_atoms();
            if !atoms_implying_box_bot.is_disjoint(&left_atoms) && !sequent.rb.is_empty() {
                // We could remove this sequent now.
                // But first make sure that it isn't the sequent with `p⇒⌷bot`.
                if sequent.lb.is_empty() && sequent.atoms.len() == 1 && sequent.rb.len() == 1 {
                    // We already know that one of the atoms in
                    // `atoms_implying_box_bot` must be in
                    // `left_atoms`.
                    return NNF::Bot != *sequent.rb.iter().next().unwrap();
                } else {
                    return true;
                }
            }
            false
        });

        if cfg!(debug) {
            for atom in atoms_implying_box_bot.iter() {
                psi.atoms.clear();
                psi.atoms.insert(*atom, LeftRight::Left);
                assert!(self.irreducibles.contains(&psi));
            }
        }
    }

    /// Does not perform the cut-rule, because that one may cause loops.
    //TODO: Deal with `p ⇒ φ ; φ ⇒ p` with `φ` variable-free, by substituting `p` by `φ`.
    pub fn unifiability_simplify(self) -> Result<ClauseIrred, Result<ClauseAtoms, ClauseWaiting>> {
        let clause_irred = match self.simplify().unifiability_simplify_empty() {
            Ok(ci) => ci,
            Err(ca) => return Err(Ok(ca)),
        };
        let clause_irred = match clause_irred.unifiability_simplify_box_p_impl_p() {
            Ok(ci) => ci,
            Err(cw) => {
                return Err(Err(cw));
            }
        };
        let mut clause_irred = match clause_irred.unifiability_simplify_equivalents() {
            Ok(ci) => ci,
            Err(cw) => {
                return Err(Err(cw));
            }
        };
        clause_irred.unifiability_simplify_p_impl_box_bot();
        clause_irred.unifiability_simplify_free_atoms();
        Ok(clause_irred)
    }

    /// Returns `Some(false)` if the clause contains an empty
    /// sequent. i.e. the clause is contradictory.
    /// Returns `Some(true)` if the clause is empty. i.e. the clause
    /// is valid.
    /// Returns `None` otherwise
    pub fn simple_check_validity(&self) -> Option<bool> {
        if self.is_empty() {
            return Some(true);
        }
        for sequent in self.irreducibles.iter() {
            if sequent.is_empty() {
                return Some(false);
            }
        }
        None
    }

    pub fn simple_check_unifiability(&self) -> Option<bool> {
        if let Some(b) = self.simple_check_validity() {
            return Some(b);
        }

        // Check whether the left/right atoms are all disjoint.
        let mut atom_iter = self.irreducibles.iter().map(|psi| &psi.atoms);

        let mut atoms = {
            if let Some(atoms) = atom_iter.next() {
                atoms.clone()
            } else {
                return None;
            }
        };
        for other_atom in atom_iter {
            for (k, v) in atoms.clone().iter() {
                if other_atom.get(k) != Some(v) {
                    atoms.remove(k);
                }
            }
        }
        if !atoms.is_empty() {
            // We found some intersection, so * -> top or * -> bot are unifiers.
            return Some(true);
        }

        None
    }

    pub fn display_beautiful(&self) -> ClauseIrredDisplayBeautiful {
        ClauseIrredDisplayBeautiful { clause: self }
    }

    pub fn display_spartacus(&self) -> ClauseIrredDisplaySpartacus {
        ClauseIrredDisplaySpartacus { clause: self }
    }

    /// Take care with this rule, because it may cause loops.
    pub fn unifiability_simplify_perform_cut_rule(mut self) -> Result<ClauseCut, ClauseAtoms> {
        // For all sequents `sequent`, for all variables `p` on the left of this sequent,
        // Search for other sequents with `p` on the right. Then perform
        // cut on these two sequents and this variable. Add the resulting sequent to a waiting list.
        // In the end add the waiting list to the `clause` and return.

        //TODO: This loop is inefficient :
        // In the next iteration, we have forgotten, which sequents were already matched together.
        // This way we do lots of duplicate work.
        let mut i: usize = 0;

        loop {
            if i != 0 && (i % 100 == 0) {
                eprintln!("{}", i);
            }
            if i > 500 {
                eprintln!("{}", self.display_beautiful());
            }
            if i > 10_000 {
                panic!();
            }
            i += 1;

            let mut new_irred_sequents: BTreeSet<PSI> = BTreeSet::new();
            let mut new_box_sequents: Vec<PSB> = Vec::new();

            for left_sequent in self.irreducibles.iter() {
                // iterate over all the left atoms of `sequent`
                for i in left_sequent
                    .atoms
                    .iter()
                    .filter_map(|(i, left_right)| match left_right {
                        LeftRight::Left => Some(i),
                        LeftRight::Right => None,
                    })
                {
                    // now find all sequents with `i` on the right
                    for right_sequent in self.irreducibles.iter() {
                        if right_sequent.atoms.get(i) != Some(&LeftRight::Right) {
                            continue;
                        }
                        // create the new sequent as a combination of
                        // `left_sequent` and `right_sequent` where `i` is left out.
                        // And if an atom appears both left and right, then the new
                        // sequent becomes trivial, so skip that.

                        // The new sets of atoms
                        let mut new_atoms = left_sequent.atoms.clone();
                        new_atoms.remove(i);

                        for (j, lr) in right_sequent.atoms.iter() {
                            // skip `j` if it is `i`, otherwise we don't cut.
                            if j == i {
                                continue;
                            }
                            match new_atoms.insert(*j, *lr) {
                                None => {}
                                Some(prev_lr) => {
                                    if prev_lr != *lr {
                                        // The sequent is trivial
                                        continue;
                                    }
                                }
                            }
                        }

                        // It is important, that we don't just append the vectors to eachother.
                        // This would create way too many
                        // duplicates. Using the `BTreeSet` we can
                        // check for uniqueness.
                        let mut new_lb: BTreeSet<NNF> = BTreeSet::new();
                        new_lb.extend(left_sequent.lb.iter().cloned());
                        new_lb.extend(right_sequent.lb.iter().cloned());
                        let mut new_rb: BTreeSet<NNF> = BTreeSet::new();
                        new_rb.extend(left_sequent.rb.iter().cloned());
                        new_rb.extend(right_sequent.rb.iter().cloned());

                        let new_sequent: PSI = PSI {
                            atoms: new_atoms,
                            lb: new_lb,
                            rb: new_rb,
                        };

                        // Now try transforming the `new_sequent` into a `PSB`.
                        // If that doesn't work, check whether it is already present in `clause`

                        match new_sequent.try_into() {
                            Ok(new_sequent_psb) => {
                                new_box_sequents.push(new_sequent_psb);
                            }
                            Err(new_sequent) => {
                                if !self.irreducibles.contains(&new_sequent) {
                                    new_irred_sequents.insert(new_sequent);
                                }
                            }
                        }
                    }
                }
            }

            // Now return a clause, without loosing any information.
            let new_irred_sequents_is_empty = new_irred_sequents.is_empty();
            self.irreducibles.append(&mut new_irred_sequents);
            if !new_box_sequents.is_empty() {
                let clause_atom = ClauseAtoms {
                    irreducibles: self.irreducibles,
                    atom_sequents: new_box_sequents,
                };
                return Err(clause_atom);
            }

            if new_irred_sequents_is_empty {
                return Ok(ClauseCut {
                    irreducibles: self.irreducibles,
                });
            }
        }
    }
}

#[allow(dead_code)]
fn arb_clause_waiting_conj() -> impl Strategy<Value = ClauseWaiting> {
    (
        prop::collection::btree_set(arb_psi(), 0..3),
        prop::collection::btree_set(arb_psb(), 0..3),
        prop::collection::btree_set(arb_ps(), 0..3),
    )
        .prop_map(
            |(irreducibles, atom_sequents, conj_disj_sequents)| ClauseWaiting {
                irreducibles,
                atom_sequents,
                conj_disj_sequents,
            },
        )
}

#[allow(dead_code)]
fn arb_clause_atom() -> impl Strategy<Value = ClauseAtoms> {
    (
        prop::collection::btree_set(arb_psi(), 0..10),
        prop::collection::vec(arb_psb(), 0..10),
    )
        .prop_map(|(irreducibles, atom_sequents)| ClauseAtoms {
            irreducibles,
            atom_sequents,
        })
}

#[allow(dead_code)]
fn arb_clause_irred() -> impl Strategy<Value = ClauseIrred> {
    prop::collection::btree_set(arb_psi(), 0..3)
        .prop_map(|irreducibles| ClauseIrred { irreducibles })
}

proptest! {
 #[test]
 fn simplify_equiv(clause in arb_clause_irred()) {
     let clause_simplify = clause.clone().simplify();
     assert!(NNF::equiv_dec(&clause.to_nnf(), &clause_simplify.to_nnf()));
 }
}

pub struct ClauseSetDisplayBeautiful<'a> {
    clause_set: &'a ClauseSet,
}

impl<'a> std::fmt::Display for ClauseSetDisplayBeautiful<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{{")?;

        write!(f, " cut_clauses: ")?;
        for clause in self.clause_set.cut_clauses.iter() {
            write!(
                f,
                " ; {} ; ",
                ClauseIrred {
                    irreducibles: clause.irreducibles.clone()
                }
                .display_beautiful()
            )?;
        }

        write!(f, " irreducibles: ")?;
        for clause in self.clause_set.irreducibles.iter() {
            write!(f, " ; {} ; ", clause.display_beautiful())?;
        }

        write!(f, " waiting_atoms: ")?;
        for clause in self.clause_set.waiting_atoms.iter() {
            write!(
                f,
                " ; {} ; ",
                Into::<ClauseWaiting>::into(clause.clone()).display_beautiful()
            )?;
        }

        write!(f, " waiting_cd: ")?;
        for clause in self.clause_set.waiting_conj_disj.iter() {
            write!(f, " ; {} ; ", clause.display_beautiful())?;
        }

        write!(f, "}}")
    }
}

pub struct ClauseWaitingDisplayBeautiful<'a> {
    clause: &'a ClauseWaiting,
}

impl<'a> std::fmt::Display for ClauseWaitingDisplayBeautiful<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for seq in self.clause.irreducibles.iter() {
            write!(
                f,
                " , {}",
                Into::<PSW>::into(seq.clone()).display_beautiful()
            )?;
        }
        for seq in self.clause.atom_sequents.iter() {
            write!(
                f,
                " , {}",
                Into::<PSW>::into(Into::<PSI>::into(seq.clone())).display_beautiful()
            )?;
        }
        for seq in self.clause.conj_disj_sequents.iter() {
            write!(
                f,
                " , {}",
                Into::<PSW>::into(seq.clone()).display_beautiful()
            )?;
        }
        Ok(())
    }
}

pub struct ClauseIrredDisplayBeautiful<'a> {
    clause: &'a ClauseIrred,
}

impl<'a> std::fmt::Display for ClauseIrredDisplayBeautiful<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut sequent_iter = self.clause.irreducibles.iter();

        if let Some(seq) = sequent_iter.next() {
            write!(f, "{}", Into::<PSW>::into(seq.clone()).display_beautiful())?;
        } else {
            write!(f, "⊤")?;
        }
        for seq in sequent_iter {
            write!(
                f,
                " , {}",
                Into::<PSW>::into(seq.clone()).display_beautiful()
            )?;
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
            NNF::And(
                self.clause
                    .irreducibles
                    .iter()
                    .cloned()
                    .map(Into::into)
                    .map(|x: PSI| x.to_nnf())
                    .collect()
            )
            .display_spartacus()
        )
    }
}

#[derive(Debug)]
pub struct ClauseSet {
    pub cut_clauses: BTreeSet<ClauseCut>,
    pub irreducibles: BTreeSet<ClauseIrred>,
    pub waiting_atoms: Vec<ClauseAtoms>,
    pub waiting_conj_disj: Vec<ClauseWaiting>,
}

impl ClauseSet {
    pub fn display_beautiful(&self) -> ClauseSetDisplayBeautiful {
        ClauseSetDisplayBeautiful { clause_set: self }
    }
    pub fn from_clause(clause: ClauseWaiting) -> ClauseSet {
        ClauseSet::from_clause_vec(vec![clause])
    }

    /// The clause set is irreducible, if the cut-rule has been applied to all sequents.
    pub fn is_irred(&self) -> bool {
        self.irreducibles.is_empty()
            && self.waiting_atoms.is_empty()
            && self.waiting_conj_disj.is_empty()
    }

    /// Creates an empty (and thus unsatisfiable) `ClauseSet`.
    #[allow(clippy::new_without_default)]
    pub fn new() -> ClauseSet {
        ClauseSet {
            cut_clauses: BTreeSet::new(),
            irreducibles: BTreeSet::new(),
            waiting_atoms: Vec::new(),
            waiting_conj_disj: Vec::new(),
        }
    }

    pub fn from_clause_vec(clauses: Vec<ClauseWaiting>) -> ClauseSet {
        ClauseSet {
            cut_clauses: BTreeSet::new(),
            irreducibles: BTreeSet::new(),
            waiting_atoms: Vec::new(),
            waiting_conj_disj: clauses,
        }
    }

    pub fn from_nnf(nnf: NNF) -> ClauseSet {
        ClauseSet::from_clause(ClauseWaiting::from_nnf(nnf))
    }

    pub fn unifiability_simplify(&mut self) {
        let mut waiting_conj_disj: Vec<ClauseWaiting> =
            Vec::with_capacity(self.waiting_conj_disj.len());

        for clause_irred in std::mem::take(&mut self.irreducibles).into_iter() {
            match clause_irred.unifiability_simplify() {
                Ok(clause_irred) => {
                    self.irreducibles.insert(clause_irred);
                }
                Err(Ok(clause_atoms)) => {
                    self.waiting_atoms.push(clause_atoms);
                }
                Err(Err(clause_waiting)) => {
                    self.waiting_conj_disj.push(clause_waiting);
                }
            }
        }
        /*
            for clause_atom in std::mem::take(&mut self.waiting_atoms).into_iter() {
                let clause_waiting = clause_atom.unifiability_simplify();
                match TryInto::<ClauseAtoms>::try_into(clause_waiting) {
                    Err(clause_waiting) => {
                        waiting_conj_disj.push(clause_waiting);
                    }
                    Ok(clause_atoms) => match TryInto::<ClauseIrred>::try_into(clause_atoms) {
                        Err(clause_atoms) => {
                            self.waiting_atoms.push(clause_atoms);
                        }
                        Ok(clause_irred) => {
                            self.irreducibles.insert(clause_irred);
                        }
                    },
                }
            }
            for clause_waiting in self.waiting_conj_disj.iter_mut() {
                clause_waiting.unifiability_simplify();
            }
        */
        self.waiting_conj_disj.append(&mut waiting_conj_disj);
    }

    pub fn is_empty(&self) -> bool {
        self.cut_clauses.is_empty()
            && self.irreducibles.is_empty()
            && self.waiting_atoms.is_empty()
            && self.waiting_conj_disj.is_empty()
    }

    /// Removes those clauses, whose negation is valid. I.e. those
    /// clauses which are not satisfiable by Kripke models.
    /// Because these are certainly not unifiable.
    pub fn unifiability_simplify_sat(&mut self) {
        self.cut_clauses
            .drain_filter(|clause| {
                Into::<ClauseIrred>::into(clause.clone())
                    .to_nnf()
                    .neg()
                    .is_valid()
            })
            .for_each(drop);
        self.irreducibles
            .drain_filter(|clause| clause.to_nnf().neg().is_valid())
            .for_each(drop);
        self.waiting_atoms
            .drain_filter(|clause| clause.to_nnf().neg().is_valid())
            .for_each(drop);
        self.waiting_conj_disj
            .drain_filter(|clause| clause.to_nnf().neg().is_valid())
            .for_each(drop);
    }

    /// Tries to check for unifiability, without making further simplifications.
    /// Try calling `unifiability_simplify` beforehand, for better results.
    pub fn simple_check_unifiable(&self) -> Option<bool> {
        if self.is_empty() {
            return Some(false);
        }

        let mut maybe_unifiable = false;

        for clause in self.cut_clauses.iter() {
            match Into::<ClauseIrred>::into(clause.clone()).simple_check_unifiability() {
                None => {
                    maybe_unifiable = true;
                }
                Some(true) => return Some(true),
                Some(false) => {}
            }
            let clause: ClauseIrred = clause.clone().into();
            let nnf = clause.to_nnf();
            if nnf.substitute_all(&NNF::Top).is_valid() || nnf.substitute_all(&NNF::Bot).is_valid()
            {
                return Some(true);
            }
        }

        //const FIXED_UNIFIERS_TO_CHECK: [NNF; 2] = [NNF::Top, NNF::Bot];
        const FIXED_UNIFIERS_TO_CHECK: [NNF; 0] = [];

        for clause in self.irreducibles.iter() {
            match clause.simple_check_unifiability() {
                None => {
                    maybe_unifiable = true;
                }
                Some(true) => return Some(true),
                Some(false) => {}
            }
            let nnf = clause.to_nnf();
            for unif in FIXED_UNIFIERS_TO_CHECK {
                if nnf.substitute_all(&unif).is_valid() {
                    return Some(true);
                }
            }
        }
        for clause in self.waiting_atoms.iter() {
            match clause.simple_check_unifiability() {
                None => {
                    maybe_unifiable = true;
                }
                Some(true) => return Some(true),
                Some(false) => {}
            }
            let nnf = clause.to_nnf();
            for unif in FIXED_UNIFIERS_TO_CHECK {
                if nnf.substitute_all(&unif).is_valid() {
                    return Some(true);
                }
            }
        }
        for clause in self.waiting_conj_disj.iter() {
            match clause.simple_check_unifiability() {
                None => {
                    maybe_unifiable = true;
                }
                Some(true) => return Some(true),
                Some(false) => {}
            }
            let nnf = clause.to_nnf();
            for unif in FIXED_UNIFIERS_TO_CHECK {
                if nnf.substitute_all(&unif).is_valid() {
                    return Some(true);
                }
            }
        }
        if maybe_unifiable {
            None
        } else {
            Some(false)
        }
    }
}

/// `Contradictory` is maybe too strong a word, because box-bottom is
/// also "contradictory" in the sense used here, even though it is not
/// "un-satisfiable".
#[derive(Debug)]
pub enum ProcessAtomsResult {
    Valid,
    Contradictory,
    Irred(ClauseIrred),
    Clause(ClauseAtoms),
    Waiting(Vec<ClauseWaiting>),
}

use proptest::proptest;

proptest! {
    #[test]
    fn clause_process_clause_easy_boxes(clause in arb_clause_waiting_conj()) {
    let clause_is_valid = clause.to_nnf().is_valid();
    let clause_simplified = clause;
    let clause_simplified = clause_simplified.process_easy_boxes();
    assert_eq!(clause_is_valid, clause_simplified.to_nnf().is_valid());
    }

    #[test]
    fn clause_simplify(clause in arb_clause_irred()) {
    // check whether simplification preserves equivalence
    let clause_simplified = clause.clone().simplify();
    assert_eq!(clause.check_valid(), clause_simplified.clone().check_valid());
    let clause_unif_simplified = clause_simplified.clone().unifiability_simplify();
    let clause_unif_simplified_unif =
        match clause_unif_simplified {
        Ok(clause_unif_simplified) => Into::<ClauseIrred>::into(clause_unif_simplified).simple_check_unifiability(),
        Err(Ok(clause_unif_simplified)) => clause_unif_simplified.simple_check_unifiability(),
        Err(Err(clause_unif_simplified)) => clause_unif_simplified.simple_check_unifiability(),
        };
    match (clause_simplified.simple_check_unifiability(), clause_unif_simplified_unif) {
    (Some(a), Some(b)) => assert_eq!(a, b),
    (None, _) => {},
    (Some(_), _) => panic!(),
    }
    }

    #[test]
    fn atom_simple_check_validity(clause in arb_clause_atom()) {
    if let Some(b) = clause.simple_check_validity() {
        assert_eq!(clause.to_nnf().is_valid(), b);
    }
    }

    #[test]
    fn test_clause_waiting_substitute(clause in arb_clause_waiting_conj(), substitution in prop::collection::btree_map(any::<NnfAtom>(), crate::nnf::arb_nnf(), 0..10)) {
    let mut clause_copy = clause.clone();
    clause_copy.substitute(&substitution);
    let mut clause_nnf = clause.to_nnf();
    clause_nnf.substitute(&substitution);
    assert!(NNF::equiv_dec(&clause_copy.to_nnf(),
                   &clause_nnf));
    }

    /*
    #[test]
    fn clause_process_conjs(clause in arb_clause_waiting_conj()) {
    let clause_is_valid = clause.check_valid();
    let clause_atoms = clause.clone().process_conjs();
    assert!(NNF::equiv_dec(&clause.to_nnf(), &clause_atoms.to_nnf()));
    let clause_irred = ClauseSetAtoms::from_clause(clause_atoms).process_atoms();
    assert_eq!(clause_is_valid, clause_irred.to_nnf_boxed().is_valid());
    assert_eq!(clause_is_valid, clause_irred.check_valid());
    }
    */
}
