use std::collections::{BTreeMap, BTreeSet};

use proptest_derive::Arbitrary;

use super::clauses::push_if_not_exists;
use crate::nnf::{NnfAtom, NNF};

#[derive(Arbitrary, Clone, Debug, Eq, PartialEq, PartialOrd, Ord)]
pub enum LeftRight {
    Left,
    Right,
}

/// Processing Sequent Waiting
/// A sequent which has some unprocessed formulae (`lw` and `rw`)
#[allow(clippy::upper_case_acronyms)]
#[derive(Debug)]
pub struct PSW {
    // atoms (left or right)
    pub atoms: BTreeMap<NnfAtom, LeftRight>,

    // left boxes
    pub lb: Vec<NNF>,
    // right boxes
    pub rb: Vec<NNF>,

    // left disjunctions
    pub ld: Vec<Vec<NNF>>,
    // right conjunctions
    pub rc: Vec<Vec<NNF>>,

    // left waiting
    pub lw: Vec<NNF>,
    // right waiting
    pub rw: Vec<NNF>,
}

impl PSW {
    /// Create a new, contradictory sequent
    pub fn new_contradictory() -> PSW {
        PSW {
            atoms: BTreeMap::new(),
            lb: Vec::new(),
            rb: Vec::new(),
            ld: Vec::new(),
            rc: Vec::new(),
            lw: Vec::new(),
            rw: Vec::new(),
        }
    }

    /// Create a new sequent from an `NNF`
    pub fn from_nnf(phi: NNF) -> PSW {
        PSW {
            atoms: BTreeMap::new(),
            lb: Vec::new(),
            rb: Vec::new(),
            ld: Vec::new(),
            rc: Vec::new(),
            lw: Vec::new(),
            rw: vec![phi],
        }
    }

    /// Represent this sequent as `NNF` but keep the left and right
    /// half of the sequent separate
    fn to_nnf_lr(&self) -> (NNF, NNF) {
        let mut atoms_l = Vec::new();
        let mut atoms_r = Vec::new();
        for (i, lr) in self.atoms.iter() {
            match lr {
                LeftRight::Left => atoms_l.push(i),
                LeftRight::Right => atoms_r.push(i),
            }
        }

        let left = atoms_l
            .iter()
            .map(|x| NNF::AtomPos(**x))
            .chain(self.lb.iter().map(|x| NNF::NnfBox(Box::new(x.clone()))))
            .chain(self.ld.iter().cloned().map(NNF::Or))
            .chain(self.lw.iter().cloned())
            .collect();
        let right = atoms_r
            .iter()
            .map(|x| NNF::AtomPos(**x))
            .chain(self.rb.iter().map(|x| NNF::NnfBox(Box::new(x.clone()))))
            .chain(self.rc.iter().cloned().map(NNF::And))
            .chain(self.rw.iter().cloned())
            .collect();
        (NNF::And(left), NNF::Or(right))
    }

    /// Convert this sequent to an equivalent `NNF`.
    pub fn to_nnf(&self) -> NNF {
        let (l, r) = self.to_nnf_lr();
        NNF::impli(l, r).simpl_slow()
    }

    pub fn display_beautiful(&self) -> PSWDisplayBeautiful {
        PSWDisplayBeautiful { psw: self }
    }
}

pub struct PSWDisplayBeautiful<'a> {
    psw: &'a PSW,
}

impl<'a> std::fmt::Display for PSWDisplayBeautiful<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let (left, right) = self.psw.to_nnf_lr();
        write!(
            f,
            "{}⇒{}",
            left.display_beautiful(),
            right.display_beautiful()
        )
    }
}

/// Processing Sequent
#[derive(Clone, Debug, Eq, PartialEq, PartialOrd, Ord)]
pub struct PS {
    // atoms (left or right)
    pub atoms: BTreeMap<NnfAtom, LeftRight>,

    // left boxes
    pub lb: Vec<NNF>,
    // right boxes
    pub rb: Vec<NNF>,

    // left disjunctions
    pub ld: Vec<Vec<NNF>>,
    // right conjunctions
    pub rc: Vec<Vec<NNF>>,
}

/// Procesing Sequent Irreducible
#[allow(clippy::upper_case_acronyms)]
#[derive(Debug, Clone, Eq, PartialEq, PartialOrd, Ord)]
pub struct PSI {
    // atoms (left or right)
    pub atoms: BTreeMap<NnfAtom, LeftRight>,

    // left boxes
    pub lb: Vec<NNF>,
    // right boxes
    pub rb: Vec<NNF>,
}

impl TryFrom<PS> for PSI {
    type Error = PS;

    fn try_from(value: PS) -> Result<Self, Self::Error> {
        if !value.ld.is_empty() || !value.rc.is_empty() {
            Err(value)
        } else {
            Ok(PSI {
                atoms: value.atoms,
                lb: value.lb,
                rb: value.rb,
            })
        }
    }
}

impl TryFrom<PSI> for PSB {
    type Error = PSI;
    /// Is only allowed if `atoms` is empty.
    fn try_from(value: PSI) -> Result<Self, Self::Error> {
        if !value.atoms.is_empty() {
            Err(value)
        } else {
            Ok(PSB {
                lb: value.lb,
                rb: value.rb,
            })
        }
    }
}

impl PSI {
    pub fn new_empty() -> PSI {
        PSI {
            atoms: BTreeMap::new(),
            lb: Vec::new(),
            rb: Vec::new(),
        }
    }

    pub fn to_nnf(&self) -> NNF {
        Into::<PSW>::into(self.clone()).to_nnf()
    }

    pub fn is_empty(&self) -> bool {
        self.atoms.is_empty() && self.lb.is_empty() && self.rb.is_empty()
    }

    pub fn substitute(mut self, substitution: &BTreeMap<NnfAtom, NNF>) -> PSW {
        for phi in self.lb.iter_mut() {
            phi.substitute(substitution);
        }
        for phi in self.rb.iter_mut() {
            phi.substitute(substitution);
        }

        let mut lw = Vec::new();
        let mut rw = Vec::new();
        let mut atoms = BTreeMap::new();
        for (atom, lr) in self.atoms.into_iter() {
            if let Some(nnf) = substitution.get(&atom) {
                match lr {
                    LeftRight::Left => lw.push(nnf.clone()),
                    LeftRight::Right => rw.push(nnf.clone()),
                }
            } else {
                atoms.insert(atom, lr);
            }
        }

        PSW {
            atoms,
            lb: self.lb,
            rb: self.rb,
            ld: Vec::new(),
            rc: Vec::new(),
            lw,
            rw,
        }
    }

    pub fn simplify(&mut self) {
        // Remove box top from the left
        let mut i = 0;
        while i < self.lb.len() {
            if self.lb[i] != NNF::Top {
                i += 1;
            } else if self.lb[i] == NNF::Bot {
                // If there are boxes on the right, this sequent is valid.
                if !self.rb.is_empty() {
                    *self = PSI::new_valid();
                    return;
                }
                // We can remove all other boxes on the left
                self.lb.clear();
                self.lb.push(NNF::Bot);
                break;
            } else {
                self.lb.swap_remove(i);
            }
        }
        let mut i = 0;
        while i < self.rb.len() {
            if self.rb[i] == NNF::Top {
                // we found a trivial box on the right. => this sequent is valid.
                *self = PSI::new_valid();
                return;
            }
            i += 1;
        }

        for left_box in self.lb.iter() {
            for right_box in self.rb.iter() {
                if left_box == right_box {
                    *self = PSI::new_valid();
                    return;
                }
            }
        }
    }

    /// Returns `Some(true)` if the sequent is valid.
    /// Returns `Some(false)` if the sequent is contradictory.
    /// Returns `None` if it is hard to tell.
    pub fn simple_check_validity(&self) -> Option<bool> {
        if self.is_empty() {
            return Some(false);
        }
        if *self == PSI::new_valid() {
            return Some(true);
        }
        None
    }

    pub fn new_valid() -> PSI {
        PSI {
            atoms: BTreeMap::new(),
            lb: Vec::new(),
            rb: vec![NNF::Top],
        }
    }

    /// requires that the two sets don't intersect.
    /// Returns `None` if the resulting sequent is trivially valid.
    pub fn substitute_top_bot(
        mut self,
        subst_top: &BTreeSet<NnfAtom>,
        subst_bot: &BTreeSet<NnfAtom>,
    ) -> Option<PSI> {
        // if the two sets intersect, abort
        if !subst_top.is_disjoint(subst_bot) {
            unreachable!();
        }

        for prop_top in subst_top.iter() {
            match self.atoms.remove(prop_top) {
                None | Some(LeftRight::Left) => {}
                Some(LeftRight::Right) => {
                    // this sequent is trivial
                    return None;
                }
            }
        }

        for prop_bot in subst_bot.iter() {
            match self.atoms.remove(prop_bot) {
                None | Some(LeftRight::Right) => {}
                Some(LeftRight::Left) => {
                    // this sequent is trivial
                    return None;
                }
            }
        }

        // now perform the substitution on the boxed formulae
        for box_left in self.lb.iter_mut() {
            *box_left = box_left
                .clone()
                .substitute_top_bot(subst_top, subst_bot)
                .simpl();
        }
        for box_right in self.lb.iter_mut() {
            *box_right = box_right
                .clone()
                .substitute_top_bot(subst_top, subst_bot)
                .simpl();
        }
        // and simplify the boxed formulae
        Some(self)
    }
    /*
        pub fn display_latex<'a>(&'a self) -> PSIDisplayLaTeX<'a> {
            PSIDisplayLaTeX { psi: self }
        }

        pub fn display_spartacus<'a>(&'a self) -> PSIDisplaySpartacus<'a> {
            PSIDisplaySpartacus { psi: self }
        }
    */
}

impl From<PS> for PSW {
    fn from(value: PS) -> PSW {
        PSW {
            atoms: value.atoms,
            lb: value.lb,
            rb: value.rb,
            ld: value.ld,
            rc: value.rc,
            lw: Vec::new(),
            rw: Vec::new(),
        }
    }
}

impl From<PSI> for PSW {
    fn from(value: PSI) -> PSW {
        PSW {
            atoms: value.atoms,
            lb: value.lb,
            rb: value.rb,
            ld: Vec::new(),
            rc: Vec::new(),
            lw: Vec::new(),
            rw: Vec::new(),
        }
    }
}

impl PSW {
    fn into_ps_step(mut self) -> Option<PSW> {
        let mut new_left_waiting = Vec::with_capacity(self.lw.len());
        for left_waiting in self.lw.into_iter() {
            match left_waiting {
                NNF::AtomPos(i) => {
                    if let Some(LeftRight::Right) = self.atoms.insert(i, LeftRight::Left) {
                        return None;
                    }
                }
                NNF::AtomNeg(i) => {
                    if let Some(LeftRight::Left) = self.atoms.insert(i, LeftRight::Right) {
                        return None;
                    }
                }
                NNF::Bot => {
                    return None;
                }
                NNF::Top => {
                    // do nothing
                }
                NNF::And(mut conjuncts) => {
                    new_left_waiting.append(&mut conjuncts);
                }
                NNF::Or(disjuncts) => {
                    self.ld.push(disjuncts);
                }
                NNF::NnfBox(phi) => {
                    push_if_not_exists(&mut self.lb, *phi);
                }
                NNF::NnfDia(phi) => {
                    push_if_not_exists(&mut self.rb, phi.neg());
                }
            }
        }

        let mut new_right_waiting = Vec::with_capacity(self.rw.len());
        for right_waiting in self.rw.into_iter() {
            match right_waiting {
                NNF::AtomNeg(i) => {
                    if let Some(LeftRight::Right) = self.atoms.insert(i, LeftRight::Left) {
                        return None;
                    }
                }
                NNF::AtomPos(i) => {
                    if let Some(LeftRight::Left) = self.atoms.insert(i, LeftRight::Right) {
                        return None;
                    }
                }
                NNF::Bot => {
                    // do nothing
                }
                NNF::Top => {
                    return None;
                }
                NNF::And(conjuncts) => {
                    self.rc.push(conjuncts);
                }
                NNF::Or(mut disjuncts) => {
                    new_right_waiting.append(&mut disjuncts);
                }
                NNF::NnfBox(phi) => {
                    push_if_not_exists(&mut self.rb, *phi);
                }
                NNF::NnfDia(phi) => {
                    push_if_not_exists(&mut self.lb, phi.neg());
                }
            }
        }
        self.lw = new_left_waiting;
        self.rw = new_right_waiting;
        Some(self)
    }

    /// Transforms the given `PSW` into an equivalent but simpler `PS`.
    /// Returns `None` if the input is valid.
    pub fn into_ps(self) -> Option<PS> {
        if self.lw.is_empty() && self.rw.is_empty() {
            return Some(PS {
                atoms: self.atoms,
                lb: self.lb,
                rb: self.rb,
                ld: self.ld,
                rc: self.rc,
            });
        }
        // Otherwise there is more processing that needs to be done.
        self.into_ps_step()?.into_ps()
    }
}

pub enum PSConjsResult {
    NewPS(Vec<PS>),
    Irred(PSI),
    Boxes(PSB),
}

enum PSstepResult {
    Waiting(Vec<PSW>),
    Next(PSI),
}

impl PS {
    pub fn to_nnf(&self) -> NNF {
        Into::<PSW>::into(self.clone()).to_nnf()
    }

    pub fn is_empty(&self) -> bool {
        self.atoms.is_empty()
            && self.lb.is_empty()
            && self.rb.is_empty()
            && self.ld.is_empty()
            && self.rc.is_empty()
    }

    pub fn new_valid() -> PS {
        PS {
            atoms: BTreeMap::new(),
            lb: Vec::new(),
            rb: Vec::new(),
            ld: vec![vec![NNF::Bot]],
            rc: Vec::new(),
        }
    }

    pub fn substitute(&mut self, substitution: &BTreeMap<NnfAtom, NNF>) {
        for phi in self.lb.iter_mut() {
            phi.substitute(substitution);
        }
        for phi in self.rb.iter_mut() {
            phi.substitute(substitution);
        }
        for vec in self.ld.iter_mut() {
            for phi in vec.iter_mut() {
                phi.substitute(substitution);
            }
        }
        for vec in self.rc.iter_mut() {
            for phi in vec.iter_mut() {
                phi.substitute(substitution);
            }
        }

        let mut lw = Vec::new();
        let mut rw = Vec::new();
        let mut new_atoms = BTreeMap::new();
        for (atom, lr) in std::mem::take(&mut self.atoms).into_iter() {
            if let Some(nnf) = substitution.get(&atom) {
                match lr {
                    LeftRight::Left => lw.push(nnf.clone()),
                    LeftRight::Right => rw.push(nnf.clone()),
                }
            } else {
                new_atoms.insert(atom, lr);
            }
        }

        if let Some(ps) = (PSW {
            atoms: new_atoms,
            lb: std::mem::take(&mut self.lb),
            rb: std::mem::take(&mut self.rb),
            ld: std::mem::take(&mut self.ld),
            rc: std::mem::take(&mut self.rc),
            lw,
            rw,
        })
        .into_ps()
        {
            *self = ps;
        } else {
            *self = PS::new_valid();
        }
    }

    /// requires that the two sets don't intersect.
    /// Returns `None` if the resulting sequent is trivially valid.
    pub fn substitute_top_bot(
        mut self,
        subst_top: &BTreeSet<NnfAtom>,
        subst_bot: &BTreeSet<NnfAtom>,
    ) -> Option<PS> {
        // if the two sets intersect, abort
        if !subst_top.is_disjoint(subst_bot) {
            unreachable!();
        }

        for prop_top in subst_top.iter() {
            match self.atoms.remove(prop_top) {
                None | Some(LeftRight::Left) => {}
                Some(LeftRight::Right) => {
                    // this sequent is trivial
                    return None;
                }
            }
        }

        for prop_bot in subst_bot.iter() {
            match self.atoms.remove(prop_bot) {
                None | Some(LeftRight::Right) => {}
                Some(LeftRight::Left) => {
                    // this sequent is trivial
                    return None;
                }
            }
        }

        // now perform the substitution on the boxed formulae and simplify them
        for box_left in self.lb.iter_mut() {
            *box_left = box_left
                .clone()
                .substitute_top_bot(subst_top, subst_bot)
                .simpl();
        }
        for box_right in self.rb.iter_mut() {
            *box_right = box_right
                .clone()
                .substitute_top_bot(subst_top, subst_bot)
                .simpl();
            if *box_right == NNF::Top {
                // We found a box-top on the right, so this sequent is valid.
                return None;
            }
        }

        // perform the substitution on the left/right conjunctions/disjunctions
        // TODO: It is possible to perform some ad-hoc optimisations
        // here, if `conjunct` or `disjunct` are `Top` or `Bot`.
        for conjuncts in self.rc.iter_mut() {
            // TODO: Skip those `conjunct` that became `Top`.
            // If any element became `Bot` remove the whole `conjuncts`
            // If in the end no element remains, we are valid and can return `None`
            // If there is only a single element remaining, turn it
            // into a `psw` and then into a `ps` and sort it
            // correctly.
            for conjunct in conjuncts.iter_mut() {
                *conjunct = conjunct
                    .clone()
                    .substitute_top_bot(subst_top, subst_bot)
                    .simpl();
            }
        }
        for disjuncts in self.rc.iter_mut() {
            // TODO: Skip those `disjunct` that became `Bot`.
            // If any element became `Top` remove the whole `disjuncts`
            // If in the end no element remains, we are valid and can return `None`
            // If there is only a single element remaining, turn it
            // into a `psw` and then into a `ps` and sort it
            // correctly.
            for disjunct in disjuncts.iter_mut() {
                *disjunct = disjunct
                    .clone()
                    .substitute_top_bot(subst_top, subst_bot)
                    .simpl();
            }
        }
        Some(self)
    }

    /// Process those conjunctions and disjunctions which are of one
    /// element or fewer.
    pub fn process_easy_conjs(&mut self) {
        let mut i = 0;
        while i < self.rc.len() {
            let conjuncts = &self.rc[i];

            // If there are no conjuncts, the conjunction is valid, making the whole sequent valid
            if conjuncts.is_empty() {
                *self = PS::new_valid();
                return;
            }

            // If the conjunction has more than one conjunct,
            // destructuring this conjunction would cause
            // branching. This is "too complicated", so don't deal
            // with it here.
            if conjuncts.len() > 1 {
                i += 1;
                continue;
            }

            // Remove `conjuncts` from `self.rc`
            let conjuncts = self.rc.swap_remove(i);

            let new_psw: PSW = PSW {
                atoms: BTreeMap::new(),
                lb: Vec::new(),
                rb: Vec::new(),
                ld: Vec::new(),
                rc: Vec::new(),
                lw: Vec::new(),
                rw: conjuncts,
            };
            if let Some(mut ps) = new_psw.into_ps() {
                self.atoms.append(&mut ps.atoms);
                self.lb.append(&mut ps.lb);
                self.rb.append(&mut ps.rb);
                self.ld.append(&mut ps.ld);
                self.rc.append(&mut ps.rc);
            } else {
                *self = PS::new_valid();
                return;
            }
        }
        // now the same game for the left disjunctions
        let mut i = 0;
        while i < self.rc.len() {
            let disjuncts = &self.rc[i];

            // If there are no disjuncts, the disjunction is
            // contradictory, making the whole sequent valid
            if disjuncts.is_empty() {
                *self = PS::new_valid();
                return;
            }

            // If the disjunction has more than one conjunct,
            // destructuring this disjunction would cause
            // branching. This is "too complicated", so don't deal
            // with it here.
            if disjuncts.len() > 1 {
                i += 1;
                continue;
            }

            // Remove `conjuncts` from `self.ld`
            let disjuncts = self.ld.swap_remove(i);

            let new_psw: PSW = PSW {
                atoms: BTreeMap::new(),
                lb: Vec::new(),
                rb: Vec::new(),
                ld: Vec::new(),
                rc: Vec::new(),
                lw: disjuncts,
                rw: Vec::new(),
            };
            if let Some(mut ps) = new_psw.into_ps() {
                self.atoms.append(&mut ps.atoms);
                self.lb.append(&mut ps.lb);
                self.rb.append(&mut ps.rb);
                self.ld.append(&mut ps.ld);
                self.rc.append(&mut ps.rc);
            } else {
                *self = PS::new_valid();
                return;
            }
        }
    }

    pub fn process_conjs_step(mut self) -> PSConjsResult {
        self.process_easy_conjs();
        if let Some(conjuncts) = self.rc.pop() {
            let mut new_ps_vec: Vec<PS> = Vec::with_capacity(conjuncts.len());
            for conj in conjuncts.into_iter() {
                let mut new_psw: PSW = self.clone().into();
                new_psw.rw.push(conj);
                if let Some(new_ps) = new_psw.into_ps() {
                    new_ps_vec.push(new_ps);
                }
            }
            PSConjsResult::NewPS(new_ps_vec)
        } else if let Some(disjuncts) = self.ld.pop() {
            let mut new_ps_vec: Vec<PS> = Vec::with_capacity(disjuncts.len());
            for disjunct in disjuncts.into_iter() {
                let mut new_psw: PSW = self.clone().into();
                new_psw.lw.push(disjunct);
                if let Some(ps) = new_psw.into_ps() {
                    new_ps_vec.push(ps);
                }
            }
            PSConjsResult::NewPS(new_ps_vec)
        } else {
            // this `ps` is irreducible. Does it contain atoms?
            if self.atoms.is_empty() {
                PSConjsResult::Boxes(self.try_into().unwrap())
            } else {
                PSConjsResult::Irred(self.try_into().unwrap())
            }
        }
    }

    fn into_psi(self) -> Vec<PSI> {
        match self.process_conjs_step() {
            PSConjsResult::Boxes(psb) => {
                vec![psb.into()]
            }
            PSConjsResult::Irred(psi) => {
                vec![psi]
            }
            PSConjsResult::NewPS(ps_vec) => {
                let mut output = Vec::with_capacity(ps_vec.len());
                for ps in ps_vec {
                    output.append(&mut ps.into_psi());
                }
                output
            }
        }
    }
}

/// Processing Sequent Boxes
/// a `PSI` for which `atoms` is empty. I.e. it contains no atoms on either side.
#[allow(clippy::upper_case_acronyms)]
#[derive(Clone, Debug, Eq, PartialEq, PartialOrd, Ord)]
pub struct PSB {
    pub lb: Vec<NNF>,
    pub rb: Vec<NNF>,
}

impl PSB {
    pub fn new_contradictory() -> PSB {
        PSB {
            lb: Vec::new(),
            rb: Vec::new(),
        }
    }
    pub fn is_empty(&self) -> bool {
        self.lb.is_empty() && self.rb.is_empty()
    }
    pub fn to_nnf(&self) -> NNF {
        Into::<PSI>::into(self.clone()).to_nnf()
    }

    pub fn substitute(&mut self, substitution: &BTreeMap<NnfAtom, NNF>) {
        for phi in self.lb.iter_mut() {
            phi.substitute(substitution);
        }
        for phi in self.rb.iter_mut() {
            phi.substitute(substitution);
        }
    }

    /// requires that the two sets don't intersect.
    /// Returns `None` if the resulting sequent is trivially valid.
    pub fn substitute_top_bot(
        mut self,
        subst_top: &BTreeSet<NnfAtom>,
        subst_bot: &BTreeSet<NnfAtom>,
    ) -> Option<PSB> {
        // if the two sets intersect, abort
        if !subst_top.is_disjoint(subst_bot) {
            unreachable!();
        }

        // now perform the substitution on the boxed formulae
        for box_left in self.lb.iter_mut() {
            *box_left = box_left
                .clone()
                .substitute_top_bot(subst_top, subst_bot)
                .simpl();
        }
        for box_right in self.lb.iter_mut() {
            *box_right = box_right
                .clone()
                .substitute_top_bot(subst_top, subst_bot)
                .simpl();
            if *box_right == NNF::Top {
                // We have box-top on the right, so this sequent is valid.
                return None;
            }
        }
        // and simplify the boxed formulae
        Some(self)
    }
}

impl From<PSB> for PSI {
    fn from(value: PSB) -> PSI {
        PSI {
            atoms: BTreeMap::new(),
            lb: value.lb,
            rb: value.rb,
        }
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

use proptest::proptest;

proptest! {
    #[test]
    fn test_psw(nnf in crate::nnf::arb_nnf()) {
    // The contradictory `PSW` shall be contradictory.
    assert!(NNF::equiv_dec(&PSW::new_contradictory().to_nnf(), &NNF::Bot));
    let psw = PSW::from_nnf(nnf.clone());
    assert!(NNF::equiv_dec(&nnf.clone(), &psw.to_nnf()));
    if let Some(ps) = psw.into_ps() {
        assert!(NNF::equiv_dec(&nnf.clone(), &ps.to_nnf()));
    } else {
        assert!(nnf.is_valid());
    }
    }

    #[test]
    fn test_psi(psi in super::clauses::arb_psi()) {
    let mut psi_simpl = psi.clone();
    psi_simpl.simplify();
    assert!(NNF::equiv_dec(&psi.to_nnf(), &psi_simpl.to_nnf()));
    }
}
