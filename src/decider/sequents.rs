use std::collections::{BTreeMap, BTreeSet};

use proptest::prelude::*;
use proptest_derive::Arbitrary;

use crate::nnf::{NnfAtom, NNF};

#[derive(Arbitrary, Clone, Copy, Debug, Eq, PartialEq, PartialOrd, Ord)]
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
    pub lb: BTreeSet<NNF>,
    // right boxes
    pub rb: BTreeSet<NNF>,

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
            lb: BTreeSet::new(),
            rb: BTreeSet::new(),
            ld: Vec::new(),
            rc: Vec::new(),
            lw: Vec::new(),
            rw: Vec::new(),
        }
    }

    /// Create a new sequent from an `NNF`
    pub fn from_nnf(phi: NNF) -> PSW {
        PSW::from_waiting(Vec::new(), vec![phi])
    }

    pub fn from_waiting(lw: Vec<NNF>, rw: Vec<NNF>) -> PSW {
        PSW {
            atoms: BTreeMap::new(),
            lb: BTreeSet::new(),
            rb: BTreeSet::new(),
            ld: Vec::new(),
            rc: Vec::new(),
            lw,
            rw,
        }
    }

    /// Represent this sequent as `NNF` but keep the left and right
    /// half of the sequent separate
    fn to_nnf_lr(&self) -> (NNF, NNF) {
        let mut atoms_l = Vec::new();
        let mut atoms_r = Vec::new();
        for (i, lr) in &self.atoms {
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
        NNF::impli(l, r).simpl()
    }

    pub fn display_beautiful(&self) -> PSWDisplayBeautiful {
        PSWDisplayBeautiful { psw: self }
    }
}

pub struct PSIDisplayLaTeX<'a> {
    psi: &'a PSI,
}

impl<'a> std::fmt::Display for PSIDisplayLaTeX<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let (left, right) = self.psi.to_nnf_lr();
        let (left, right) = (left.simpl(), right.simpl());
        write!(
            f,
            "{}\\Rightarrow{{}}{}",
            left.display_latex(),
            right.display_latex()
        )
    }
}

pub struct PSIDisplayBeautiful<'a> {
    psi: &'a PSI,
}

impl<'a> std::fmt::Display for PSIDisplayBeautiful<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let (left, right) = self.psi.to_nnf_lr();
        let (left, right) = (left.simpl(), right.simpl());
        write!(
            f,
            "{}⇒{}",
            left.display_beautiful(),
            right.display_beautiful()
        )
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
    pub lb: BTreeSet<NNF>,
    // right boxes
    pub rb: BTreeSet<NNF>,

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
    pub lb: BTreeSet<NNF>,
    // right boxes
    pub rb: BTreeSet<NNF>,
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
            lb: BTreeSet::new(),
            rb: BTreeSet::new(),
        }
    }

    pub fn is_varfree(&self) -> bool {
        self.atoms.is_empty()
            && self.lb.iter().all(NNF::is_ground)
            && self.rb.iter().all(NNF::is_ground)
    }

    /// Represent this sequent as `NNF` but keep the left and right
    /// half of the sequent separate
    pub fn to_nnf_lr(&self) -> (NNF, NNF) {
        let mut atoms_l = Vec::new();
        let mut atoms_r = Vec::new();
        for (i, lr) in &self.atoms {
            match lr {
                LeftRight::Left => atoms_l.push(i),
                LeftRight::Right => atoms_r.push(i),
            }
        }

        let left = atoms_l
            .iter()
            .map(|x| NNF::AtomPos(**x))
            .chain(self.lb.iter().map(|x| NNF::NnfBox(Box::new(x.clone()))))
            .collect();
        let right = atoms_r
            .iter()
            .map(|x| NNF::AtomPos(**x))
            .chain(self.rb.iter().map(|x| NNF::NnfBox(Box::new(x.clone()))))
            .collect();
        (NNF::And(left), NNF::Or(right))
    }

    pub fn to_nnf(&self) -> NNF {
        let (l, r) = self.to_nnf_lr();
        NNF::impli(l, r).simpl()
    }

    pub fn is_empty(&self) -> bool {
        self.atoms.is_empty() && self.lb.is_empty() && self.rb.is_empty()
    }

    pub fn display_beautiful(&self) -> PSIDisplayBeautiful {
        PSIDisplayBeautiful { psi: self }
    }

    pub fn substitute(mut self, substitution: &BTreeMap<NnfAtom, NNF>) -> PSW {
        self.lb = self
            .lb
            .into_iter()
            .map(|mut phi| {
                phi.substitute(substitution);
                phi
            })
            .collect();
        self.rb = self
            .rb
            .into_iter()
            .map(|mut phi| {
                phi.substitute(substitution);
                phi
            })
            .collect();

        let mut lw = Vec::new();
        let mut rw = Vec::new();
        let mut atoms = BTreeMap::new();
        for (atom, lr) in self.atoms {
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
        self.lb.remove(&NNF::Top);

        if self.lb.contains(&NNF::Bot) {
            // If there are boxes on the right, this sequent is valid.
            if !self.rb.is_empty() {
                *self = PSI::new_valid();
                return;
            }
            // We can remove all other boxes on the left
            self.lb.clear();
            self.lb.insert(NNF::Bot);
        }

        if self.rb.contains(&NNF::Top) {
            // we found a trivial box on the right. => this sequent is valid.
            *self = PSI::new_valid();
            return;
        }

        if self.rb.contains(&NNF::Bot) {
            // If there is box bot on the right and some other boxes, we can remove the box bot.
            if self.rb.len() > 1 {
                self.rb.remove(&NNF::Bot);
            }
        }

        for left_box in &self.lb {
            for right_box in &self.rb {
                if left_box == right_box {
                    *self = PSI::new_valid();
                    return;
                }
            }
        }

        // Use the usual simplification algorithm to work on the left boxes.
        // (If there are any)
        if self.lb.len() > 1 {
            let mut lb: Vec<_> = Vec::with_capacity(self.lb.len());
            lb.extend(std::mem::take(&mut self.lb).into_iter());
            match NNF::And(lb).simpl() {
                NNF::Top => {}
                NNF::And(conjuncts) => self.lb.extend(conjuncts.into_iter()),
                phi => {
                    self.lb.insert(phi);
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

        // If there is a box-bottom on the left and any box on the
        // right, then the sequent is trivially valid.
        if self.lb.contains(&NNF::Bot) && !self.rb.is_empty() {
            return Some(true);
        }

        // If the boxes on the left and on the right intersect, then
        // the sequent is trivially valid.
        if !self.lb.is_disjoint(&self.rb) {
            return Some(true);
        }

        None
    }

    pub fn new_valid() -> PSI {
        PSI {
            atoms: BTreeMap::new(),
            lb: BTreeSet::new(),
            rb: {
                let mut set = BTreeSet::new();
                set.insert(NNF::Top);
                set
            },
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
        self.lb = self
            .lb
            .into_iter()
            .map(|phi| phi.substitute_top_bot(subst_top, subst_bot).simpl())
            .collect();
        self.rb = self
            .rb
            .into_iter()
            .map(|phi| phi.substitute_top_bot(subst_top, subst_bot).simpl())
            .collect();
        // and simplify the boxed formulae

        self.lb.remove(&NNF::Top);

        if self.rb.contains(&NNF::Top) {
            return None;
        }

        Some(self)
    }
    pub fn display_latex(&self) -> PSIDisplayLaTeX {
        PSIDisplayLaTeX { psi: self }
    }

    /*
        pub fn display_spartacus<'a>(&'a self) -> PSIDisplaySpartacus<'a> {
            PSIDisplaySpartacus { psi: self }
        }
    */

    pub fn left_atoms(&self) -> BTreeSet<NnfAtom> {
        self.atoms
            .iter()
            .filter_map(|(atom, dir)| match dir {
                LeftRight::Left => Some(*atom),
                LeftRight::Right => None,
            })
            .collect()
    }

    pub fn right_atoms(&self) -> BTreeSet<NnfAtom> {
        self.atoms
            .iter()
            .filter_map(|(atom, dir)| match dir {
                LeftRight::Left => None,
                LeftRight::Right => Some(*atom),
            })
            .collect()
    }

    /// If the two sequents have this form:
    ///    Γ ⇒ Δ1; Γ ⇒ Δ2 with Δ1 subset Δ2
    /// or the form
    ///    Γ1 ⇒ Δ; Γ2 ⇒ Δ with Γ1 subset Γ2
    /// then return `Some(Left)`.
    /// If the inclusions are the other way around, return `Some(Right)`.
    /// Otherwise return `None`.
    pub fn check_subset(seq0: &PSI, seq1: &PSI) -> Option<LeftRight> {
        let left_atoms0: BTreeSet<_> = seq0.left_atoms();
        let left_atoms1: BTreeSet<_> = seq1.left_atoms();
        let right_atoms0: BTreeSet<_> = seq0.right_atoms();
        let right_atoms1: BTreeSet<_> = seq1.right_atoms();

        if seq0.lb.is_subset(&seq1.lb)
            && left_atoms0.is_subset(&left_atoms1)
            && seq0.rb.is_subset(&seq1.rb)
            && right_atoms0.is_subset(&right_atoms1)
        {
            // `seq0` is smaller than `seq1`
            Some(LeftRight::Left)
        } else if seq1.lb.is_subset(&seq0.lb)
            && left_atoms1.is_subset(&left_atoms0)
            && seq1.rb.is_subset(&seq0.rb)
            && right_atoms1.is_subset(&right_atoms0)
        {
            // `seq1` is smaller than `seq0`
            Some(LeftRight::Right)
        } else {
            None
        }
    }
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
        if self.rb.contains(&NNF::Top) {
            return None;
        }

        let mut new_left_waiting = Vec::with_capacity(self.lw.len());
        for left_waiting in self.lw {
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
                    if disjuncts.is_empty() {
                        // Then the disjunction is empty, so bot. On
                        // the left, so the sequent is valid.
                        return None;
                    } else if disjuncts.len() == 1 {
                        // There is a single formula on the left, push
                        // it to the new waiting formulae
                        new_left_waiting.push(disjuncts.into_iter().next().unwrap());
                    } else {
                        self.ld.push(disjuncts);
                    }
                }
                NNF::NnfBox(phi) => {
                    // If `lb` already contains `Bot` then do not insert the formula,
                    if self.lb.contains(&NNF::Bot) {
                        continue;
                    }
                    if self.rb.contains(&phi) {
                        // There is already a right box of the same value.
                        // So the sequent becomes valid.
                        return None;
                    }
                    self.lb.insert(*phi);
                }
                NNF::NnfDia(phi) => {
                    let phi_neg = phi.neg();
                    if self.lb.contains(&phi_neg) {
                        // There is already a left box of the same value.
                        // So the sequent becomes valid.
                        return None;
                    }
                    if phi_neg == NNF::Bot && !self.rb.is_empty() {
                        // If there are other boxed formulae on the
                        // right, then adding box bottom on the right
                        // does not change equivalence.
                        continue;
                    }
                    if phi_neg == NNF::Top {
                        // We are adding box-top on the right, i.e. top on the right.
                        // This makes the sequent valid.
                        return None;
                    }
                    self.rb.insert(phi_neg);
                }
            }
        }

        let mut new_right_waiting = Vec::with_capacity(self.rw.len());
        for right_waiting in self.rw {
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
                    if conjuncts.is_empty() {
                        // Then the conjunction is empty, so top. On
                        // the right, so the sequent is valid.
                        return None;
                    } else if conjuncts.len() == 1 {
                        // There is a single formula on the left, push
                        // it to the new waiting formulae
                        new_right_waiting.push(conjuncts.into_iter().next().unwrap());
                    } else {
                        self.rc.push(conjuncts);
                    }
                }
                NNF::Or(mut disjuncts) => {
                    new_right_waiting.append(&mut disjuncts);
                }
                NNF::NnfBox(phi) => {
                    if self.lb.contains(&phi) {
                        return None;
                    }
                    if *phi == NNF::Bot && !self.rb.is_empty() {
                        // If there are other boxed formulae on the
                        // right, then adding box bottom on the right
                        // does not change equivalence.
                        continue;
                    }
                    if *phi == NNF::Top {
                        // We are adding box-top on the right, i.e. top on the right.
                        // This makes the sequent valid.
                        return None;
                    }
                    self.rb.insert(*phi);
                }
                NNF::NnfDia(phi) => {
                    let phi_neg = phi.neg();
                    if self.rb.contains(&phi_neg) {
                        return None;
                    }
                    self.lb.insert(phi_neg);
                }
            }
        }
        self.lw = new_left_waiting;
        self.rw = new_right_waiting;
        Some(self)
    }

    /// Transforms the given `PSW` into an equivalent but simpler `PS`.
    /// Returns `None` if the input is valid.
    pub fn into_ps(mut self) -> Option<PS> {
        loop {
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
            self = self.into_ps_step()?;
        }
    }
}

pub enum PSConjsResult {
    NewPS(BTreeSet<PS>),
    Irred(PSI),
    Boxes(PSB),
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
            lb: BTreeSet::new(),
            rb: BTreeSet::new(),
            ld: vec![vec![NNF::Bot]],
            rc: Vec::new(),
        }
    }

    pub fn substitute(&mut self, substitution: &BTreeMap<NnfAtom, NNF>) {
        let old_lb = std::mem::take(&mut self.lb);
        self.lb.extend(old_lb.into_iter().map(|mut phi| {
            phi.substitute(substitution);
            phi
        }));
        let old_rb = std::mem::take(&mut self.rb);
        self.rb.extend(old_rb.into_iter().map(|mut phi| {
            phi.substitute(substitution);
            phi
        }));
        for vec in &mut self.ld {
            for phi in vec.iter_mut() {
                phi.substitute(substitution);
            }
        }
        for vec in &mut self.rc {
            for phi in vec.iter_mut() {
                phi.substitute(substitution);
            }
        }

        let mut lw = Vec::new();
        let mut rw = Vec::new();
        let mut new_atoms = BTreeMap::new();
        for (atom, lr) in std::mem::take(&mut self.atoms) {
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
        self.lb = self
            .lb
            .into_iter()
            .map(|phi| phi.substitute_top_bot(subst_top, subst_bot).simpl())
            .collect();
        self.rb = self
            .rb
            .into_iter()
            .map(|phi| phi.substitute_top_bot(subst_top, subst_bot).simpl())
            .collect();

        // perform the substitution on the left/right conjunctions/disjunctions
        // TODO: It is possible to perform some ad-hoc optimisations
        // here, if `conjunct` or `disjunct` are `Top` or `Bot`.
        for conjuncts in &mut self.rc {
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
        for disjuncts in &mut self.rc {
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
                lb: BTreeSet::new(),
                rb: BTreeSet::new(),
                ld: Vec::new(),
                rc: Vec::new(),
                lw: Vec::new(),
                rw: conjuncts,
            };
            if let Some(mut ps) = new_psw.into_ps() {
                for (atom, dir) in ps.atoms {
                    if let Some(prev_dir) = self.atoms.insert(atom, dir) {
                        if dir != prev_dir {
                            // There is an atom on the left and on the right.
                            // Therefore this sequent is valid.
                            *self = PS::new_valid();
                            return;
                        }
                    }
                }
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
                lb: BTreeSet::new(),
                rb: BTreeSet::new(),
                ld: Vec::new(),
                rc: Vec::new(),
                lw: disjuncts,
                rw: Vec::new(),
            };
            if let Some(mut ps) = new_psw.into_ps() {
                for (atom, dir) in ps.atoms {
                    if let Some(prev_dir) = self.atoms.insert(atom, dir) {
                        if dir != prev_dir {
                            // There is an atom on the left and on the right.
                            // Therefore this sequent is valid.
                            *self = PS::new_valid();
                            return;
                        }
                    }
                }
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
            let mut new_ps_set: BTreeSet<PS> = BTreeSet::new();
            for conj in conjuncts {
                let mut new_psw: PSW = self.clone().into();
                new_psw.rw.push(conj);
                if let Some(new_ps) = new_psw.into_ps() {
                    new_ps_set.insert(new_ps);
                }
            }
            PSConjsResult::NewPS(new_ps_set)
        } else if let Some(disjuncts) = self.ld.pop() {
            let mut new_ps_set: BTreeSet<PS> = BTreeSet::new();
            for disjunct in disjuncts {
                let mut new_psw: PSW = self.clone().into();
                new_psw.lw.push(disjunct);
                if let Some(ps) = new_psw.into_ps() {
                    new_ps_set.insert(ps);
                }
            }
            PSConjsResult::NewPS(new_ps_set)
        } else {
            // this `ps` is irreducible. Does it contain atoms?
            if self.atoms.is_empty() {
                PSConjsResult::Boxes(self.try_into().unwrap())
            } else {
                PSConjsResult::Irred(self.try_into().unwrap())
            }
        }
    }
}

/// Processing Sequent Boxes
/// a `PSI` for which `atoms` is empty. I.e. it contains no atoms on either side.
#[allow(clippy::upper_case_acronyms)]
#[derive(Clone, Debug, Eq, PartialEq, PartialOrd, Ord)]
pub struct PSB {
    pub lb: BTreeSet<NNF>,
    pub rb: BTreeSet<NNF>,
}

impl PSB {
    pub fn new_contradictory() -> PSB {
        PSB {
            lb: BTreeSet::new(),
            rb: BTreeSet::new(),
        }
    }
    pub fn is_empty(&self) -> bool {
        self.lb.is_empty() && self.rb.is_empty()
    }
    pub fn to_nnf(&self) -> NNF {
        Into::<PSI>::into(self.clone()).to_nnf()
    }

    pub fn is_varfree(&self) -> bool {
        self.lb.iter().all(NNF::is_ground) && self.rb.iter().all(NNF::is_ground)
    }

    pub fn substitute(&mut self, substitution: &BTreeMap<NnfAtom, NNF>) {
        let old_lb = std::mem::take(&mut self.lb);
        self.lb.extend(old_lb.into_iter().map(|mut phi| {
            phi.substitute(substitution);
            phi
        }));
        let old_rb = std::mem::take(&mut self.rb);
        self.rb.extend(old_rb.into_iter().map(|mut phi| {
            phi.substitute(substitution);
            phi
        }));
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
        self.lb = self
            .lb
            .into_iter()
            .map(|box_left| box_left.substitute_top_bot(subst_top, subst_bot))
            .collect();
        self.rb = self
            .rb
            .into_iter()
            .map(|box_right| box_right.substitute_top_bot(subst_top, subst_bot))
            .collect();

        self.lb.remove(&NNF::Top);

        if self.rb.contains(&NNF::Top) {
            return None;
        }

        if !self.lb.is_disjoint(&self.rb) {
            return None;
        }

        // and simplify the boxed formulae
        Some(self)
    }

    /// Transforms this sequent into equivalent sequents, if there is
    /// at most one boxed formulae on the right.
    ///
    /// Returns `PsbEasyResult::Hard` iff it has more than one boxed formulae on the right.
    pub fn step_if_easy(self) -> PsbEasyResult {
        // If the sequent has no boxed formulae on the right, it is contradictory.
        // Making the whole clause contradictory.
        if self.rb.is_empty() {
            return PsbEasyResult::InValid;
        }

        // If the sequent has more than one boxed formula on the
        // right, applying the box-rule causes a branching, i.e. new clauses.
        // This is "too complicated", so don't deal with these here.
        if self.rb.len() > 1 {
            return PsbEasyResult::Hard(self);
        }

        // "Remove" all the boxes, by moving the `lb` and `rb` into
        // `lw` and `rw`.
        let new_sequent: PSW = PSW {
            atoms: BTreeMap::new(),
            lb: BTreeSet::new(),
            rb: BTreeSet::new(),
            ld: Vec::new(),
            rc: Vec::new(),
            lw: {
                let mut lw = Vec::with_capacity(self.lb.len());
                lw.extend(self.lb.into_iter());
                lw
            },
            rw: {
                let mut rw = Vec::with_capacity(self.rb.len());
                rw.extend(self.rb.into_iter());
                rw
            },
        };

        // if `to_ps` returns `None`, the sequent was valid and
        // imposes no further restriction on `clause`.
        if let Some(new_sequent) = new_sequent.into_ps() {
            match TryInto::<PSI>::try_into(new_sequent) {
                Ok(psi) => match TryInto::<PSB>::try_into(psi) {
                    Ok(psb) => psb.step_if_easy(),
                    Err(psi) => PsbEasyResult::Psi(psi),
                },
                Err(ps) => PsbEasyResult::Ps(ps),
            }
        } else {
            PsbEasyResult::Valid
        }
    }
}

pub enum PsbEasyResult {
    Hard(PSB),
    Psi(PSI),
    Ps(PS),
    Valid,
    InValid,
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

#[allow(dead_code)]
pub fn arb_psi() -> impl Strategy<Value = PSI> {
    (
        prop::collection::btree_map(any::<NnfAtom>(), any::<LeftRight>(), 0..10),
        prop::collection::btree_set(crate::nnf::arb_nnf(), 0..3),
        prop::collection::btree_set(crate::nnf::arb_nnf(), 0..3),
    )
        .prop_map(|(atoms, lb, rb)| PSI { atoms, lb, rb })
}

#[allow(dead_code)]
pub fn arb_psb() -> impl Strategy<Value = PSB> {
    (
        prop::collection::btree_set(crate::nnf::arb_nnf(), 0..3),
        prop::collection::btree_set(crate::nnf::arb_nnf(), 0..3),
    )
        .prop_map(|(lb, rb)| PSB { lb, rb })
}

#[allow(dead_code)]
pub fn arb_ps() -> impl Strategy<Value = PS> {
    (
        prop::collection::btree_map(any::<NnfAtom>(), any::<LeftRight>(), 0..10),
        prop::collection::btree_set(crate::nnf::arb_nnf(), 0..3),
        prop::collection::btree_set(crate::nnf::arb_nnf(), 0..3),
        prop::collection::vec(prop::collection::vec(crate::nnf::arb_nnf(), 0..3), 0..3),
        prop::collection::vec(prop::collection::vec(crate::nnf::arb_nnf(), 0..3), 0..3),
    )
        .prop_map(|(atoms, lb, rb, ld, rc)| PS {
            atoms,
            lb,
            rb,
            ld,
            rc,
        })
}

proptest! {
    #[test]
    fn test_psw(nnf in crate::nnf::arb_nnf()) {
    // The contradictory `PSW` shall be contradictory.
    assert!(NNF::equiv_dec(&PSW::new_contradictory().to_nnf(), &NNF::Bot));
    let psw = PSW::from_nnf(nnf.clone());
    assert!(NNF::equiv_dec(&nnf, &psw.to_nnf()));
    if let Some(ps) = psw.into_ps() {
        assert!(NNF::equiv_dec(&nnf, &ps.to_nnf()));
    } else {
        assert!(nnf.is_valid());
    }
    }

    #[test]
    fn test_psi_to_nnf(psi in arb_psi()) {
    let (l, r) = psi.to_nnf_lr();
    let nnf = NNF::impli(l, r);
    assert!(NNF::equiv_dec(&psi.to_nnf(), &nnf));
    }

    #[test]
    fn test_step_if_easy(psb in arb_psb()) {
    // Condition: The output of `step_if_easy` is both equi-valid
    // and unifier-equivalent to `psb`.
    // TODO: Check for unifier-equivalence.
    match psb.clone().step_if_easy() {
    PsbEasyResult::Hard(hard) => {
        assert_eq!(psb.to_nnf().is_valid(), hard.to_nnf().is_valid());
    }
    PsbEasyResult::Psi(psi) => {
        assert_eq!(psb.to_nnf().is_valid(), psi.to_nnf().is_valid())
    }
    PsbEasyResult::Ps(ps) => {
        assert_eq!(psb.to_nnf().is_valid(), ps.to_nnf().is_valid())
    }
    PsbEasyResult::Valid => assert!(psb.to_nnf().is_valid()),
    PsbEasyResult::InValid => {
        // There are kripke models in which the formula is false,
        // no matter what substitution we apply. Not only is it
        // not-valid, but also not unifiable.
        assert!(!psb.to_nnf().is_valid())
    }
    }
    }

    #[test]
    fn test_psi_simplify(psi in arb_psi()) {
    let mut psi_simpl = psi.clone();
    psi_simpl.simplify();
    assert!(NNF::equiv_dec(&psi.to_nnf(), &psi_simpl.to_nnf()));
    match psi.simple_check_validity() {
    None => {},
    Some(true) => {
        assert!(psi.to_nnf().is_valid());
    },
    Some(false) => {
        assert!(NNF::equiv_dec(&psi.to_nnf(), &NNF::Bot));
    }
    }
    }

    #[test]
    fn test_process_easy_conjs(ps in arb_ps()) {
    let mut ps_simpl = ps.clone();
    ps_simpl.process_easy_conjs();
    let ps : PSW = ps.into();
    let ps_simpl: PSW = ps_simpl.into();
    assert!(NNF::equiv_dec(&ps.to_nnf(), &ps_simpl.to_nnf()));
    }
}
