//! Simplification shall be done in multiple steps: Destructure the formula
//! into its constituent parts, using `BTreeSet`. Then apply simplifications where possible.
//! Then put it together again using `Vec`.

use super::{NnfAtom, NNF};
use std::collections::BTreeSet;

#[derive(Clone, Debug, Eq, PartialEq, PartialOrd, Ord)]
enum BoxConjuncts {
    None,
    Some(Box<NnfConj>),
    /// is used if box-bottom is a conjunct.
    Bot,
}

impl BoxConjuncts {
    fn add_precise(self, phi: NnfPrecise) -> BoxConjuncts {
        match self {
            BoxConjuncts::None => {
                let new_bc = BoxConjuncts::Some(Box::new(NnfConj::new_empty()));
                new_bc.add_precise(phi)
            }
            // The dia-top absorbs the new formula.
            BoxConjuncts::Bot => BoxConjuncts::Bot,
            BoxConjuncts::Some(nc) => {
                if let Some(new_nc) = nc.add_precise(phi) {
                    BoxConjuncts::Some(Box::new(new_nc))
                } else {
                    BoxConjuncts::Bot
                }
            }
        }
    }

    fn neg(self) -> DiaDisjuncts {
        match self {
            BoxConjuncts::None => DiaDisjuncts::None,
            BoxConjuncts::Bot => DiaDisjuncts::Top,
            BoxConjuncts::Some(bc) => DiaDisjuncts::Some(Box::new(bc.neg())),
        }
    }

    fn simpl(self) -> Option<NnfPrecise> {
        match self {
            BoxConjuncts::None => None,
            BoxConjuncts::Bot => Some(NnfPrecise::Bot),
            BoxConjuncts::Some(nc) => Some(nc.simpl()),
        }
    }

    fn into_nnf(self) -> Option<NNF> {
        match self {
            BoxConjuncts::None => None,
            BoxConjuncts::Bot => Some(NNF::boxx(NNF::Bot)),
            BoxConjuncts::Some(nc) => Some(NNF::boxx(nc.into_nnf())),
        }
    }

    fn and(self, disj: BoxConjuncts) -> BoxConjuncts {
        match (self, disj) {
            (BoxConjuncts::None, disj) | (disj, BoxConjuncts::None) => disj,
            (BoxConjuncts::Bot, _) | (_, BoxConjuncts::Bot) => BoxConjuncts::Bot,
            (BoxConjuncts::Some(nc0), BoxConjuncts::Some(nc1)) => {
                if let Some(new_nc) = nc0.and(*nc1) {
                    BoxConjuncts::Some(Box::new(new_nc))
                } else {
                    BoxConjuncts::Bot
                }
            }
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, PartialOrd, Ord)]
enum DiaDisjuncts {
    None,
    Some(Box<NnfDisj>),
    /// is used if dia-top is a disjunct.
    Top,
}

impl DiaDisjuncts {
    fn into_nnf(self) -> Option<NNF> {
        match self {
            DiaDisjuncts::None => None,
            DiaDisjuncts::Top => Some(NNF::dia(NNF::Top)),
            DiaDisjuncts::Some(nd) => Some(NNF::dia(nd.into_nnf())),
        }
    }

    fn neg(self) -> BoxConjuncts {
        match self {
            DiaDisjuncts::None => BoxConjuncts::None,
            DiaDisjuncts::Top => BoxConjuncts::Bot,
            DiaDisjuncts::Some(nd) => BoxConjuncts::Some(Box::new(nd.neg())),
        }
    }

    fn simpl(self) -> Option<NnfPrecise> {
        match self {
            DiaDisjuncts::None => None,
            DiaDisjuncts::Top => Some(NnfPrecise::Top),
            DiaDisjuncts::Some(nd) => Some(nd.simpl()),
        }
    }

    fn add_precise(self, phi: NnfPrecise) -> DiaDisjuncts {
        match self {
            DiaDisjuncts::None => {
                let new_dd = DiaDisjuncts::Some(Box::new(NnfDisj::new_empty()));
                new_dd.add_precise(phi)
            }
            // The dia-top absorbs the new formula.
            DiaDisjuncts::Top => DiaDisjuncts::Top,
            DiaDisjuncts::Some(nd) => {
                if let Some(new_nd) = nd.add_precise(phi) {
                    DiaDisjuncts::Some(Box::new(new_nd))
                } else {
                    DiaDisjuncts::Top
                }
            }
        }
    }

    fn or(self, disj: DiaDisjuncts) -> DiaDisjuncts {
        match (self, disj) {
            (DiaDisjuncts::None, disj) | (disj, DiaDisjuncts::None) => disj,
            (DiaDisjuncts::Top, _) | (_, DiaDisjuncts::Top) => DiaDisjuncts::Top,
            (DiaDisjuncts::Some(nd0), DiaDisjuncts::Some(nd1)) => {
                if let Some(new_nd) = nd0.or(*nd1) {
                    DiaDisjuncts::Some(Box::new(new_nd))
                } else {
                    DiaDisjuncts::Top
                }
            }
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, PartialOrd, Ord)]
enum NnfPrecise {
    AtomPos(NnfAtom),
    AtomNeg(NnfAtom),
    Bot,
    Top,
    NnfBox(Box<NnfPrecise>),
    NnfDia(Box<NnfPrecise>),
    And(NnfConj),
    Or(NnfDisj),
}

impl NnfPrecise {
    fn neg(self) -> NnfPrecise {
        match self {
            NnfPrecise::AtomPos(i) => NnfPrecise::AtomNeg(i),
            NnfPrecise::AtomNeg(i) => NnfPrecise::AtomPos(i),
            NnfPrecise::Bot => NnfPrecise::Top,
            NnfPrecise::Top => NnfPrecise::Bot,
            NnfPrecise::NnfBox(phi) => NnfPrecise::NnfDia(Box::new(phi.neg())),
            NnfPrecise::NnfDia(phi) => NnfPrecise::NnfBox(Box::new(phi.neg())),
            NnfPrecise::And(phi) => NnfPrecise::Or(phi.neg()),
            NnfPrecise::Or(phi) => NnfPrecise::And(phi.neg()),
        }
    }

    fn and(self, other: NnfPrecise) -> NnfPrecise {
        match (self, other) {
            (NnfPrecise::Bot, _) | (_, NnfPrecise::Bot) => NnfPrecise::Bot,
            (NnfPrecise::Top, other) | (other, NnfPrecise::Top) => other,
            (NnfPrecise::And(conj), other) | (other, NnfPrecise::And(conj)) => {
                if let Some(conj) = conj.add_precise(other) {
                    NnfPrecise::And(conj)
                } else {
                    NnfPrecise::Bot
                }
            }
            (a, b) => {
                let conj = NnfConj::new_empty();
                if let Some(conj) = conj.add_precise(a) {
                    if let Some(conj) = conj.add_precise(b) {
                        return NnfPrecise::And(conj);
                    }
                }
                NnfPrecise::Bot
            }
        }
    }

    fn or(self, other: NnfPrecise) -> NnfPrecise {
        match (self, other) {
            (NnfPrecise::Top, _) | (_, NnfPrecise::Top) => NnfPrecise::Top,
            (NnfPrecise::Bot, other) | (other, NnfPrecise::Bot) => other,
            (NnfPrecise::Or(disj), other) | (other, NnfPrecise::Or(disj)) => {
                if let Some(disj) = disj.add_precise(other) {
                    NnfPrecise::Or(disj)
                } else {
                    NnfPrecise::Top
                }
            }
            (a, b) => {
                let disj = NnfDisj::new_empty();
                if let Some(disj) = disj.add_precise(a) {
                    if let Some(disj) = disj.add_precise(b) {
                        return NnfPrecise::Or(disj);
                    }
                }
                NnfPrecise::Top
            }
        }
    }

    fn from_nnf(nnf: NNF) -> NnfPrecise {
        match nnf {
            NNF::AtomPos(i) => NnfPrecise::AtomPos(i),
            NNF::AtomNeg(i) => NnfPrecise::AtomNeg(i),
            NNF::Bot => NnfPrecise::Bot,
            NNF::Top => NnfPrecise::Top,
            NNF::And(conjuncts) => {
                let mut base: NnfPrecise = NnfPrecise::Top;
                for conjunct in conjuncts {
                    base = base.and(NnfPrecise::from_nnf(conjunct));
                }
                base
            }
            NNF::Or(disjuncts) => {
                let mut base: NnfPrecise = NnfPrecise::Bot;
                for disjunct in disjuncts {
                    base = base.or(NnfPrecise::from_nnf(disjunct));
                }
                base
            }
            NNF::NnfBox(phi) => {
                let phi = NnfPrecise::from_nnf(*phi);
                if phi == NnfPrecise::Top {
                    NnfPrecise::Top
                } else {
                    NnfPrecise::NnfBox(Box::new(phi))
                }
            }
            NNF::NnfDia(phi) => {
                let phi = NnfPrecise::from_nnf(*phi);
                if phi == NnfPrecise::Bot {
                    NnfPrecise::Bot
                } else {
                    NnfPrecise::NnfDia(Box::new(phi))
                }
            }
        }
    }

    fn into_nnf(self) -> NNF {
        match self {
            NnfPrecise::AtomPos(i) => NNF::AtomPos(i),
            NnfPrecise::AtomNeg(i) => NNF::AtomNeg(i),
            NnfPrecise::Bot => NNF::Bot,
            NnfPrecise::Top => NNF::Top,
            NnfPrecise::NnfBox(phi) => NNF::NnfBox(Box::new(phi.into_nnf())),
            NnfPrecise::NnfDia(phi) => NNF::NnfDia(Box::new(phi.into_nnf())),
            NnfPrecise::And(conj) => conj.into_nnf(),
            NnfPrecise::Or(disj) => disj.into_nnf(),
        }
    }

    fn simpl(self) -> NnfPrecise {
        match self {
            NnfPrecise::AtomPos(i) => NnfPrecise::AtomPos(i),
            NnfPrecise::AtomNeg(i) => NnfPrecise::AtomNeg(i),
            NnfPrecise::Bot => NnfPrecise::Bot,
            NnfPrecise::Top => NnfPrecise::Top,
            NnfPrecise::NnfBox(phi) => {
                let phi = phi.simpl();
                if phi == NnfPrecise::Top {
                    NnfPrecise::Top
                } else {
                    NnfPrecise::NnfBox(Box::new(phi))
                }
            }
            NnfPrecise::NnfDia(phi) => {
                let phi = phi.simpl();
                if phi == NnfPrecise::Bot {
                    NnfPrecise::Bot
                } else {
                    NnfPrecise::NnfDia(Box::new(phi))
                }
            }
            NnfPrecise::And(conj) => conj.simpl(),
            NnfPrecise::Or(disj) => disj.simpl(),
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, PartialOrd, Ord)]
struct NnfConj {
    atoms_pos: BTreeSet<NnfAtom>,
    atoms_neg: BTreeSet<NnfAtom>,

    boxed_conjuncts: BoxConjuncts,
    diamond_conjuncts: BTreeSet<NnfPrecise>,
    or_conjuncts: BTreeSet<NnfDisj>,
}

#[derive(Clone, Debug, Eq, PartialEq, PartialOrd, Ord)]
struct NnfDisj {
    atoms_pos: BTreeSet<NnfAtom>,
    atoms_neg: BTreeSet<NnfAtom>,

    diamond_disjuncts: DiaDisjuncts,
    box_disjuncts: BTreeSet<NnfPrecise>,
    and_disjuncts: BTreeSet<NnfConj>,
}

impl NnfDisj {
    /// Empty disjunctions are contradictory
    fn new_empty() -> NnfDisj {
        NnfDisj {
            atoms_pos: BTreeSet::new(),
            atoms_neg: BTreeSet::new(),

            diamond_disjuncts: DiaDisjuncts::None,
            box_disjuncts: BTreeSet::new(),
            and_disjuncts: BTreeSet::new(),
        }
    }

    fn neg(self) -> NnfConj {
        NnfConj {
            atoms_pos: self.atoms_neg,
            atoms_neg: self.atoms_pos,

            boxed_conjuncts: self.diamond_disjuncts.neg(),
            diamond_conjuncts: self
                .box_disjuncts
                .into_iter()
                .map(NnfPrecise::neg)
                .collect(),
            or_conjuncts: self.and_disjuncts.into_iter().map(NnfConj::neg).collect(),
        }
    }

    fn add_precise(mut self, phi: NnfPrecise) -> Option<NnfDisj> {
        match phi {
            NnfPrecise::AtomPos(i) => {
                if self.atoms_neg.contains(&i) {
                    None
                } else {
                    self.atoms_pos.insert(i);
                    Some(self)
                }
            }
            NnfPrecise::AtomNeg(i) => {
                if self.atoms_pos.contains(&i) {
                    None
                } else {
                    self.atoms_neg.insert(i);
                    Some(self)
                }
            }
            NnfPrecise::Top => None,
            NnfPrecise::Bot => Some(self),
            NnfPrecise::Or(disj) => self.or(disj),
            NnfPrecise::NnfDia(phi) => {
                if *phi == NnfPrecise::Bot {
                    return Some(self);
                } else if *phi == NnfPrecise::Top && !self.box_disjuncts.is_empty() {
                    return None;
                }

                self.diamond_disjuncts = self.diamond_disjuncts.add_precise(*phi);
                Some(self)
            }
            NnfPrecise::NnfBox(phi) => {
                if *phi == NnfPrecise::Top {
                    return None;
                } else if *phi == NnfPrecise::Bot && !self.box_disjuncts.is_empty() {
                    // If there are other `bd` than `Bot`, then we can omit the `Bot`
                    return Some(self);
                }
                // If there are other `bd` than `Bot`, then we can omit the `Bot`
                self.box_disjuncts.remove(&NnfPrecise::Bot);

                self.box_disjuncts.insert(*phi);
                Some(self)
            }
            NnfPrecise::And(mut conj) => {
                // If there is another `and_disjunts` which differs
                // from `conj` only in the sign of an atom, then
                // simplify using distributivity.
                // I.e. if `(p /\ A) \/ (~p /\ A) \/ B` would appear,
                // do `A \/ B` instead.
                let mut atom = None;
                self.and_disjuncts.retain(|other| {
                    if atom.is_some() {
                        return true;
                    }
                    if let Some(i) = conj.differ_by_single_atom(other) {
                        atom = Some(i);
                        false
                    } else {
                        true
                    }
                });
                if let Some(i) = atom {
                    conj.atoms_neg.remove(&i);
                    conj.atoms_pos.remove(&i);
                    //WARNING: It is possible that repeated simplifications are possible,
                    //using this rule. But the current algorithm stops at one application.
                    //This is only a "problem" in the multi-variable case.
                }
                self.and_disjuncts
                    .retain(|other| !conj.differ_by_negated_dc(other));

                // Replace ⋄~φ ∨ (⌷φ ∧ Γ) ∨ Δ by ⋄~φ ∨ Γ ∨ Δ.
                if self.diamond_disjuncts == conj.boxed_conjuncts.clone().neg() {
                    conj.boxed_conjuncts = BoxConjuncts::None;
                }

                self.and_disjuncts.insert(conj);
                Some(self)
            }
        }
    }

    fn or(mut self, disj: NnfDisj) -> Option<NnfDisj> {
        if !self.atoms_pos.is_disjoint(&disj.atoms_neg)
            || !self.atoms_neg.is_disjoint(&disj.atoms_pos)
        {
            return None;
        }
        self.atoms_pos.extend(disj.atoms_pos.into_iter());
        self.atoms_neg.extend(disj.atoms_neg.into_iter());

        self.diamond_disjuncts = self.diamond_disjuncts.or(disj.diamond_disjuncts);
        self.box_disjuncts.extend(disj.box_disjuncts.into_iter());
        self.and_disjuncts.extend(disj.and_disjuncts.into_iter());
        Some(self)
    }

    fn simpl(mut self) -> NnfPrecise {
        // first move all the "nested" parts out of `self`
        let mut diamond_disjuncts = DiaDisjuncts::None;
        std::mem::swap(&mut self.diamond_disjuncts, &mut diamond_disjuncts);
        let box_disjuncts = std::mem::take(&mut self.box_disjuncts);
        let and_disjuncts = std::mem::take(&mut self.and_disjuncts);

        // now simplify the parts, while writing the results back into `self`
        for bd in box_disjuncts {
            let bd = bd.simpl();

            if bd == NnfPrecise::Top {
                return NnfPrecise::Top;
            }

            if let Some(disj) = self.add_precise(NnfPrecise::NnfBox(Box::new(bd))) {
                self = disj;
            } else {
                return NnfPrecise::Top;
            }
        }
        for ad in and_disjuncts {
            let ad = ad.simpl();
            if let Some(disj) = self.add_precise(ad) {
                self = disj;
            } else {
                return NnfPrecise::Top;
            }
        }
        if let Some(dd) = diamond_disjuncts.simpl() {
            if dd == NnfPrecise::Top && !self.box_disjuncts.is_empty() {
                return NnfPrecise::Top;
            }

            // it is possible that `dd` implies the negation of one of
            // the formulae in `box_disjuncts`. in that case, the
            // whole disjunction becomes trivially valid.
            for bd in &self.box_disjuncts {
                if dd.clone().into_nnf() == bd.clone().into_nnf().neg() {
                    return NnfPrecise::Top;
                }
            }

            if let Some(disj) = self.add_precise(NnfPrecise::NnfDia(Box::new(dd))) {
                self = disj;
            } else {
                return NnfPrecise::Top;
            }
        }

        if !self.atoms_pos.is_disjoint(&self.atoms_neg) {
            return NnfPrecise::Top;
        }

        if self.atoms_pos.is_empty()
            && self.atoms_neg.is_empty()
            && self.diamond_disjuncts == DiaDisjuncts::None
            && self.box_disjuncts.is_empty()
            && self.and_disjuncts.is_empty()
        {
            return NnfPrecise::Bot;
        }
        if self.atoms_pos.len() == 1
            && self.atoms_neg.is_empty()
            && self.diamond_disjuncts == DiaDisjuncts::None
            && self.box_disjuncts.is_empty()
            && self.and_disjuncts.is_empty()
        {
            return NnfPrecise::AtomPos(self.atoms_pos.into_iter().next().unwrap());
        }
        if self.atoms_pos.is_empty()
            && self.atoms_neg.len() == 1
            && self.diamond_disjuncts == DiaDisjuncts::None
            && self.box_disjuncts.is_empty()
            && self.and_disjuncts.is_empty()
        {
            return NnfPrecise::AtomNeg(self.atoms_neg.into_iter().next().unwrap());
        }
        if self.atoms_pos.is_empty()
            && self.atoms_neg.is_empty()
            && self.diamond_disjuncts == DiaDisjuncts::Top
            && self.box_disjuncts.is_empty()
            && self.and_disjuncts.is_empty()
        {
            return NnfPrecise::NnfDia(Box::new(NnfPrecise::Top));
        }
        if self.atoms_pos.is_empty()
            && self.atoms_neg.is_empty()
            && self.diamond_disjuncts == DiaDisjuncts::None
            && self.box_disjuncts.len() == 1
            && self.and_disjuncts.is_empty()
        {
            return NnfPrecise::NnfBox(Box::new(self.box_disjuncts.into_iter().next().unwrap()));
        }
        NnfPrecise::Or(self)
    }

    fn into_nnf(self) -> NNF {
        let atom_pos = self.atoms_pos.into_iter().map(NNF::AtomPos);
        let atom_neg = self.atoms_neg.into_iter().map(NNF::AtomNeg);
        let dia_disj = self.diamond_disjuncts.into_nnf();
        let box_disjuncts = self
            .box_disjuncts
            .into_iter()
            .map(|dc| NNF::NnfBox(Box::new(dc.into_nnf())));
        let and_disjuncts = self.and_disjuncts.into_iter().map(NnfConj::into_nnf);

        let vec: Vec<NNF> = atom_pos
            .chain(atom_neg)
            .chain(dia_disj.into_iter())
            .chain(box_disjuncts)
            .chain(and_disjuncts)
            .collect();

        if vec.is_empty() {
            return NNF::Bot;
        }
        if vec.len() == 1 {
            return vec.into_iter().next().unwrap();
        }

        NNF::Or(vec)
    }

    /// Returns `Some(i)` iff `self` and `other` only differ in
    /// exactly the sign of the atom `i`.  Otherwise returns `None`.
    fn differ_by_single_atom(&self, other: &NnfDisj) -> Option<NnfAtom> {
        // For the below to work, we need the `atoms_pos` and `atoms_neg` to be disjoint.
        assert!(self.atoms_pos.is_disjoint(&self.atoms_neg));
        assert!(other.atoms_pos.is_disjoint(&other.atoms_neg));

        // Early exit, if `self` and `other` are certainly not similar enough to be considered.
        if self.box_disjuncts.len() != other.box_disjuncts.len()
            || self.and_disjuncts.len() != other.and_disjuncts.len()
        {
            return None;
        }

        // The atoms can be compared using the symmetric difference.
        let mut pos = self.atoms_pos.symmetric_difference(&other.atoms_pos);
        let mut neg = self.atoms_neg.symmetric_difference(&other.atoms_neg);

        // We need both iterators to contain exactly one and exactly the same element.
        if let (Some(i), Some(j)) = (pos.next(), neg.next()) {
            if i == j
                && pos.next().is_none()
                && neg.next().is_none()
                && self.diamond_disjuncts == other.diamond_disjuncts
                && self.box_disjuncts == other.box_disjuncts
                && self.and_disjuncts == other.and_disjuncts
            {
                return Some(*i);
            }
        }
        None
    }

    /// If `self` and `other` are of the form
    /// `([]p \/ A)` and `(<>~p \/ A)` then return `true` and change `self` into `A`.
    /// Otherwise return `false` and do nothing.
    fn differ_by_negated_bd(&mut self, other: &NnfDisj) -> bool {
        // First ensure that all other things are equal.
        if self.atoms_pos != other.atoms_pos
            || self.atoms_neg != other.atoms_neg
            || self.and_disjuncts != other.and_disjuncts
        {
            return false;
        }

        // The symmetric difference of `box_disjuncts` must contain exactly one element.
        let mut bd_diff = self
            .box_disjuncts
            .symmetric_difference(&other.box_disjuncts);

        let bd_diff = {
            if let Some(bd) = bd_diff.next() {
                if bd_diff.next().is_none() {
                    bd
                } else {
                    return false;
                }
            } else {
                return false;
            }
        };

        // The `NnfDisj` which contains `bd_diff` must have
        // `DiaDisjuncts::None` while the other must have the negation
        // of `bd_diff` as `DiaDisjuncts`

        if self.box_disjuncts.contains(bd_diff) {
            if self.diamond_disjuncts != DiaDisjuncts::None {
                return false;
            }

            // `self` is ok. check `other` now.
            if *bd_diff == NnfPrecise::Bot {
                if other.diamond_disjuncts == DiaDisjuncts::Top {
                    // Found a match.
                    self.box_disjuncts.remove(&bd_diff.clone());
                    return true;
                } else {
                    return false;
                }
            }

            if let DiaDisjuncts::Some(dd) = &other.diamond_disjuncts {
                if bd_diff.clone().into_nnf().neg() == dd.clone().into_nnf() {
                    // Found a match.
                    self.box_disjuncts.remove(&bd_diff.clone());
                    return true;
                }
            }
        } else {
            if other.diamond_disjuncts != DiaDisjuncts::None {
                return false;
            }

            // `other` is ok. check `self` now.
            if *bd_diff == NnfPrecise::Bot {
                if self.diamond_disjuncts == DiaDisjuncts::Top {
                    // Found a match.
                    self.diamond_disjuncts = DiaDisjuncts::None;
                    return true;
                } else {
                    return false;
                }
            }

            if let DiaDisjuncts::Some(dd) = &self.diamond_disjuncts {
                if bd_diff.clone().into_nnf().neg() == dd.clone().into_nnf() {
                    // Found a match.
                    self.diamond_disjuncts = DiaDisjuncts::None;
                    return true;
                }
            }
        }
        false
    }
}

impl NnfConj {
    /// Empty conjunctions are valid
    fn new_empty() -> NnfConj {
        NnfConj {
            atoms_pos: BTreeSet::new(),
            atoms_neg: BTreeSet::new(),

            boxed_conjuncts: BoxConjuncts::None,
            diamond_conjuncts: BTreeSet::new(),
            or_conjuncts: BTreeSet::new(),
        }
    }

    fn neg(self) -> NnfDisj {
        NnfDisj {
            atoms_pos: self.atoms_neg,
            atoms_neg: self.atoms_pos,

            diamond_disjuncts: self.boxed_conjuncts.neg(),
            box_disjuncts: self
                .diamond_conjuncts
                .into_iter()
                .map(|p| p.neg())
                .collect(),
            and_disjuncts: self.or_conjuncts.into_iter().map(|p| p.neg()).collect(),
        }
    }

    fn add_precise(mut self, phi: NnfPrecise) -> Option<NnfConj> {
        match phi {
            NnfPrecise::AtomPos(i) => {
                if self.atoms_neg.contains(&i) {
                    None
                } else {
                    self.atoms_pos.insert(i);
                    Some(self)
                }
            }
            NnfPrecise::AtomNeg(i) => {
                if self.atoms_pos.contains(&i) {
                    None
                } else {
                    self.atoms_neg.insert(i);
                    Some(self)
                }
            }
            NnfPrecise::Bot => None,
            NnfPrecise::Top => Some(self),
            NnfPrecise::And(conj) => self.and(conj),
            NnfPrecise::NnfBox(phi) => {
                if *phi == NnfPrecise::Top {
                    return Some(self);
                } else if *phi == NnfPrecise::Bot && !self.diamond_conjuncts.is_empty() {
                    return None;
                }

                /* The problematic thing about this rule is, that it is "asymmetric".
                It gives "⋄top" a special role. Thus it won't interact
                confluently with the other rules.
                // Replace (Γ ∧ ⌷φ ∧ ⋄φ) by (Γ ∧ ⌷φ ∧ ⋄top)
                        if self.diamond_conjuncts.contains(&phi) {
                            self.diamond_conjuncts.remove(&phi);
                            // If there are no other `diamond_conjuncts`, we need to add a placeholder
                            if self.diamond_conjuncts.is_empty() {
                                self.diamond_conjuncts.insert(NnfPrecise::Top);
                            }
                        }*/

                self.boxed_conjuncts = self.boxed_conjuncts.add_precise(*phi);
                Some(self)
            }
            NnfPrecise::NnfDia(phi) => {
                if *phi == NnfPrecise::Bot {
                    return None;
                } else if *phi == NnfPrecise::Top && !self.diamond_conjuncts.is_empty() {
                    // If there are other `dc` than `Top`, then we can omit the `Top`
                    return Some(self);
                }

                // If there are other `dc` than `Top`, then we can omit the `Top`
                self.diamond_conjuncts.remove(&NnfPrecise::Top);
                self.diamond_conjuncts.insert(*phi);
                Some(self)
            }
            NnfPrecise::Or(mut disj) => {
                // If there is another `or_conjuncts` which differs
                // from `disj` only in the sign of an atom, then
                // simplify using distributivity.
                self.or_conjuncts.retain(|other| {
                    if let Some(i) = disj.differ_by_single_atom(other) {
                        disj.atoms_neg.remove(&i);
                        disj.atoms_pos.remove(&i);
                        false
                    } else {
                        true
                    }
                });
                //WARNING: It is possible that repeated simplifications are possible,
                //using this rule. But the current algorithm stops after one application.
                //This is only a "problem" in the multi-variable case.

                // It is possible for `([]p \/ A) /\ (<>~p \/ A) /\ B` to appear.
                // Replace this by `A /\ B`.
                // i.e. the `diamond_disjunct` of one disjunction is
                // the negation of one of the `box_disjuncts` of the other disjunction.
                // Note that `differ_by_negated_bd` changes `disj` as necessary.
                self.or_conjuncts
                    .retain(|other| !disj.differ_by_negated_bd(other));

                // Replace ⌷φ ∧ (⋄~φ ∨ Γ) ∧ Δ by ⌷φ ∧ Γ ∧ Δ.
                if self.boxed_conjuncts == disj.diamond_disjuncts.clone().neg() {
                    disj.diamond_disjuncts = DiaDisjuncts::None;
                }

                self.or_conjuncts.insert(disj);
                Some(self)
            }
        }
    }

    fn into_nnf(self) -> NNF {
        let atom_pos = self.atoms_pos.into_iter().map(NNF::AtomPos);
        let atom_neg = self.atoms_neg.into_iter().map(NNF::AtomNeg);
        let box_conj = self.boxed_conjuncts.into_nnf();
        let diamond_conjuncts = self
            .diamond_conjuncts
            .into_iter()
            .map(|dc| NNF::NnfDia(Box::new(dc.into_nnf())));
        let or_conjuncts = self.or_conjuncts.into_iter().map(NnfDisj::into_nnf);
        let vec: Vec<NNF> = atom_pos
            .chain(atom_neg)
            .chain(box_conj.into_iter())
            .chain(diamond_conjuncts)
            .chain(or_conjuncts)
            .collect();

        if vec.is_empty() {
            return NNF::Top;
        }
        if vec.len() == 1 {
            return vec.into_iter().next().unwrap();
        }

        NNF::And(vec)
    }

    fn and(mut self, conj: NnfConj) -> Option<NnfConj> {
        if !self.atoms_pos.is_disjoint(&conj.atoms_neg)
            || !self.atoms_neg.is_disjoint(&conj.atoms_pos)
        {
            return None;
        }
        self.atoms_pos.extend(conj.atoms_pos.into_iter());
        self.atoms_neg.extend(conj.atoms_neg.into_iter());

        self.boxed_conjuncts = self.boxed_conjuncts.and(conj.boxed_conjuncts);
        self.diamond_conjuncts
            .extend(conj.diamond_conjuncts.into_iter());
        self.or_conjuncts.extend(conj.or_conjuncts.into_iter());
        Some(self)
    }

    fn simpl(mut self) -> NnfPrecise {
        // first move all the "nested" parts out of `self`
        let mut boxed_conjuncts = BoxConjuncts::None;
        std::mem::swap(&mut self.boxed_conjuncts, &mut boxed_conjuncts);
        let diamond_conjuncts = std::mem::take(&mut self.diamond_conjuncts);
        let or_conjuncts = std::mem::take(&mut self.or_conjuncts);

        // now simplify the parts, while writing the results back into `self`

        for dc in diamond_conjuncts {
            let dc = dc.simpl();

            if dc == NnfPrecise::Bot {
                return NnfPrecise::Bot;
            }

            if let Some(conj) = self.add_precise(NnfPrecise::NnfDia(Box::new(dc))) {
                self = conj
            } else {
                return NnfPrecise::Bot;
            }
        }
        for or in or_conjuncts {
            let or = or.simpl();
            if let Some(conj) = self.add_precise(or) {
                self = conj;
            } else {
                return NnfPrecise::Bot;
            }
        }
        if let Some(bc) = boxed_conjuncts.simpl() {
            if bc == NnfPrecise::Bot && !self.diamond_conjuncts.is_empty() {
                return NnfPrecise::Bot;
            }

            // it is possible that `bc` implies the negation of one of
            // the formulae in `diamond_conjuncts`. in that case, the
            // whole disjunction becomes trivially valid.
            for dc in &self.diamond_conjuncts {
                if bc.clone().into_nnf() == dc.clone().into_nnf().neg() {
                    return NnfPrecise::Bot;
                }
            }

            if let Some(conj) = self.add_precise(NnfPrecise::NnfBox(Box::new(bc))) {
                self = conj;
            } else {
                return NnfPrecise::Bot;
            }
        }

        if !self.atoms_pos.is_disjoint(&self.atoms_neg) {
            return NnfPrecise::Top;
        }

        if self.atoms_pos.is_empty()
            && self.atoms_neg.is_empty()
            && self.boxed_conjuncts == BoxConjuncts::None
            && self.diamond_conjuncts.is_empty()
            && self.or_conjuncts.is_empty()
        {
            return NnfPrecise::Top;
        }
        if self.atoms_pos.len() == 1
            && self.atoms_neg.is_empty()
            && self.boxed_conjuncts == BoxConjuncts::None
            && self.diamond_conjuncts.is_empty()
            && self.or_conjuncts.is_empty()
        {
            return NnfPrecise::AtomPos(self.atoms_pos.into_iter().next().unwrap());
        }
        if self.atoms_pos.is_empty()
            && self.atoms_neg.len() == 1
            && self.boxed_conjuncts == BoxConjuncts::None
            && self.diamond_conjuncts.is_empty()
            && self.or_conjuncts.is_empty()
        {
            return NnfPrecise::AtomNeg(self.atoms_neg.into_iter().next().unwrap());
        }
        if self.atoms_pos.is_empty()
            && self.atoms_neg.is_empty()
            && self.boxed_conjuncts == BoxConjuncts::Bot
            && self.diamond_conjuncts.is_empty()
            && self.or_conjuncts.is_empty()
        {
            return NnfPrecise::NnfBox(Box::new(NnfPrecise::Bot));
        }
        if self.atoms_pos.is_empty()
            && self.atoms_neg.is_empty()
            && self.boxed_conjuncts == BoxConjuncts::None
            && self.diamond_conjuncts.len() == 1
            && self.or_conjuncts.is_empty()
        {
            return NnfPrecise::NnfDia(Box::new(
                self.diamond_conjuncts.into_iter().next().unwrap(),
            ));
        }
        NnfPrecise::And(self)
    }

    /// Returns `Some(i)` iff `self` and `other` only differ in
    /// exactly the sign of the atom `i`.  Otherwise returns `None`.
    fn differ_by_single_atom(&self, other: &NnfConj) -> Option<NnfAtom> {
        // For the below to work, we need the `atoms_pos` and `atoms_neg` to be disjoint.
        assert!(self.atoms_pos.is_disjoint(&self.atoms_neg));
        assert!(other.atoms_pos.is_disjoint(&other.atoms_neg));

        // The atoms can be compared using the symmetric difference.
        let mut pos = self.atoms_pos.symmetric_difference(&other.atoms_pos);
        let mut neg = self.atoms_neg.symmetric_difference(&other.atoms_neg);

        // We need both iterators to contain exactly one and exactly the same element.
        if let (Some(i), Some(j)) = (pos.next(), neg.next()) {
            if i == j
                && pos.next().is_none()
                && neg.next().is_none()
                && self.boxed_conjuncts == other.boxed_conjuncts
                && self.diamond_conjuncts == other.diamond_conjuncts
                && self.or_conjuncts == other.or_conjuncts
            {
                return Some(*i);
            }
        }
        None
    }

    /// If `self` and `other` are of the form
    /// `([]p /\ A)` and `(<>~p /\ A)` then return `true` and change `self` into `A`.
    /// Otherwise return `false` and do nothing.
    fn differ_by_negated_dc(&mut self, other: &NnfConj) -> bool {
        // First ensure that all other things are equal.
        if self.atoms_pos != other.atoms_pos
            || self.atoms_neg != other.atoms_neg
            || self.or_conjuncts != other.or_conjuncts
        {
            return false;
        }

        // The symmetric difference of `diamond_conjuncts` must contain exactly one element.
        let mut dc_diff = self
            .diamond_conjuncts
            .symmetric_difference(&other.diamond_conjuncts);

        // If the difference has exactly one element, then go on with `dc_diff` being that element.
        // Otherwise return.
        let dc_diff = {
            if let Some(dc) = dc_diff.next() {
                if dc_diff.next().is_none() {
                    dc
                } else {
                    return false;
                }
            } else {
                return false;
            }
        };

        // The `NnfConj` which contains `dc_diff` must have
        // `BoxConjuncts::None` while the other must have the negation
        // of `dc_diff` as `BoxConjuncts`

        if self.diamond_conjuncts.contains(dc_diff) {
            if self.boxed_conjuncts != BoxConjuncts::None {
                return false;
            }

            // `self` is ok. check `other` now.
            if *dc_diff == NnfPrecise::Top {
                if other.boxed_conjuncts == BoxConjuncts::Bot {
                    // Found a match.
                    self.diamond_conjuncts.remove(&dc_diff.clone());
                    return true;
                } else {
                    return false;
                }
            }

            if let BoxConjuncts::Some(bc) = &other.boxed_conjuncts {
                if dc_diff.clone().into_nnf().neg() == bc.clone().into_nnf() {
                    // Found a match.
                    self.diamond_conjuncts.remove(&dc_diff.clone());
                    return true;
                }
            }
        } else {
            if other.boxed_conjuncts != BoxConjuncts::None {
                return false;
            }

            // `other` is ok. check `self` now.
            if *dc_diff == NnfPrecise::Top {
                if self.boxed_conjuncts == BoxConjuncts::Bot {
                    // Found a match.
                    self.boxed_conjuncts = BoxConjuncts::None;
                    return true;
                } else {
                    return false;
                }
            }

            if let BoxConjuncts::Some(bc) = &self.boxed_conjuncts {
                if dc_diff.clone().into_nnf().neg() == bc.clone().into_nnf() {
                    // Found a match.
                    self.boxed_conjuncts = BoxConjuncts::None;
                    return true;
                }
            }
        }
        false
    }
}

impl NNF {
    /// Simplifiy the formula using some elementary facts.
    pub fn simpl(self) -> NNF {
        let precise = NnfPrecise::from_nnf(self);
        let precise = precise.simpl();
        precise.into_nnf()
    }
}

use proptest::prelude::*;

proptest! {
    #[test]
    fn simpl_equiv(a in super::arb_nnf()) {
    // simplification returns equivalent formulae
    assert!(NNF::equiv_dec(&a, &a.clone().simpl()));

    // every formula is equivalent to itself, but not to its negation
    assert!(NNF::equiv_dec(&a, &a));
    assert!(!NNF::equiv_dec(&a, &a.neg()));
    }

    #[test]
    fn neg_equiv(a in super::arb_nnf()) {
    let precise = NnfPrecise::from_nnf(a.clone());
    let double_neg = precise.clone().neg().neg();
    assert_eq!(precise, double_neg);
    assert!(NNF::equiv_dec(&precise.neg().into_nnf(), &a.neg()));
    }
}

extern crate test;
#[allow(unused_imports)]
use test::Bencher;

#[bench]
fn bench_simpl_fast(b: &mut Bencher) {
    b.iter(|| {
        crate::fineform_iter::FineFormNNFIter::new(5)
            .take(200)
            .map(NNF::simpl)
            .for_each(drop);
    });
}
