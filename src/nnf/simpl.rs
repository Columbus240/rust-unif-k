//! Simplification shall be done in multiple steps: Destructure the formula
//! into its constituent parts, using `BTreeSet`. Then apply simplifications where possible.
//! Then put it together again using `Vec`.
//!TODO: Benchmark the two simplifying algorithms and compare them.

use super::{NnfAtom, NNF};
use std::collections::BTreeSet;

#[derive(Clone, Debug, Eq, PartialEq, PartialOrd, Ord)]
enum BoxConjuncts {
    None,
    Some(Box<NNF_Conj>),
    /// is used if box-bottom is a conjunct.
    Bot,
}

impl BoxConjuncts {
    fn add_precise(self, phi: NNF_precise) -> BoxConjuncts {
        match self {
            BoxConjuncts::None => {
                let new_bc = BoxConjuncts::Some(Box::new(NNF_Conj::new_empty()));
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

    fn simpl(self) -> Option<NNF_precise> {
        match self {
            BoxConjuncts::None => None,
            BoxConjuncts::Bot => Some(NNF_precise::Bot),
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

    fn and(mut self, disj: BoxConjuncts) -> BoxConjuncts {
        match (self, disj) {
            (BoxConjuncts::None, disj) => disj,
            (disj, BoxConjuncts::None) => disj,
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
    Some(Box<NNF_Disj>),
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

    fn simpl(self) -> Option<NNF_precise> {
        match self {
            DiaDisjuncts::None => None,
            DiaDisjuncts::Top => Some(NNF_precise::Top),
            DiaDisjuncts::Some(nd) => Some(nd.simpl()),
        }
    }

    fn add_precise(self, phi: NNF_precise) -> DiaDisjuncts {
        match self {
            DiaDisjuncts::None => {
                let new_dd = DiaDisjuncts::Some(Box::new(NNF_Disj::new_empty()));
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

    fn or(mut self, disj: DiaDisjuncts) -> DiaDisjuncts {
        match (self, disj) {
            (DiaDisjuncts::None, disj) => disj,
            (disj, DiaDisjuncts::None) => disj,
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
enum NNF_precise {
    AtomPos(NnfAtom),
    AtomNeg(NnfAtom),
    Bot,
    Top,
    NnfBox(Box<NNF_precise>),
    NnfDia(Box<NNF_precise>),
    And(NNF_Conj),
    Or(NNF_Disj),
}

impl NNF_precise {
    fn and(self, other: NNF_precise) -> NNF_precise {
        match (self, other) {
            (NNF_precise::Bot, _) | (_, NNF_precise::Bot) => NNF_precise::Bot,
            (NNF_precise::Top, other) | (other, NNF_precise::Top) => other,
            (NNF_precise::And(conj), other) | (other, NNF_precise::And(conj)) => {
                if let Some(conj) = conj.add_precise(other) {
                    NNF_precise::And(conj)
                } else {
                    NNF_precise::Bot
                }
            }
            (a, b) => {
                let conj = NNF_Conj::new_empty();
                if let Some(conj) = conj.add_precise(a) {
                    if let Some(conj) = conj.add_precise(b) {
                        return NNF_precise::And(conj);
                    }
                }
                NNF_precise::Bot
            }
        }
    }

    fn or(self, other: NNF_precise) -> NNF_precise {
        match (self, other) {
            (NNF_precise::Top, _) | (_, NNF_precise::Top) => NNF_precise::Top,
            (NNF_precise::Bot, other) | (other, NNF_precise::Bot) => other,
            (NNF_precise::Or(disj), other) | (other, NNF_precise::Or(disj)) => {
                if let Some(disj) = disj.add_precise(other) {
                    NNF_precise::Or(disj)
                } else {
                    NNF_precise::Top
                }
            }
            (a, b) => {
                let disj = NNF_Disj::new_empty();
                if let Some(disj) = disj.add_precise(a) {
                    if let Some(disj) = disj.add_precise(b) {
                        return NNF_precise::Or(disj);
                    }
                }
                NNF_precise::Top
            }
        }
    }

    fn from_nnf(nnf: NNF) -> NNF_precise {
        match nnf {
            NNF::AtomPos(i) => NNF_precise::AtomPos(i),
            NNF::AtomNeg(i) => NNF_precise::AtomNeg(i),
            NNF::Bot => NNF_precise::Bot,
            NNF::Top => NNF_precise::Top,
            NNF::And(conjuncts) => {
                let mut base: NNF_precise = NNF_precise::Top;
                for conjunct in conjuncts {
                    base = base.and(NNF_precise::from_nnf(conjunct));
                }
                base
            }
            NNF::Or(disjuncts) => {
                let mut base: NNF_precise = NNF_precise::Bot;
                for disjunct in disjuncts {
                    base = base.or(NNF_precise::from_nnf(disjunct));
                }
                base
            }
            NNF::NnfBox(phi) => {
                let phi = NNF_precise::from_nnf(*phi);
                if phi == NNF_precise::Top {
                    NNF_precise::Top
                } else {
                    NNF_precise::NnfBox(Box::new(phi))
                }
            }
            NNF::NnfDia(phi) => {
                let phi = NNF_precise::from_nnf(*phi);
                if phi == NNF_precise::Bot {
                    NNF_precise::Bot
                } else {
                    NNF_precise::NnfDia(Box::new(phi))
                }
            }
        }
    }

    fn into_nnf(self) -> NNF {
        match self {
            NNF_precise::AtomPos(i) => NNF::AtomPos(i),
            NNF_precise::AtomNeg(i) => NNF::AtomNeg(i),
            NNF_precise::Bot => NNF::Bot,
            NNF_precise::Top => NNF::Top,
            NNF_precise::NnfBox(phi) => NNF::NnfBox(Box::new(phi.into_nnf())),
            NNF_precise::NnfDia(phi) => NNF::NnfDia(Box::new(phi.into_nnf())),
            NNF_precise::And(conj) => conj.into_nnf(),
            NNF_precise::Or(disj) => disj.into_nnf(),
        }
    }

    fn simpl(self) -> NNF_precise {
        match self {
            NNF_precise::AtomPos(i) => NNF_precise::AtomPos(i),
            NNF_precise::AtomNeg(i) => NNF_precise::AtomNeg(i),
            NNF_precise::Bot => NNF_precise::Bot,
            NNF_precise::Top => NNF_precise::Top,
            NNF_precise::NnfBox(phi) => {
                let phi = phi.simpl();
                if phi == NNF_precise::Top {
                    NNF_precise::Top
                } else {
                    NNF_precise::NnfBox(Box::new(phi))
                }
            }
            NNF_precise::NnfDia(phi) => {
                let phi = phi.simpl();
                if phi == NNF_precise::Bot {
                    NNF_precise::Bot
                } else {
                    NNF_precise::NnfDia(Box::new(phi))
                }
            }
            NNF_precise::And(conj) => conj.simpl(),
            NNF_precise::Or(disj) => disj.simpl(),
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, PartialOrd, Ord)]
struct NNF_Conj {
    atoms_pos: BTreeSet<NnfAtom>,
    atoms_neg: BTreeSet<NnfAtom>,

    boxed_conjuncts: BoxConjuncts,
    diamond_conjuncts: BTreeSet<NNF_precise>,
    or_conjuncts: BTreeSet<NNF_Disj>,
}

#[derive(Clone, Debug, Eq, PartialEq, PartialOrd, Ord)]
struct NNF_Disj {
    atoms_pos: BTreeSet<NnfAtom>,
    atoms_neg: BTreeSet<NnfAtom>,

    diamond_disjuncts: DiaDisjuncts,
    box_disjuncts: BTreeSet<NNF_precise>,
    and_disjuncts: BTreeSet<NNF_Conj>,
}

impl NNF_Disj {
    /// Empty disjunctions are contradictory
    fn new_empty() -> NNF_Disj {
        NNF_Disj {
            atoms_pos: BTreeSet::new(),
            atoms_neg: BTreeSet::new(),

            diamond_disjuncts: DiaDisjuncts::None,
            box_disjuncts: BTreeSet::new(),
            and_disjuncts: BTreeSet::new(),
        }
    }

    fn add_precise(mut self, phi: NNF_precise) -> Option<NNF_Disj> {
        match phi {
            NNF_precise::AtomPos(i) => {
                if self.atoms_neg.contains(&i) {
                    None
                } else {
                    self.atoms_pos.insert(i);
                    Some(self)
                }
            }
            NNF_precise::AtomNeg(i) => {
                if self.atoms_pos.contains(&i) {
                    None
                } else {
                    self.atoms_neg.insert(i);
                    Some(self)
                }
            }
            NNF_precise::Top => None,
            NNF_precise::Bot => Some(self),
            NNF_precise::Or(disj) => self.or(disj),
            NNF_precise::NnfDia(phi) => {
                if *phi == NNF_precise::Bot {
                    return Some(self);
                }
                self.diamond_disjuncts = self.diamond_disjuncts.add_precise(*phi);
                Some(self)
            }
            NNF_precise::NnfBox(phi) => {
                if *phi == NNF_precise::Top {
                    return None;
                } else if *phi == NNF_precise::Bot && !self.box_disjuncts.is_empty() {
                    // If there are other `bd` than `Bot`, then we can omit the `Bot`
                    return Some(self);
                }
                // If there are other `bd` than `Bot`, then we can omit the `Bot`
                self.box_disjuncts.remove(&NNF_precise::Bot);

                self.box_disjuncts.insert(*phi);
                Some(self)
            }
            NNF_precise::And(mut conj) => {
                // If there is another `and_disjunts` which differs
                // from `conj` only in the sign of an atom, then
                // simplify using distributivity.
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
                }
                self.and_disjuncts.insert(conj);
                Some(self)
            }
        }
    }

    fn or(mut self, disj: NNF_Disj) -> Option<NNF_Disj> {
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

    fn simpl(mut self) -> NNF_precise {
        // first move all the "nested" parts out of `self`
        let mut diamond_disjuncts = DiaDisjuncts::None;
        std::mem::swap(&mut self.diamond_disjuncts, &mut diamond_disjuncts);
        let box_disjuncts = std::mem::take(&mut self.box_disjuncts);
        let and_disjuncts = std::mem::take(&mut self.and_disjuncts);

        // now simplify the parts, while writing the results back into `self`
        for bd in box_disjuncts.into_iter() {
            let bd = bd.simpl();

            if bd == NNF_precise::Top {
                return NNF_precise::Top;
            }

            if let Some(disj) = self.add_precise(NNF_precise::NnfBox(Box::new(bd))) {
                self = disj
            } else {
                return NNF_precise::Top;
            }
        }
        for ad in and_disjuncts.into_iter() {
            let ad = ad.simpl();
            if let Some(disj) = self.add_precise(ad) {
                self = disj;
            } else {
                return NNF_precise::Top;
            }
        }
        if let Some(dd) = diamond_disjuncts.simpl() {
            //TODO: Enforce this rule in `add_precise`
            if dd == NNF_precise::Top && !self.box_disjuncts.is_empty() {
                return NNF_precise::Top;
            }

            // it is possible that `dd` implies the negation of one of
            // the formulae in `box_disjuncts`. in that case, the
            // whole disjunction becomes trivially valid.
            for bd in self.box_disjuncts.iter() {
                if dd.clone().into_nnf() == bd.clone().into_nnf().neg() {
                    return NNF_precise::Top;
                }
            }

            if let Some(disj) = self.add_precise(NNF_precise::NnfDia(Box::new(dd))) {
                self = disj;
            } else {
                return NNF_precise::Top;
            }
        }

        if !self.atoms_pos.is_disjoint(&self.atoms_neg) {
            return NNF_precise::Top;
        }

        if self.atoms_pos.is_empty()
            && self.atoms_neg.is_empty()
            && self.diamond_disjuncts == DiaDisjuncts::None
            && self.box_disjuncts.is_empty()
            && self.and_disjuncts.is_empty()
        {
            return NNF_precise::Bot;
        }
        if self.atoms_pos.len() == 1
            && self.atoms_neg.is_empty()
            && self.diamond_disjuncts == DiaDisjuncts::None
            && self.box_disjuncts.is_empty()
            && self.and_disjuncts.is_empty()
        {
            return NNF_precise::AtomPos(self.atoms_pos.into_iter().next().unwrap());
        }
        if self.atoms_pos.is_empty()
            && self.atoms_neg.len() == 1
            && self.diamond_disjuncts == DiaDisjuncts::None
            && self.box_disjuncts.is_empty()
            && self.and_disjuncts.is_empty()
        {
            return NNF_precise::AtomNeg(self.atoms_neg.into_iter().next().unwrap());
        }
        if self.atoms_pos.is_empty()
            && self.atoms_neg.is_empty()
            && self.diamond_disjuncts == DiaDisjuncts::Top
            && self.box_disjuncts.is_empty()
            && self.and_disjuncts.is_empty()
        {
            return NNF_precise::NnfDia(Box::new(NNF_precise::Top));
        }
        NNF_precise::Or(self)
    }

    fn into_nnf(self) -> NNF {
        let atom_pos = self.atoms_pos.into_iter().map(NNF::AtomPos);
        let atom_neg = self.atoms_neg.into_iter().map(NNF::AtomNeg);
        let dia_disj = self.diamond_disjuncts.into_nnf();
        let box_disjuncts = self
            .box_disjuncts
            .into_iter()
            .map(|dc| NNF::NnfBox(Box::new(dc.into_nnf())));
        let and_disjuncts = self.and_disjuncts.into_iter().map(NNF_Conj::into_nnf);

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
    fn differ_by_single_atom(&self, other: &NNF_Disj) -> Option<NnfAtom> {
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
                && self.diamond_disjuncts == other.diamond_disjuncts
                && self.box_disjuncts == other.box_disjuncts
                && self.and_disjuncts == other.and_disjuncts
            {
                return Some(*i);
            }
        }
        None
    }
}

impl NNF_Conj {
    /// Empty conjunctions are valid
    fn new_empty() -> NNF_Conj {
        NNF_Conj {
            atoms_pos: BTreeSet::new(),
            atoms_neg: BTreeSet::new(),

            boxed_conjuncts: BoxConjuncts::None,
            diamond_conjuncts: BTreeSet::new(),
            or_conjuncts: BTreeSet::new(),
        }
    }

    fn add_precise(mut self, phi: NNF_precise) -> Option<NNF_Conj> {
        match phi {
            NNF_precise::AtomPos(i) => {
                if self.atoms_neg.contains(&i) {
                    None
                } else {
                    self.atoms_pos.insert(i);
                    Some(self)
                }
            }
            NNF_precise::AtomNeg(i) => {
                if self.atoms_pos.contains(&i) {
                    None
                } else {
                    self.atoms_neg.insert(i);
                    Some(self)
                }
            }
            NNF_precise::Bot => None,
            NNF_precise::Top => Some(self),
            NNF_precise::And(conj) => self.and(conj),
            NNF_precise::NnfBox(phi) => {
                if *phi == NNF_precise::Top {
                    return Some(self);
                }
                self.boxed_conjuncts = self.boxed_conjuncts.add_precise(*phi);
                Some(self)
            }
            NNF_precise::NnfDia(phi) => {
                if *phi == NNF_precise::Bot {
                    return None;
                } else if *phi == NNF_precise::Top && !self.diamond_conjuncts.is_empty() {
                    // If there are other `dc` than `Top`, then we can omit the `Top`
                    return Some(self);
                }
                // If there are other `dc` than `Top`, then we can omit the `Top`
                self.diamond_conjuncts.remove(&NNF_precise::Top);
                self.diamond_conjuncts.insert(*phi);
                Some(self)
            }
            NNF_precise::Or(mut disj) => {
                // If there is another `or_conjuncts` which differs
                // from `disj` only in the sign of an atom, then
                // simplify using distributivity.
                let mut atom = None;
                self.or_conjuncts.retain(|other| {
                    if atom.is_some() {
                        return true;
                    }
                    if let Some(i) = disj.differ_by_single_atom(other) {
                        atom = Some(i);
                        false
                    } else {
                        true
                    }
                });
                if let Some(i) = atom {
                    disj.atoms_neg.remove(&i);
                    disj.atoms_pos.remove(&i);
                }
                //TODO: Apply distributivity here
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
        let or_conjuncts = self.or_conjuncts.into_iter().map(NNF_Disj::into_nnf);
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

    fn and(mut self, conj: NNF_Conj) -> Option<NNF_Conj> {
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

    fn simpl(mut self) -> NNF_precise {
        // first move all the "nested" parts out of `self`
        let mut boxed_conjuncts = BoxConjuncts::None;
        std::mem::swap(&mut self.boxed_conjuncts, &mut boxed_conjuncts);
        let diamond_conjuncts = std::mem::take(&mut self.diamond_conjuncts);
        let or_conjuncts = std::mem::take(&mut self.or_conjuncts);

        // now simplify the parts, while writing the results back into `self`

        for dc in diamond_conjuncts.into_iter() {
            let dc = dc.simpl();

            if dc == NNF_precise::Bot {
                return NNF_precise::Bot;
            }

            if let Some(conj) = self.add_precise(NNF_precise::NnfDia(Box::new(dc))) {
                self = conj
            } else {
                return NNF_precise::Bot;
            }
        }
        for or in or_conjuncts.into_iter() {
            let or = or.simpl();
            if let Some(conj) = self.add_precise(or) {
                self = conj;
            } else {
                return NNF_precise::Bot;
            }
        }
        if let Some(bc) = boxed_conjuncts.simpl() {
            //TODO: Enforce this rule in `add_precise`
            if bc == NNF_precise::Bot && !self.diamond_conjuncts.is_empty() {
                return NNF_precise::Bot;
            }

            // it is possible that `bc` implies the negation of one of
            // the formulae in `diamond_conjuncts`. in that case, the
            // whole disjunction becomes trivially valid.
            for dc in self.diamond_conjuncts.iter() {
                if bc.clone().into_nnf() == dc.clone().into_nnf().neg() {
                    return NNF_precise::Bot;
                }
            }

            if let Some(conj) = self.add_precise(NNF_precise::NnfBox(Box::new(bc))) {
                self = conj;
            } else {
                return NNF_precise::Bot;
            }
        }

        if !self.atoms_pos.is_disjoint(&self.atoms_neg) {
            return NNF_precise::Top;
        }

        if self.atoms_pos.is_empty()
            && self.atoms_neg.is_empty()
            && self.boxed_conjuncts == BoxConjuncts::None
            && self.diamond_conjuncts.is_empty()
            && self.or_conjuncts.is_empty()
        {
            return NNF_precise::Top;
        }
        if self.atoms_pos.len() == 1
            && self.atoms_neg.is_empty()
            && self.boxed_conjuncts == BoxConjuncts::None
            && self.diamond_conjuncts.is_empty()
            && self.or_conjuncts.is_empty()
        {
            return NNF_precise::AtomPos(self.atoms_pos.into_iter().next().unwrap());
        }
        if self.atoms_pos.is_empty()
            && self.atoms_neg.len() == 1
            && self.boxed_conjuncts == BoxConjuncts::None
            && self.diamond_conjuncts.is_empty()
            && self.or_conjuncts.is_empty()
        {
            return NNF_precise::AtomNeg(self.atoms_neg.into_iter().next().unwrap());
        }
        if self.atoms_pos.is_empty()
            && self.atoms_neg.is_empty()
            && self.boxed_conjuncts == BoxConjuncts::Bot
            && self.diamond_conjuncts.is_empty()
            && self.or_conjuncts.is_empty()
        {
            return NNF_precise::NnfBox(Box::new(NNF_precise::Bot));
        }
        NNF_precise::And(self)
    }

    /// Returns `Some(i)` iff `self` and `other` only differ in
    /// exactly the sign of the atom `i`.  Otherwise returns `None`.
    fn differ_by_single_atom(&self, other: &NNF_Conj) -> Option<NnfAtom> {
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
}

impl NNF {
    pub fn simpl(self) -> NNF {
        let precise = NNF_precise::from_nnf(self);
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
}

extern crate test;
#[allow(unused_imports)]
use test::Bencher;

#[bench]
fn bench_simpl_fast(b: &mut Bencher) {
    b.iter(|| {
        crate::fineform_correct::FineFormIter::new(5)
            .take(200)
            .map(NNF::simpl)
            .for_each(drop);
    });
}
