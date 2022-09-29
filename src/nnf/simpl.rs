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
    fn add_nnf(self, nnf: NNF) -> BoxConjuncts {
        match self {
            BoxConjuncts::None => {
                let new_bc = BoxConjuncts::Some(Box::new(NNF_Conj::new_empty()));
                new_bc.add_nnf(nnf)
            }
            // The box-bottom absorbs the new formula.
            BoxConjuncts::Bot => BoxConjuncts::Bot,
            BoxConjuncts::Some(nc) => {
                if let Some(new_nc) = nc.add_nnf(nnf) {
                    BoxConjuncts::Some(Box::new(new_nc))
                } else {
                    BoxConjuncts::Bot
                }
            }
        }
    }

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
    fn add_nnf(self, nnf: NNF) -> DiaDisjuncts {
        match self {
            DiaDisjuncts::None => {
                let new_dd = DiaDisjuncts::Some(Box::new(NNF_Disj::new_empty()));
                new_dd.add_nnf(nnf)
            }
            // The dia-top absorbs the new formula.
            DiaDisjuncts::Top => DiaDisjuncts::Top,
            DiaDisjuncts::Some(nd) => {
                if let Some(new_nd) = nd.add_nnf(nnf) {
                    DiaDisjuncts::Some(Box::new(new_nd))
                } else {
                    DiaDisjuncts::Top
                }
            }
        }
    }

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
    fn from_nnf(nnf: NNF) -> NNF_precise {
        match nnf {
            NNF::AtomPos(i) => NNF_precise::AtomPos(i),
            NNF::AtomNeg(i) => NNF_precise::AtomNeg(i),
            NNF::Bot => NNF_precise::Bot,
            NNF::Top => NNF_precise::Top,
            NNF::And(conjuncts) => {
                if let Some(conj) = NNF_Conj::from_nnf_vec(conjuncts) {
                    NNF_precise::And(conj)
                } else {
                    NNF_precise::Bot
                }
            }
            NNF::Or(disjuncts) => {
                if let Some(disj) = NNF_Disj::from_nnf_vec(disjuncts) {
                    NNF_precise::Or(disj)
                } else {
                    NNF_precise::Top
                }
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
                }
                self.box_disjuncts.insert(*phi);
                Some(self)
            }
            NNF_precise::And(conj) => {
                //TODO: Apply distributivity here.
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

    /// Return `None` if the result is valid.
    fn add_nnf(mut self, nnf: NNF) -> Option<NNF_Disj> {
        match nnf {
            NNF::AtomPos(i) => {
                if self.atoms_neg.contains(&i) {
                    None
                } else {
                    self.atoms_pos.insert(i);
                    Some(self)
                }
            }
            NNF::AtomNeg(i) => {
                if self.atoms_pos.contains(&i) {
                    None
                } else {
                    self.atoms_neg.insert(i);
                    Some(self)
                }
            }
            NNF::Top => None,
            NNF::Bot => Some(self),
            NNF::Or(disjuncts) => {
                let mut disj = self;
                for disjunct in disjuncts.into_iter() {
                    disj = disj.add_nnf(disjunct)?;
                }
                Some(disj)
            }
            NNF::NnfDia(phi) => {
                self.diamond_disjuncts = self.diamond_disjuncts.add_nnf(*phi);
                Some(self)
            }
            NNF::NnfBox(phi) => {
                self.box_disjuncts.insert(NNF_precise::from_nnf(*phi));
                Some(self)
            }
            NNF::And(conjuncts) => {
                if let Some(conj) = NNF_Conj::from_nnf_vec(conjuncts) {
                    self.and_disjuncts.insert(conj);
                }
                // otherwise `conj` was contradictory and thus can be removed from the conjunction
                Some(self)
            }
        }
    }

    fn from_nnf_vec(disjuncts: Vec<NNF>) -> Option<NNF_Disj> {
        let mut disj = NNF_Disj::new_empty();
        for disjunct in disjuncts.into_iter() {
            disj = disj.add_nnf(disjunct)?;
        }
        Some(disj)
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
                }
                self.diamond_conjuncts.insert(*phi);
                Some(self)
            }
            NNF_precise::Or(disj) => {
                //TODO: Apply distributivity here
                self.or_conjuncts.insert(disj);
                Some(self)
            }
        }
    }

    /// Returns `None` if the result is contradictory.
    fn add_nnf(mut self, nnf: NNF) -> Option<NNF_Conj> {
        match nnf {
            NNF::AtomPos(i) => {
                if self.atoms_neg.contains(&i) {
                    None
                } else {
                    self.atoms_pos.insert(i);
                    Some(self)
                }
            }
            NNF::AtomNeg(i) => {
                if self.atoms_pos.contains(&i) {
                    None
                } else {
                    self.atoms_neg.insert(i);
                    Some(self)
                }
            }
            NNF::Bot => None,
            NNF::Top => Some(self),
            NNF::And(conjuncts) => {
                let mut conj = self;
                for conjunct in conjuncts.into_iter() {
                    conj = conj.add_nnf(conjunct)?;
                }
                Some(conj)
            }
            NNF::NnfBox(phi) => {
                self.boxed_conjuncts = self.boxed_conjuncts.add_nnf(*phi);
                Some(self)
            }
            NNF::NnfDia(phi) => {
                self.diamond_conjuncts.insert(NNF_precise::from_nnf(*phi));
                Some(self)
            }
            NNF::Or(disjuncts) => {
                if let Some(disj) = NNF_Disj::from_nnf_vec(disjuncts) {
                    self.or_conjuncts.insert(disj);
                }
                // otherwise `disj` was valid and thus can be removed from the conjunction
                Some(self)
            }
        }
    }

    fn from_nnf_vec(conjuncts: Vec<NNF>) -> Option<NNF_Conj> {
        let mut conj = NNF_Conj::new_empty();
        for conjunct in conjuncts.into_iter() {
            conj = conj.add_nnf(conjunct)?;
        }
        Some(conj)
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
}

impl NNF {
    pub fn simpl_new(self) -> NNF {
        let precise = NNF_precise::from_nnf(self);
        let precise = precise.simpl();
        precise.into_nnf()
    }

    // the actual implementation of `simpl` and `simpl_slow`
    fn simpl_actual(self, slow: bool) -> NNF {
        match self {
            NNF::AtomPos(i) => NNF::AtomPos(i),
            NNF::AtomNeg(i) => NNF::AtomNeg(i),
            NNF::Bot => NNF::Bot,
            NNF::Top => NNF::Top,
            NNF::And(conjuncts) => {
                let mut new_conjuncts = Vec::with_capacity(conjuncts.len());

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

                    new_conjuncts.push(phi);
                }

                // Given the formula `p /\ []q` then store `p` in
                // `new_conjuncts` and `q` in `boxed_conjuncts`.
                let mut boxed_conjuncts = Vec::new();
                let mut i = 0;
                while i < new_conjuncts.len() {
                    if let NNF::NnfBox(_) = new_conjuncts[i] {
                        let phi = new_conjuncts.swap_remove(i);
                        if let NNF::NnfBox(phi_inner) = phi {
                            boxed_conjuncts.push(phi_inner);
                        } else {
                            unreachable!();
                        }
                    } else {
                        i += 1;
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
                        let boxed_conjuncts = NNF::And(new_boxed_conjuncts); //.simpl_actual(slow);
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
    assert!(NNF::equiv_dec(&a, &a.clone().simpl_new()));

    // every formula is equivalent to itself, but not to its negation
    assert!(NNF::equiv_dec(&a, &a));
    assert!(!NNF::equiv_dec(&a, &a.neg()));
    }
}
