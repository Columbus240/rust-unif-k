use chrono;
use std::cmp;
use std::collections::btree_map::BTreeMap;
use std::collections::btree_set::BTreeSet;

#[allow(unused_imports)]
use rayon::prelude::*;

use crate::nnf::NNF;

#[derive(Debug, Clone, Eq, Ord, PartialEq, PartialOrd)]
pub enum FineForm {
    Top,
    Node(Box<FFNode>),
}

#[derive(Debug, Clone, Eq, Ord, PartialEq, PartialOrd)]
pub struct FFNode {
    pub atoms: BTreeMap<usize, bool>,
    pub dia_branch: Option<FineForm>,
    pub box_branches: BTreeSet<FineForm>,
}

impl FineForm {
    #[allow(dead_code)]
    pub fn bot() -> FineForm {
        FineForm::Node(Box::new(FFNode {
            atoms: BTreeMap::new(),
            dia_branch: None,
            box_branches: BTreeSet::new(),
        }))
    }

    #[allow(dead_code)]
    pub fn box_n_bot(n: usize) -> FineForm {
        if n == 0 {
            return FineForm::bot();
        }
        let dia_n_top = {
            let mut dt = FineForm::Top;
            for _ in 1..n {
                dt = dt.dia();
            }
            dt
        };
        FineForm::Node(Box::new(FFNode {
            atoms: BTreeMap::new(),
            dia_branch: None,
            box_branches: {
                let mut bb = BTreeSet::new();
                bb.insert(dia_n_top);
                bb
            },
        }))
    }

    pub fn dia(self) -> FineForm {
        FineForm::Node(Box::new(FFNode {
            atoms: BTreeMap::new(),
            dia_branch: Some(self),
            box_branches: BTreeSet::new(),
        }))
    }

    #[allow(dead_code)]
    fn degree(&self) -> usize {
        if let FineForm::Node(node) = self {
            cmp::max(
                node.dia_branch.as_ref().map_or(0, |x| x.degree() + 1),
                node.box_branches
                    .iter()
                    .fold(0, |acc, x| cmp::max(acc, x.degree() + 1)),
            )
        } else {
            0
        }
    }

    #[allow(dead_code)]
    fn len(&self) -> usize {
        if let FineForm::Node(node) = self {
            node.atoms.len()
                + node.dia_branch.as_ref().map_or(0, |x| x.len() + 1)
                + node.box_branches.iter().fold(0, |acc, x| acc + x.len() + 1)
        } else {
            1
        }
    }

    fn to_nnf_helper(i: usize, b: bool) -> NNF {
        if b {
            NNF::AtomPos(i)
        } else {
            NNF::AtomNeg(i)
        }
    }

    pub fn to_nnf(&self) -> NNF {
        if let FineForm::Node(node) = self {
            if node.atoms.is_empty() && node.dia_branch.is_none() && node.box_branches.is_empty() {
                return NNF::Bot;
            }

            let atoms = node
                .atoms
                .iter()
                .map(|(i, b)| FineForm::to_nnf_helper(*i, *b));
            let mut output = atoms.collect::<Vec<_>>();

            if let Some(dia) = &node.dia_branch {
                let dia_nnf = dia.to_nnf();
                if dia_nnf == NNF::Bot {
                    // do nothing
                } else {
                    output.push(NNF::NnfDia(Box::new(dia_nnf)));
                }
            }

            for bb in node.box_branches.iter() {
                let bb_nnf = bb.to_nnf().neg();
                if bb_nnf == NNF::Top {
                    return NNF::Top;
                }
                output.push(NNF::NnfBox(Box::new(bb_nnf)));
            }

            return NNF::Or(output);
        }
        NNF::Top
    }

    #[allow(dead_code)]
    pub fn or(&self, other: &FineForm) -> FineForm {
        match (self, other) {
            (FineForm::Top, _) => FineForm::Top,
            (_, FineForm::Top) => FineForm::Top,
            (FineForm::Node(node0), FineForm::Node(node1)) => {
                FineForm::Node(Box::new(node0.or(node1)))
            }
        }
    }

    // decides whether `self -> other` is valid.
    #[cfg(test)]
    fn impl_dec(&self, other: &FineForm) -> Option<bool> {
        if let FineForm::Node(node1) = other {
            if let FineForm::Node(node0) = self {
                node0.impl_dec(node1)
            } else {
                other.valid_dec()
            }
        } else {
            Some(true)
        }
    }

    #[cfg(test)]
    pub fn valid_dec(&self) -> Option<bool> {
        if let FineForm::Node(node) = self {
            node.valid_dec()
        } else {
            Some(true)
        }
    }

    #[cfg(test)]
    fn equiv_dec(&self, other: &FineForm) -> Option<bool> {
        if self == other {
            return Some(true);
        }

        if let FineForm::Node(node0) = self {
            if let FineForm::Node(node1) = other {
                return node0.equiv_dec(node1);
            } else {
                return node0.valid_dec();
            }
        } else {
            return other.valid_dec();
        }
    }

    #[cfg(test)]
    pub fn contradictory_dec(&self) -> Option<bool> {
        if let FineForm::Node(node) = self {
            node.contradictory_dec()
        } else {
            Some(false)
        }
    }
}

#[cfg(test)]
#[allow(dead_code)]
fn option_bool_and(a: Option<bool>, b: Option<bool>) -> Option<bool> {
    match (a, b) {
        (Some(true), Some(true)) => Some(true),
        (Some(false), _) => Some(false),
        (_, Some(false)) => Some(false),
        (None, _) => None,
        (_, None) => None,
    }
}

impl FFNode {
    fn or(&self, other: &FFNode) -> FFNode {
        let mut new_atoms = BTreeMap::new();
        new_atoms.append(&mut self.atoms.clone());
        new_atoms.append(&mut other.atoms.clone());

        // compute the diamond branch
        let dia_branch = {
            if let Some(dia0) = &self.dia_branch {
                if let Some(dia1) = &other.dia_branch {
                    Some(dia0.or(dia1))
                } else {
                    Some(dia0.clone())
                }
            } else {
                other.dia_branch.clone()
            }
        };

        FFNode {
            atoms: new_atoms,
            dia_branch: dia_branch,
            box_branches: self
                .box_branches
                .union(&other.box_branches)
                .cloned()
                .collect(),
        }
    }

    #[cfg(test)]
    fn contradictory_dec(&self) -> Option<bool> {
        // A formula with atoms is never contradictory
        if !self.atoms.is_empty() {
            return Some(false);
        }

        let mut uncertain = false;

        if let Some(dia) = &self.dia_branch {
            match dia.contradictory_dec() {
                Some(false) => return Some(false),
                Some(true) => {}
                None => uncertain = true,
            }
        }

        /* is wrong

           let bb_result = self
               .box_branches
               .iter()
               .map(|bb| bb.valid_dec())
               .fold(Some(true), option_bool_and);

           match (bb_result, uncertain) {
               (Some(false), _) => Some(false),
               (Some(true), false) => Some(true),
               (None, _) => None,
               (_, true) => None,
           }
        */
        None
    }

    #[cfg(test)]
    fn impl_dec(&self, other: &FFNode) -> Option<bool> {
        // Remove all atoms that appear with the same sign.
        let mut atoms_left = self.atoms.clone();
        let mut atoms_right = other.atoms.clone();

        for (i, b) in self.atoms.iter() {
            if let Some(b0) = atoms_right.get(i) {
                if b == b0 {
                    atoms_left.remove(i);
                    atoms_right.remove(i);
                }
            }
        }

        // If the left atoms are not empty, consider
        // the validity of the right branch (without atoms).
        if !atoms_left.is_empty() {
            return other.valid_dec();
        }

        // If the right atoms are not empty, consider
        // whether the left branch is contradictor (without atoms...).
        /*
            if !atoms_right.is_empty() {
                return self.contradictory_dec();
            }

            let mut uncertain = false;

            // otherwise consider the conjunction of the following:
            match self.or(other).valid_dec() {
                Some(false) => {
                    return Some(false);
                }
                Some(true) => {}
                None => uncertain = false,
            }

            let bb_result = if let Some(dia) = &other.dia_branch {
                other
                    .box_branches
                    .iter()
                    .map(|bb| bb.impl_dec(&dia))
                    .fold(Some(true), option_bool_and)
            } else {
                other
                    .box_branches
                    .iter()
                    .map(|bb| bb.contradictory_dec())
                    .fold(Some(true), option_bool_and)
            };

            match (bb_result, uncertain) {
                (Some(false), _) => Some(false),
                (Some(true), false) => Some(true),
                (None, _) => None,
                (_, true) => None,
            }
        */
        None
    }

    #[cfg(test)]
    fn valid_dec(&self) -> Option<bool> {
        // If all branches are empty, then the formula is contradictory => not valid.
        if self.box_branches.is_empty() && self.dia_branch.is_none() {
            return Some(false);
        }

        if self.atoms.is_empty() && !self.box_branches.is_empty() {
            if let Some(dia) = &self.dia_branch {
                let result = self.box_branches.iter().map(|bb| bb.impl_dec(dia)).fold(
                    Some(false),
                    |acc, b| match (acc, b) {
                        (Some(true), _) => Some(true),
                        (_, Some(true)) => Some(true),
                        (None, _) => None,
                        (_, None) => None,
                        (Some(false), Some(false)) => Some(false),
                    },
                );
                return result;
            } else {
                return self
                    .box_branches
                    .iter()
                    .map(|bb| bb.contradictory_dec())
                    .fold(Some(false), |acc, b| match (acc, b) {
                        (Some(true), _) => Some(true),
                        (_, Some(true)) => Some(true),
                        (None, _) => None,
                        (_, None) => None,
                        (Some(false), Some(false)) => Some(false),
                    });
            }
        }
        None
    }

    // Two non-trivial FineForms are equivalent if each of their three
    // parts are equivalent.
    // This is false, as the following example shows:
    //   ~p \/ <>T \/ []bot   == T
    // Two facts are at play here
    // - The diamond branch and one of the box branches add up to top.
    // - The atoms on the left can be ignored, because the rest is top.
    #[cfg(test)]
    fn equiv_dec(&self, other: &FFNode) -> Option<bool> {
        // first compare the atoms.
        if self.atoms != other.atoms {
            // now both formulae have to be valid, or they can't be equivalent
            let self_valid = self.valid_dec();
            let other_valid = other.valid_dec();
            match (self_valid, other_valid) {
                (Some(true), Some(true)) => return Some(true),
                (Some(false), _) => return Some(false),
                (_, Some(false)) => return Some(false),
                (None, _) => return None,
                (_, None) => return None,
            }
        }

        // special case: if the formulae are fully equal, then they
        // are equivalent
        if self.dia_branch == other.dia_branch && self.box_branches == other.box_branches {
            return Some(true);
        }

        None
    }
}

#[derive(Clone)]
struct FFPowerset {
    dia_branch: Option<FineForm>,
    box_branches: BTreeSet<FineForm>,
}

impl FFPowerset {
    fn bot() -> FFPowerset {
        FFPowerset {
            dia_branch: None,
            box_branches: BTreeSet::new(),
        }
    }

    fn to_ff(self, atoms: BTreeMap<usize, bool>) -> FineForm {
        FineForm::Node(Box::new(FFNode {
            atoms,
            dia_branch: self.dia_branch,
            box_branches: self.box_branches,
        }))
    }

    // Does `self.dia_branch = self.dia_branch || new_pos`,
    // but if any simplification would happen, return `None`.
    // We can assume (w.l.o.g.) that neither part would simplify on
    // its own.
    //
    // Because we list (up to equivalence) all `FineForm`, we never
    // have to do an actual "or" operation.
    fn try_dia_branch_or(&self, new_pos: &FineForm) -> Option<FFPowerset> {
        if NNF::equiv_dec(new_pos.to_nnf(), NNF::Bot) {
            return None;
        }

        if let Some(_) = self.dia_branch {
            return None;
        }

        // If the new branch is equivalent to some box branch, then it would simplify
        for bb in self.box_branches.iter() {
            if NNF::equiv_dec(new_pos.to_nnf(), bb.to_nnf()) {
                return None;
            }
        }

        Some(FFPowerset {
            dia_branch: Some(new_pos.clone()),
            box_branches: self.box_branches.clone(),
        })
    }

    // Does `self.box_branches = self.box_branches.insert(new_neg)`,
    // but if any simplification would happen, return `None`.
    // We can assume (w.l.o.g.) that neither part would simplify on
    // its own.
    fn try_box_branch_or(&self, new_neg: &FineForm) -> Option<FFPowerset> {
        // if `new_neg` is bot, it will appear as []top in the
        // disjunction, so it would make the disjunction valid.
        if NNF::equiv_dec(new_neg.to_nnf(), NNF::Bot) {
            return None;
        }

        // If the dia_branch is equivalent to the new branch, then
        // ⋄phi ∨ ⌷~phi = ⋄phi \/ ~⋄ phi = T
        if let Some(dia) = &self.dia_branch {
            if NNF::equiv_dec(dia.to_nnf(), new_neg.to_nnf()) {
                return None;
            }
        }

        // if `new_neg` implies any of the other branches, then a simplification is possible.
        for bb in self.box_branches.iter() {
            if NNF::impli(new_neg.to_nnf(), bb.to_nnf()).is_valid()
                || NNF::impli(bb.to_nnf(), new_neg.to_nnf()).is_valid()
            {
                return None;
            }
        }

        //DEFAULT:
        Some(FFPowerset {
            dia_branch: self.dia_branch.clone(),
            box_branches: {
                let mut b = self.box_branches.clone();
                b.insert(new_neg.clone());
                b
            },
        })
    }
}

// States of the TriplePowersetIterator
#[derive(Clone)]
enum TpiState<'a> {
    Empty(&'a (FineForm, NNF)),
    Pos(&'a (FineForm, NNF), FFPowerset),
    Neg(&'a (FineForm, NNF), FFPowerset),
    NearlyDone,
    Done,
}

#[derive(Clone)]
struct TriplePowersetIterator<'a> {
    state: TpiState<'a>,
    prev_level: Option<Box<TriplePowersetIterator<'a>>>,
}

impl<'a> TriplePowersetIterator<'a> {
    fn new(input: &'a [(FineForm, NNF)]) -> TriplePowersetIterator<'a> {
        if input.is_empty() {
            TriplePowersetIterator {
                state: TpiState::NearlyDone,
                prev_level: None,
            }
        } else {
            TriplePowersetIterator {
                state: TpiState::Empty(&input[0]),
                prev_level: Some(Box::new(TriplePowersetIterator::new(&input[1..]))),
            }
        }
    }
}

impl<'a> Iterator for TriplePowersetIterator<'a> {
    type Item = FFPowerset;
    fn next(&mut self) -> Option<FFPowerset> {
        match &mut self.state {
            TpiState::Empty(hd) => {
                if let Some(v) = {
                    if let Some(prev_level) = &mut self.prev_level {
                        prev_level.next()
                    } else {
                        None
                    }
                } {
                    self.state = TpiState::Pos(hd, v.clone());
                    Some(v)
                } else {
                    // be done
                    self.state = TpiState::NearlyDone;
                    self.prev_level = None;
                    None
                }
            }
            TpiState::Pos(hd, v) => {
                let result = v.try_dia_branch_or(&hd.0.clone());
                self.state = TpiState::Neg(hd, v.clone());
                // If the resulting `FineForm` would be simplifiable, skip it.
                // reasons for simplification:
                // - two positive elements have branches that imply eachother
                //    (there is a branch [a] in one element and a
                //    branch [b] in another s.t. [a] implies [b]
                // - two negative elements imply eachother
                // W.l.o.g. we can assume that `v` is not simplifiable
                // and that the only reason for simplifiability is the
                // form which we add. So investigate this case before creating `v2`.
                // This procedure should eliminate a lot of possibilities.
                if result.is_none() {
                    self.next()
                } else {
                    result
                }
            }
            TpiState::Neg(hd, v) => {
                let result = v.try_box_branch_or(&hd.0);
                self.state = TpiState::Empty(hd);
                // If the resulting `FineForm` would be simplifiable, skip it.
                if result.is_none() {
                    self.next()
                } else {
                    result
                }
            }
            TpiState::NearlyDone => {
                self.state = TpiState::Done;
                self.prev_level = None;
                Some(FFPowerset::bot())
            }
            TpiState::Done => {
                self.prev_level = None;
                None
            }
        }
    }
}
fn enumerate_step(
    literals: impl Iterator<Item = BTreeMap<usize, bool>>,
    input: Vec<(FineForm, NNF)>,
) -> Vec<(FineForm, NNF)> {
    let mut output = input.clone();

    let input_ff = input
        .iter()
        .map(|(ff, _nnf)| ff.clone())
        .collect::<Vec<_>>();

    let powerset = TriplePowersetIterator::new(input.as_slice());

    let start_time = chrono::offset::Local::now();

    for base in literals {
        for set in powerset.clone() {
            let new_ff = set.to_ff(base.clone());
            let new_nnf = new_ff.to_nnf();

            // only add `new_ff` if no such element exists in
            // `output`
            // If `TriplePowersetIterator` (i.e. `try_dia_branch_or`
            // and `try_box_branch_or`) can be made restrictive
            // enough, then this part should not be necessary.
            #[allow(unused_variables)]
            let opt_old_ff = output.iter().enumerate().find(|(_, (old_ff, old_nnf))| {
                // by first checking equivalence of `ff` and `new_ff` using a quick
                // but imprecise procedure, we can avoid a lot of
                // calls to the expensive `NNF::equiv_dec` function
                /*
                        if let Some(b) = old_ff.equiv_dec(&new_ff) {
                            if b != NNF::equiv_dec(old_nnf.clone(), new_ff.clone().to_nnf()) {
                                println!("failing equiv_dec. wrong answer: {}", b);
                                println!("old_nnf: {:?}", old_nnf);
                                println!("new_nnf: {:?}", new_ff.clone().to_nnf().simpl_slow());
                                panic!();
                            }
                            b
                        } else {
                */
                NNF::equiv_dec(old_nnf.clone(), new_nnf.clone())
                //}
            });

            let new_nnf = new_nnf.simpl_slow();

            if let Some((idx, (_, old_nnf))) = opt_old_ff {
                if old_nnf.len() > new_nnf.len() {
                    // replace the old_ff with the new_ff
                    output[idx] = (new_ff.clone(), new_nnf);
                }
            } else {
                output.push((new_ff.clone(), new_nnf));
                let now = chrono::offset::Local::now();
                eprintln!(
                    "output.len: {} at {}, since started {}",
                    output.len(),
                    now,
                    now.signed_duration_since(start_time)
                );
            }

            if output.len() >= 2000 {
                return output;
            }
        }
    }

    output
}

pub fn enumerate_formulae(
    literals: impl Clone + Iterator<Item = BTreeMap<usize, bool>>,
    i: usize,
) -> Vec<(FineForm, NNF)> {
    if i == 0 {
        let mut out = Vec::new();

        out.push((FineForm::Top, NNF::Top));
        for lit in literals {
            let ff = FineForm::Node(Box::new(FFNode {
                atoms: lit.clone(),
                dia_branch: None,
                box_branches: BTreeSet::new(),
            }));

            let nnf = ff.to_nnf().simpl();

            out.push((ff, nnf));
        }
        out.shrink_to_fit();
        out
    } else {
        enumerate_step(literals.clone(), enumerate_formulae(literals, i - 1))
    }
}

pub fn enumerate_unifiers(i: usize) -> Vec<(FineForm, NNF)> {
    if i == 0 {
        vec![(FineForm::Top, NNF::Top), (FineForm::bot(), NNF::Bot)]
    } else {
        enumerate_step(std::iter::once(BTreeMap::new()), enumerate_unifiers(i - 1))
    }
}

use proptest::prelude::*;

#[cfg(test)]
fn arb_ff() -> impl Strategy<Value = FineForm> {
    let leaf = Just(FineForm::Top);
    leaf.prop_recursive(
        8,   // 8 levels deep
        256, // Maximum 256 nodes
        10,  // Up to 10 items per collection
        |inner| {
            (
                prop::collection::btree_map(any::<usize>(), any::<bool>(), 0..10),
                prop::option::of(inner.clone()),
                prop::collection::btree_set(inner.clone(), 0..10),
            )
                .prop_map(|(atoms, dia_branch, box_branches)| {
                    FineForm::Node(Box::new(FFNode {
                        atoms,
                        dia_branch,
                        box_branches,
                    }))
                })
        },
    )
}

#[test]
fn test_equiv_constant() {
    let dia_top = FineForm::Node(Box::new(FFNode {
        atoms: BTreeMap::new(),
        dia_branch: Some(FineForm::Top),
        box_branches: BTreeSet::new(),
    }));
    let box_bot = FineForm::Node(Box::new(FFNode {
        atoms: BTreeMap::new(),
        dia_branch: None,
        box_branches: {
            let mut bb = BTreeSet::new();
            bb.insert(FineForm::Top);
            bb
        },
    }));

    // is equiv to:
    // <> <> T \/ [] <> T
    let a = FineForm::Node(Box::new(FFNode {
        atoms: BTreeMap::new(),
        dia_branch: Some(dia_top),
        box_branches: {
            let mut branches = BTreeSet::new();
            // insert box bottom, which gets turned into dia top.
            branches.insert(box_bot);
            branches
        },
    }));

    assert_eq!(a.to_nnf().is_valid(), false);
    if let Some(b) = a.valid_dec() {
        assert_eq!(b, false);
    }
}

proptest! {
    #[test]
    fn test_impl_dec(a in arb_ff(), b in arb_ff()) {
    let a_nnf = a.to_nnf();
    let b_nnf = b.to_nnf();

    let a_impl_b = NNF::Or(vec![b_nnf, a_nnf.neg()]);

    if let Some(b) = a.impl_dec(&b) {
        assert_eq!(a_impl_b.is_valid(), b);
    }
    }

    #[test]
    fn test_equiv(a in arb_ff(), b in arb_ff()) {
    let a_nnf = a.to_nnf();
    let b_nnf = b.to_nnf();

    // `equiv_dec` is reflexive
    if let Some(val) = a.equiv_dec(&a) {
        assert!(val);
    }

    if let Some(val) = a.equiv_dec(&FineForm::Top) {
        assert_eq!(val, a_nnf.clone().is_valid());
    }

    if let Some(val) = a.equiv_dec(&FineForm::bot()) {
        assert_eq!(val, NNF::equiv_dec(a_nnf.clone(),NNF::Bot));
    }

    if let Some(val) = a.valid_dec() {
        assert_eq!(val, a_nnf.clone().is_valid());
    }

    if let Some(val) = a.contradictory_dec() {
        assert_eq!(val, a_nnf.neg().is_valid());
    }

    // equivalence for FF agrees with equivalence of NNF, where they are defined
    if let Some(val) = a.equiv_dec(&b) {
        assert_eq!(val, NNF::equiv_dec(a_nnf, b_nnf));
    }
    }
}
