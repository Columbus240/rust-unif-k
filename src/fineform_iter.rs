use bitvec::prelude::*;
use core::ops::Shr;
use num_bigint::*;
use num_traits::identities::{One, Zero};

use crate::nnf::*;

use std::iter::Peekable;

#[derive(Debug)]
pub struct PowersetIter {
    num_bits: usize,
    state: Option<BigInt>,
}

impl PowersetIter {
    pub fn new(num_bits: usize) -> PowersetIter {
        PowersetIter {
            num_bits,
            state: Some(BigInt::zero()),
        }
    }
}

fn bigint_to_bitvec(mut int: BigInt, len: usize) -> BitVec<u32> {
    let mut bitvec = BitVec::with_capacity(int.bits() as usize);
    for _ in 0..len {
        // Push the last bit of `int_state` to `bitvec`
        bitvec.push((int.clone() % 2) == BigInt::one());
        // Then shift `int` to the right by one step.
        int = int.shr(1);
    }
    bitvec
}

impl Iterator for PowersetIter {
    type Item = BitVec<u32>;
    fn next(&mut self) -> Option<BitVec<u32>> {
        if let Some(state) = &mut self.state {
            // If `state` has more bits than there are
            // `self.num_bits` then abort and end the iteration.
            if state.bits() > self.num_bits.try_into().unwrap() {
                self.state = None;
                return None;
            }

            // Convert the number `state` to a `BitVec` of length `self.num_bits`
            // Then increment `state` by one
            // Then return the `BitVec` we created.

            let bitvec = bigint_to_bitvec(state.clone(), self.num_bits);

            *state += 1;
            Some(bitvec)
        } else {
            None
        }
    }
}

/// Lists all the basic fine forms of a certain level (as `NNF`).
/// The basic fine forms of the previous level must be given as an
/// argument (as `Vec<NNF>`), this struct does not keep track of that.
///
/// Invariant: the number of bits of `prev_level_powerset` is always equal to `prev_level.len()`.
/// Invariant: the number of bits of `literals_powerset` is always equal to `num_variables`.
#[derive(Debug)]
struct BasicLevelFineFormNNFIter {
    // The number of variables to use
    num_variables: NnfAtom,
    literals_powerset: PowersetIter,
    prev_level: Vec<NNF>,
    prev_level_powerset: Peekable<PowersetIter>,
    curr_level_formulae: Vec<NNF>,
}

impl BasicLevelFineFormNNFIter {
    pub fn new(num_variables: NnfAtom, prev_level: Vec<NNF>) -> BasicLevelFineFormNNFIter {
        // Allocate some space for `curr_level_formulae` by default, but
        // not too much.
        let prev_level_len = prev_level.len();
        let curr_level_formulae_len =
            (num_variables as usize) * (usize::pow(2, usize::min(prev_level_len, 16) as u32));
        BasicLevelFineFormNNFIter {
            num_variables,
            literals_powerset: PowersetIter::new(num_variables as usize),
            prev_level,
            prev_level_powerset: PowersetIter::new(prev_level_len).peekable(),
            curr_level_formulae: Vec::with_capacity(curr_level_formulae_len),
        }
    }
}

impl Iterator for BasicLevelFineFormNNFIter {
    type Item = NNF;
    fn next(&mut self) -> Option<NNF> {
        // Only advance `prev_level_powerset` if `literals_powerset` runs out.

        // Peek into `prev_level_powerset` to obtain instructions
        // about the signs for the formulae of the previous level.
        // Early return, if we are done.
        let prev_set = self.prev_level_powerset.peek()?;

        if let Some(literals_set) = self.literals_powerset.next() {
            let mut literals_vec = Vec::with_capacity(literals_set.len() + self.prev_level.len());
            for (i, b) in literals_set.iter().enumerate() {
                if *b {
                    literals_vec.push(NNF::AtomPos(i as NnfAtom));
                } else {
                    literals_vec.push(NNF::AtomNeg(i as NnfAtom));
                }
            }
            for (b, nnf) in prev_set.iter().zip(self.prev_level.iter()) {
                if *b {
                    literals_vec.push(NNF::NnfDia(Box::new(nnf.clone())));
                } else {
                    literals_vec.push(NNF::NnfBox(Box::new(nnf.neg())));
                }
            }

            let out: NNF = NNF::And(literals_vec).simpl();
            self.curr_level_formulae.push(out.clone());
            Some(out)
        } else {
            // All literals have been used, advance `prev_level_powerset` and
            // prepare `literals_powerset`.
            self.prev_level_powerset.next();
            self.literals_powerset = PowersetIter::new(self.num_variables as usize);
            // then return the next formula
            self.next()
        }
    }
}

/// Lists all basic Fine forms (as `NNF`)
pub struct BasicFineFormNNFIter {
    internal_iter: BasicLevelFineFormNNFIter,
    curr_level: usize,
}

impl BasicFineFormNNFIter {
    pub fn new(num_variables: NnfAtom) -> BasicFineFormNNFIter {
        BasicFineFormNNFIter {
            internal_iter: BasicLevelFineFormNNFIter::new(num_variables, Vec::new()),
            curr_level: 0,
        }
    }

    pub fn get_curr_level(&self) -> usize {
        self.curr_level
    }
}

impl Iterator for BasicFineFormNNFIter {
    type Item = NNF;
    fn next(&mut self) -> Option<NNF> {
        // Return the next formula from the internal iterator
        if let Some(nnf) = self.internal_iter.next() {
            return Some(nnf);
        }
        // If there is no such formula, prepare the next level.
        self.curr_level += 1;
        let new_internal_iter = BasicLevelFineFormNNFIter::new(
            self.internal_iter.num_variables,
            std::mem::take(&mut self.internal_iter.curr_level_formulae),
        );
        self.internal_iter = new_internal_iter;
        self.next()
    }
}

/// Iterates over all modal formulae in Fine Normal Form
/// (i.e. disjunctions of basic Fine Forms) of a certain level.
#[derive(Debug)]
struct LevelFineFormNNFIter {
    internal_iter: BasicLevelFineFormNNFIter,
    full_powerset: BigInt,
}

impl LevelFineFormNNFIter {
    /// `prev_level` shall contain the basic normal forms of the previous level.
    /// If `prev_level` is not empty, then `NNF::Bot` (empty
    /// disjunction) will not be listed. No particular effort is made to list `NNF::Top`.
    fn new(num_variables: NnfAtom, prev_level: Vec<NNF>) -> LevelFineFormNNFIter {
        // This could be replaced by `full_powerset = BigInt::zero()`,
        // but this would break compatibility to the old code.
        let full_powerset = if prev_level.is_empty() {
            BigInt::zero()
        } else {
            BigInt::one()
        };

        LevelFineFormNNFIter {
            internal_iter: BasicLevelFineFormNNFIter::new(num_variables, prev_level),
            full_powerset,
        }
    }
}

impl Iterator for LevelFineFormNNFIter {
    type Item = NNF;
    fn next(&mut self) -> Option<NNF> {
        if self.full_powerset.bits() > self.internal_iter.curr_level_formulae.len() as u64 {
            // generate a new formula and if the level didn't change, output the next formula
            if self.internal_iter.next().is_some() {
                return self.next();
            } else {
                return None;
            }
        }

        // Otherwise return the next formula
        let bitvec = bigint_to_bitvec(
            self.full_powerset.clone(),
            self.full_powerset.bits() as usize,
        );
        let mut formula_vec = Vec::with_capacity(self.full_powerset.bits() as usize);
        for (b, nnf) in bitvec
            .iter()
            .zip(self.internal_iter.curr_level_formulae.iter())
        {
            if *b {
                formula_vec.push(nnf.clone());
            }
        }

        self.full_powerset += BigInt::one();
        Some(NNF::Or(formula_vec))
    }
}

/// Iterates over all modal formulae in Fine Normal Form
/// (i.e. disjunctions of basic Fine Forms).
#[derive(Debug)]
pub struct FineFormNNFIter {
    first_step: bool,
    internal_iter: LevelFineFormNNFIter,
    curr_level: usize,
}

impl FineFormNNFIter {
    pub fn new(num_variables: NnfAtom) -> FineFormNNFIter {
        FineFormNNFIter {
            first_step: true,
            internal_iter: LevelFineFormNNFIter::new(num_variables, Vec::new()),
            curr_level: 0,
        }
    }

    pub fn get_curr_level(&self) -> usize {
        self.curr_level
    }

    pub fn get_curr_level_len(&self) -> usize {
        self.internal_iter.internal_iter.curr_level_formulae.len()
    }
}

impl Iterator for FineFormNNFIter {
    type Item = NNF;
    fn next(&mut self) -> Option<NNF> {
        // On the very first step, always output `NNF::Top`.
        // Note that this mechanism could be removed, because
        // `NNF::Top` always appears on the first level.
        // This is only kept to be backwards compatible with the previous `FineFormIter`.
        if self.first_step {
            self.first_step = false;
            return Some(NNF::Top);
        }

        // Return the next formula from the internal iterator
        if let Some(nnf) = self.internal_iter.next() {
            return Some(nnf);
        }
        // If there is no such formula, prepare the next level.
        self.curr_level += 1;
        let new_internal_iter = LevelFineFormNNFIter::new(
            self.internal_iter.internal_iter.num_variables,
            std::mem::take(&mut self.internal_iter.internal_iter.curr_level_formulae),
        );
        self.internal_iter = new_internal_iter;
        self.next()
    }
}
