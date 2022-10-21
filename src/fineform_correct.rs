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

/// Invariant: the number of bits of `prev_level_powerset` is always equal to `prev_level.len()`.
/// Invariant: the number of bits of `literals_powerset` is always equal to `num_variables`.
#[derive(Debug)]
pub struct FineFormIter {
    // The number of variables to use
    num_variables: NnfAtom,
    literals_powerset: PowersetIter,
    prev_level: Vec<NNF>,
    prev_level_powerset: Peekable<PowersetIter>,
    curr_level_formulae: Vec<NNF>,
    curr_level: usize,

    full_powerset: Option<BigInt>,
}

impl FineFormIter {
    pub fn new(num_variables: NnfAtom) -> FineFormIter {
        FineFormIter {
            num_variables,
            literals_powerset: PowersetIter::new(num_variables as usize),
            prev_level: Vec::new(),
            prev_level_powerset: PowersetIter::new(0).peekable(),
            curr_level_formulae: Vec::new(),
            curr_level: 0,
            full_powerset: None,
        }
    }

    pub fn get_curr_level(&self) -> usize {
        self.curr_level
    }

    pub fn get_curr_level_len(&self) -> usize {
        self.curr_level_formulae.len()
    }

    /// Returns `true` if a new level would have to start. I.e. iff `self.prev_level_powerset` is empty.
    /// Otherwise it returns `false` and adds the next "normal form" to `self.curr_level_formulae`.
    fn generate_next_formula_curr_level(&mut self) -> bool {
        // Only advance the `prev_level_powerset` if
        // `literals_powerset` runs out.

        // Peek into `prev_level_powerset` to obtain
        // instructions, about the sign of the previous level.
        let prev_set = self.prev_level_powerset.peek();
        if prev_set.is_none() {
            // `prev_level_powerset` is empty now. So we are done with this level.
            return true;
        }
        let prev_set = prev_set.unwrap();

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
            self.curr_level_formulae.push(out);
            false
        } else {
            // We are done with this set of formulae from the previous level.
            // Go to the next.
            self.prev_level_powerset.next();
            // And reset the literals iterator.
            self.literals_powerset = PowersetIter::new(self.num_variables as usize);
            // Then return the next element of this level.
            self.generate_next_formula_curr_level()
        }
    }

    /// Returns true, if a new level started
    #[allow(dead_code)]
    fn generate_next_formula(&mut self) -> bool {
        if self.generate_next_formula_curr_level() {
            self.prepare_next_level();
            true
        } else {
            // No new level started, so return `false`
            false
        }
    }

    /// Output the next formula iff it is on the current level.
    pub fn next_curr_level(&mut self) -> Option<NNF> {
        if self.full_powerset.is_none() {
            self.full_powerset = Some(BigInt::zero());
            return Some(NNF::Top);
        }

        let full_powerset = self.full_powerset.as_ref().unwrap();

        if full_powerset.bits() > self.curr_level_formulae.len() as u64 {
            // generate a new formula and if the level didn't change, output the next formula
            if !self.generate_next_formula_curr_level() {
                return self.next_curr_level();
            } else {
                return None;
            }
        }

        // Otherwise return the next formula.
        let bitvec = bigint_to_bitvec(full_powerset.clone(), full_powerset.bits() as usize);
        let mut formula_vec = Vec::with_capacity(full_powerset.bits() as usize);

        for (b, nnf) in bitvec.iter().zip(self.curr_level_formulae.iter()) {
            if *b {
                formula_vec.push(nnf.clone());
            }
        }

        self.full_powerset = Some(full_powerset + BigInt::one());
        Some(NNF::Or(formula_vec))
    }

    pub fn prepare_next_level(&mut self) {
        assert!(self.prev_level_powerset.peek().is_none());
        // `prev_level_powerset` is empty now. So we are done with this level.
        self.prev_level.clear();
        // this empties `self.curr_level_formulae` into `self.prev_level`
        self.prev_level.append(&mut self.curr_level_formulae);
        self.curr_level += 1;
        // the `literals_powerset` iterator is still fresh, so no need to update it.
        self.prev_level_powerset = PowersetIter::new(self.prev_level.len()).peekable();
        self.full_powerset = Some(BigInt::one());
    }
}

impl Iterator for FineFormIter {
    type Item = NNF;
    fn next(&mut self) -> Option<NNF> {
        if let Some(formula) = self.next_curr_level() {
            return Some(formula);
        }

        self.prepare_next_level();
        self.next()
    }
}

/// Generates a `Vec` of all formulae in fineform of modal degree at
/// most `max_modal_degree`.
#[allow(dead_code)]
pub fn fineform_bounded_level(num_vars: NnfAtom, max_modal_degree: usize) -> Vec<NNF> {
    let mut ff_iter = FineFormIter::new(num_vars);
    let mut output = Vec::new();

    loop {
        if ff_iter.get_curr_level() > max_modal_degree {
            break;
        }
        output.push(ff_iter.next().unwrap());
    }

    output
}
