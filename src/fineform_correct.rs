use bitvec::prelude::*;
use core::ops::Shr;
use num_bigint::*;
use num_traits::identities::{One, Zero};

use crate::nnf::*;

use std::iter::Peekable;

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

fn bigint_to_bitvec(mut int : BigInt, len: usize) -> BitVec<u32> {
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
pub struct FineFormIter {
    // The number of variables to use
    num_variables: usize,
    literals_powerset: PowersetIter,
    prev_level: Vec<NNF>,
    prev_level_powerset: Peekable<PowersetIter>,
    curr_level_formulae: Vec<NNF>,
    curr_level: usize,

    full_powerset: Option<BigInt>,
}

impl FineFormIter {
    pub fn new(num_variables: usize) -> FineFormIter {
        FineFormIter {
            num_variables,
            literals_powerset: PowersetIter::new(num_variables),
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

    // Returns true, if a new level started
    fn generate_next_formula_real(&mut self, new_level: bool) -> bool {
        // Only advance the `prev_level_powerset` if
        // `literals_powerset` runs out

        // Peek into `prev_level_powerset` to obtain
        // instructions, about the sign of the previous level.
        if let Some(prev_set) = self.prev_level_powerset.peek() {
            if let Some(literals_set) = self.literals_powerset.next() {
                let mut literals_vec =
                    Vec::with_capacity(literals_set.len() + self.prev_level.len());
                for (i, b) in literals_set.iter().enumerate() {
                    if *b {
                        literals_vec.push(NNF::AtomPos(i));
                    } else {
                        literals_vec.push(NNF::AtomNeg(i));
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
                return new_level;
            } else {
                // We are done with this set of formulae from the previous level.
                // Go to the next.
                self.prev_level_powerset.next();
                // And reset the literals iterator.
                self.literals_powerset = PowersetIter::new(self.num_variables);
                // Then return the next element.
                return self.generate_next_formula_real(new_level);
            }
        } else {
            // `prev_level_powerset` is empty now. So we are done with this level.
	    self.prev_level.clear();
	    self.prev_level.append(&mut self.curr_level_formulae);
            self.curr_level += 1;
            // the `literals_powerset` iterator is still fresh, so no need to update it.
            self.prev_level_powerset = PowersetIter::new(self.prev_level.len()).peekable();
            return self.generate_next_formula_real(true);
        }
    }

    fn generate_next_formula(&mut self) -> bool {
        self.generate_next_formula_real(false)
    }
}

impl Iterator for FineFormIter {
    type Item = NNF;
    fn next(&mut self) -> Option<NNF> {
        if self.full_powerset == None {
            self.full_powerset = Some(BigInt::zero());
            return Some(NNF::Bot);
        }

	let full_powerset = self.full_powerset.as_ref().unwrap();

	if full_powerset.bits() > self.curr_level_formulae.len() as u64 {
	    // generate a new formula and if the level didn't change, output the next formula
	    if !self.generate_next_formula() {
		return self.next();
	    }
	    // if the level did change, reset the powerset
	    self.full_powerset = Some(BigInt::one());
	    return self.next();
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
	return Some(NNF::Or(formula_vec));
    }
}
