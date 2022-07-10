use bit_vec::BitVec;
use core::ops::{Rem, Shr};
use num_bigint::*;
use num_traits::identities::{One, Zero};

use crate::nnf::*;

pub struct PowersetIter {
    num_variables: usize,
    state: Option<BigInt>,
}

impl PowersetIter {
    pub fn new(num_variables: usize) -> PowersetIter {
        PowersetIter {
            num_variables,
            state: Some(BigInt::zero()),
        }
    }
}

impl Iterator for PowersetIter {
    type Item = BitVec<u32>;
    fn next(&mut self) -> Option<BitVec<u32>> {
        if let Some(state) = &mut self.state {
            // If `state` has more bits than there are
            // `self.num_variables` then abort and end the iteration.
            if state.bits() > self.num_variables.try_into().unwrap() {
                self.state = None;
                return None;
            }

            // Convert the number `state` to a `BitVec` of length `self.num_variables`
            // Then increment `state` by one
            // Then return the `BitVec` we created.
            let mut temp_state: BigInt = state.clone();
            let mut bitvec = BitVec::with_capacity(self.num_variables);

            for i in 0..self.num_variables {
                // Push the last bit of `temp_state` to `bitvec`
                bitvec.push((temp_state.clone() % 2) == BigInt::one());
                // Then shift `temp_state` to the right by one step.
                temp_state = temp_state.shr(1);
            }

            *state += 1;
            Some(bitvec)
        } else {
            None
        }
    }
}

pub struct FineFormIter {
    level: usize,
    num_variables: usize,
    zero_iter: PowersetIter,
    next_level: Option<FineFormIter>,
}

impl FineFormIter {
    fn new(num_variables: usize, level: usize) -> FineFormIter {
        if level == 0 {
            FineFormIter {
                level,
                num_variables,
                zero_iter: PowersetIter::new(num_variables),
                next_level: None,
            }
        } else {
            FineFormIter {
                level,
                num_variables,
                zero_iter: PowersetIter::new(num_variables),
                next_level: Some(FineFormIter::new(num_variables, level - 1)),
            }
        }
    }
}

impl Iterator for FineFormIter {
    type Item = NNF;

    fn next(&mut self) -> Option<NNF> {
    }
}
