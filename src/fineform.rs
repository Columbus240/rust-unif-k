use crate::fineform_iter::PowersetIter;
use crate::nnf::{NnfAtom, NNF};
use std::collections::BTreeSet;
use std::iter::Peekable;

/// A datatype to encode the basic normal forms.
///
/// Invariant: We need to keep explicit track of the number of
/// variables and the degree, and ensure that *never*
/// `FineForm` of different number of variables or of different degree
/// are combined.
/// In symbols:
/// * forall i in `literals`, we have i < `num_variables`
/// * forall F in `prev_level`, we have `degree == F.degree + 1` and `num_variables == F.num_variables`
/// In Coq this can all be done on the level of types (leading to other complications of bookeeping).
/// Here this has to be done "by hand".
#[derive(Clone, PartialOrd, Ord, PartialEq, Eq)]
pub struct BasicFineForm {
    degree: usize,
    num_variables: NnfAtom,

    literals: BTreeSet<NnfAtom>,
    prev_level: BTreeSet<BasicFineForm>,
}

/// Lists the problems `FineForm::new` might have.
#[derive(Debug)]
pub enum BFFError {
    /// There is a number in `literals` that is greater or equal to
    /// `num_variables`.
    TooManyVars,
    /// The forms in `prev_level` don't have all the right degree
    WrongDegree,
    /// There should not be forms in `prev_level` because `degree` is zero.
    DegreeZeroPrevLevel,
    /// There is a form in `prev_level` with the wrong number of variables.
    WrongVariablesPrevLevel,
}

impl BasicFineForm {
    /// Creates a new `FineForm` and checks that the invariants are
    /// correct.
    /// It does not check whether the `FineForm` in `prev_level`
    /// satisfy the invariants.
    ///
    /// # Errors
    /// This function returns an error if the invariants are not
    /// upheld.
    /// TODO: Describe more closely, i.e. refer to or repeat
    /// the documentation of `BFFError`.
    pub fn new(
        degree: usize,
        num_variables: NnfAtom,
        literals: BTreeSet<NnfAtom>,
        prev_level: BTreeSet<BasicFineForm>,
    ) -> Result<BasicFineForm, BFFError> {
        // Verify the invariants.
        if degree == 0 && !prev_level.is_empty() {
            return Err(BFFError::DegreeZeroPrevLevel);
        }

        // With the ordering defined on `Option<_>` this results in the correct comparison.
        // Since `None < Some(_)` and `literals.last()` is none iff
        // `literals.is_empty()`.
        if literals.last() >= Some(&num_variables) {
            return Err(BFFError::TooManyVars);
        }

        for ff in &prev_level {
            if ff.degree + 1 != degree {
                return Err(BFFError::WrongDegree);
            }
            if ff.num_variables != num_variables {
                return Err(BFFError::WrongVariablesPrevLevel);
            }
        }

        Ok(BasicFineForm {
            degree,
            num_variables,
            literals,
            prev_level,
        })
    }

    /// We encode the `FineForm` using the "boxed-translation", because this way we don't need
    /// to compute the complement of `prev_level`.
    pub fn to_nnf(&self) -> NNF {
        let mut conjuncts =
            Vec::with_capacity(self.num_variables as usize + self.prev_level.len() + 1);

        // Prepare the list of literals
        for i in 0..self.num_variables {
            if self.literals.contains(&i) {
                conjuncts.push(NNF::AtomPos(i));
            } else {
                conjuncts.push(NNF::AtomNeg(i));
            }
        }

        // Prepare the list of the next level
        conjuncts.extend(
            self.prev_level
                .iter()
                .map(|ff| NNF::NnfDia(Box::new(ff.to_nnf()))),
        );
        if self.degree > 0 {
            conjuncts.push(NNF::NnfBox(Box::new(NNF::Or(
                self.prev_level.iter().map(BasicFineForm::to_nnf).collect(),
            ))));
        }

        NNF::And(conjuncts)
    }
}

/// Lists all the basic fine forms of a certain level (as `BasicFineForm`).
/// The basic fine forms of the previous level must be given as an
/// argument (as `Vec<BasicFineForm>`), this struct does not keep track of that.
///
/// Invariant: the number of bits of `prev_level_powerset` is always equal to `prev_level.len()`.
/// Invariant: the number of bits of `literals_powerset` is always equal to `num_variables`.
struct BasicLevelFineFormIter {
    degree: usize,
    /// The number of variables to use
    num_variables: NnfAtom,
    literals_powerset: PowersetIter,
    prev_level: Vec<BasicFineForm>,
    prev_level_powerset: Peekable<PowersetIter>,
    curr_level_formulae: Vec<BasicFineForm>,
}

impl BasicLevelFineFormIter {
    fn new(
        degree: usize,
        num_variables: NnfAtom,
        prev_level: Vec<BasicFineForm>,
    ) -> Result<BasicLevelFineFormIter, BFFError> {
        // Allocate some space for `curr_level_formulae` by default, but
        // not too much.
        let prev_level_len = prev_level.len();
        let curr_level_formulae_len =
            (num_variables as usize) * (usize::pow(2, usize::min(prev_level_len, 16) as u32));

        // Go through `prev_level` and check whether it satisfies the necessary assumptions.
        if degree == 0 && !prev_level.is_empty() {
            return Err(BFFError::DegreeZeroPrevLevel);
        }
        for ff in &prev_level {
            if ff.degree + 1 != degree {
                return Err(BFFError::WrongDegree);
            }
            if ff.num_variables != num_variables {
                return Err(BFFError::WrongVariablesPrevLevel);
            }
        }

        Ok(BasicLevelFineFormIter {
            degree,
            num_variables,
            literals_powerset: PowersetIter::new(num_variables as usize),
            prev_level,
            prev_level_powerset: PowersetIter::new(prev_level_len).peekable(),
            curr_level_formulae: Vec::with_capacity(curr_level_formulae_len),
        })
    }
}

impl Iterator for BasicLevelFineFormIter {
    type Item = BasicFineForm;
    fn next(&mut self) -> Option<BasicFineForm> {
        // Only advance `prev_level_powerset` if `literals_powerset` runs out.

        // Peek into `prev_level_powerset` to obtain instructions
        // about the signs for the formulae of the previous level.
        // Early return, if we are done.
        let prev_set = self.prev_level_powerset.peek()?;

        if let Some(literals_set) = self.literals_powerset.next() {
            let mut literals: BTreeSet<NnfAtom> = BTreeSet::new();

            for (i, b) in literals_set.iter().enumerate() {
                if *b {
                    literals.insert(i as NnfAtom);
                }
            }

            let mut prev_level: BTreeSet<BasicFineForm> = BTreeSet::new();
            for (b, bff) in prev_set.iter().zip(self.prev_level.iter()) {
                if *b {
                    prev_level.insert(bff.clone());
                }
            }

            let out: BasicFineForm =
                BasicFineForm::new(self.degree, self.num_variables, literals, prev_level).unwrap();
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

/// Lists all basic Fine forms (as `BasicFineForm`)
pub struct BasicFineFormIter {
    internal_iter: BasicLevelFineFormIter,
}

impl BasicFineFormIter {
    #[must_use]
    // This function can not panic, because
    // `BasicLevelFineFormIter::new` is always called with correct
    // arguments.
    #[allow(clippy::missing_panics_doc)]
    pub fn new(num_variables: NnfAtom) -> BasicFineFormIter {
        BasicFineFormIter {
            internal_iter: BasicLevelFineFormIter::new(0, num_variables, Vec::new()).unwrap(),
        }
    }

    #[must_use]
    pub fn get_curr_level(&self) -> usize {
        self.internal_iter.degree
    }
}

impl Iterator for BasicFineFormIter {
    type Item = BasicFineForm;
    fn next(&mut self) -> Option<BasicFineForm> {
        // Return the next formula from the internal iterator
        if let Some(ff) = self.internal_iter.next() {
            return Some(ff);
        }
        // If there is no such formula, prepare the next level.
        let new_internal_iter = BasicLevelFineFormIter::new(
            self.internal_iter.degree + 1,
            self.internal_iter.num_variables,
            std::mem::take(&mut self.internal_iter.curr_level_formulae),
        )
        .unwrap();
        self.internal_iter = new_internal_iter;
        self.next()
    }
}
