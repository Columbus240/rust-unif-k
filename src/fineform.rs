use crate::nnf::{NnfAtom, NNF};
use std::collections::BTreeSet;

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
struct BasicFineForm {
    degree: usize,
    num_variables: NnfAtom,

    literals: BTreeSet<NnfAtom>,
    prev_level: BTreeSet<BasicFineForm>,
}

/// Lists the problems `FineForm::new` might have.
enum BFFError {
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
    fn new(
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

        for ff in prev_level.iter() {
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
    fn to_nnf(&self) -> NNF {
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
        conjuncts.push(NNF::NnfBox(Box::new(NNF::Or(
            self.prev_level.iter().map(BasicFineForm::to_nnf).collect(),
        ))));

        NNF::And(conjuncts)
    }
}
