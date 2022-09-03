use super::*;
use crate::nnf::NNF;
use std::collections::BTreeSet;

use std::sync::{Arc, Mutex};

use rayon::prelude::*;

fn clause_waiting_unif_step(mut clause: ClauseWaitingConj) -> ClauseWaitingConj {
    clause.process_easy_conjs();
    let mut clause = clause.process_easy_atoms();
    clause.unifiability_simplify();
    clause.process_conjs_step()
}

fn clause_irred_perform_cut_rule(mut clause: ClauseIrred) -> Result<ClauseIrred, ClauseAtoms> {
    // For all sequents `sequent`, for all variables `p` on the left of this sequent,
    // Search for other sequents with `p` on the right. Then perform
    // cut on these two sequents and this variable. Add the resulting sequent to a waiting list.
    // In the end add the waiting list to the `clause` and return.

    let mut new_irred_sequents: BTreeSet<PSI> = BTreeSet::new();
    let mut new_box_sequents: Vec<PSB> = Vec::new();

    for left_sequent in clause.irreducibles.iter() {
        // iterate over all the left atoms of `sequent`
        for i in left_sequent
            .atoms
            .iter()
            .filter_map(|(i, left_right)| match left_right {
                LeftRight::Left => Some(i),
                LeftRight::Right => None,
            })
        {
            // now find all sequents with `i` on the right
            for right_sequent in clause.irreducibles.iter() {
                if right_sequent.atoms.get(i) != Some(&LeftRight::Right) {
                    continue;
                }
                // create the new sequent as a combination of
                // `left_sequent` and `right_sequent` where `i` is left out.
                // And if an atom appears both left and right, then the new
                // sequent becomes trivial, so skip that.

                // The new sets of atoms
                let mut new_atoms = left_sequent.atoms.clone();
                new_atoms.remove(i);

                for (j, lr) in right_sequent.atoms.iter() {
                    match new_atoms.insert(*j, *lr) {
                        None => {}
                        Some(prev_lr) => {
                            if prev_lr != *lr {
                                // The sequent is trivial
                                continue;
                            }
                        }
                    }
                }

                let mut new_lb = left_sequent.lb.clone();
                new_lb.append(&mut right_sequent.lb.clone());
                let mut new_rb = left_sequent.rb.clone();
                new_rb.append(&mut right_sequent.rb.clone());

                let new_sequent: PSI = PSI {
                    atoms: new_atoms,
                    lb: new_lb,
                    rb: new_rb,
                };

                // Now try transforming the `new_sequent` into a `PSB`.
                // If that doesn't work, check whether it is already present in `clause`

                match new_sequent.try_into() {
                    Ok(new_sequent_psb) => {
                        new_box_sequents.push(new_sequent_psb);
                    }
                    Err(new_sequent) => {
                        if !clause.irreducibles.contains(&new_sequent) {
                            new_irred_sequents.insert(new_sequent);
                        }
                    }
                }
            }
        }
    }

    // Now return a clause, without loosing any information.
    let new_irred_sequents_is_empty = new_irred_sequents.is_empty();
    clause.irreducibles.append(&mut new_irred_sequents);
    if !new_box_sequents.is_empty() {
        return Err(ClauseAtoms {
            irreducibles: clause.irreducibles,
            atom_sequents: new_box_sequents,
        });
    }

    if new_irred_sequents_is_empty {
        Ok(clause)
    } else {
        //TODO: This call is inefficient for two reasons:
        // - Rust does not do tail-call-optimization, so a loop would be better
        // - In the next iteration, we have forgotten, which sequents were already matched together.
        //   This way we do lots of duplicate work.
        clause_irred_perform_cut_rule(clause)
    }
}

/// Returns `true` if the clause is unifiable, returns `false` if it is undecided or not unifiable.
/// All further clauses that are created by this function are stored both in `visited_clauses` and `clause_set`.
fn check_unifiable_process_conjs(
    clause: ClauseWaitingConj,
    visited_clauses: Arc<Mutex<BTreeSet<ClauseAtoms>>>,
    clause_set: Arc<Mutex<ClauseSetWaiting>>,
) -> bool {
    let mut clause = clause;
    loop {
        match TryInto::<ClauseIrred>::try_into(clause) {
            Ok(clause_irred) => match clause_irred.simple_check_unifiability() {
                Some(b) => {
                    return b;
                }
                None => {
                    let clause_irred = clause_irred.simplify();
                    clause_set.lock().unwrap().irreducibles.insert(clause_irred);
                    return false;
                }
            },
            Err(clause_waiting) => {
                if let Some(b) = clause_waiting.simple_check_unifiability() {
                    return b;
                }
                match TryInto::<ClauseAtoms>::try_into(clause_waiting) {
                    Err(clause_waiting) => {
                        clause = clause_waiting_unif_step(clause_waiting);
                    }
                    Ok(clause_atoms) => {
                        if visited_clauses.lock().unwrap().insert(clause_atoms.clone()) {
                            clause_set.lock().unwrap().waiting_atoms.push(clause_atoms);
                        }
                        return false;
                    }
                }
            }
        }
    }
}

fn check_unifiable_process_atoms(
    clause: ClauseAtoms,
    visited_clauses: Arc<Mutex<BTreeSet<ClauseWaitingConj>>>,
    clause_set: Arc<Mutex<ClauseSetWaiting>>,
) -> bool {
    match TryInto::<ClauseIrred>::try_into(clause) {
        Ok(clause_irred) => match clause_irred.simple_check_unifiability() {
            Some(b) => b,
            None => {
                let clause_irred = clause_irred.simplify();
                clause_set.lock().unwrap().irreducibles.insert(clause_irred);
                false
            }
        },
        Err(clause_atoms) => {
            let clause_atoms = clause_atoms.unifiability_simplify();
            if let Some(b) = clause_atoms.simple_check_unifiability() {
                return b;
            }
            let p = clause_atoms.process_atoms_step();
            match p {
                ProcessAtomsResult::Valid => true,
                ProcessAtomsResult::Contradictory => false,
                ProcessAtomsResult::Irred(clause_irred) => {
                    let mut clause_set = clause_set.lock().unwrap();
                    let mut visited_clauses = visited_clauses.lock().unwrap();
                    // Try apply the cut rule to this clause.
                    match clause_irred_perform_cut_rule(clause_irred) {
                        Ok(clause_irred) => {
                            if visited_clauses.insert(clause_irred.clone().into()) {
                                clause_set.irreducibles.insert(clause_irred);
                            }
                        }
                        Err(clause_atoms) => {
                            if visited_clauses.insert(clause_atoms.clone().into()) {
                                clause_set.waiting_atoms.push(clause_atoms);
                            }
                        }
                    }
                    false
                }
                ProcessAtomsResult::Clause(clause_next) => {
                    let clause_next = clause_next.unifiability_simplify();
                    let mut clause_set = clause_set.lock().unwrap();
                    let mut visited_clauses = visited_clauses.lock().unwrap();
                    if visited_clauses.insert(clause_next.clone()) {
                        clause_set.waiting_conj_disj.push(clause_next);
                    }
                    false
                }
                ProcessAtomsResult::Waiting(waiting_clauses) => {
                    let mut clause_set = clause_set.lock().unwrap();
                    let mut visited_clauses = visited_clauses.lock().unwrap();
                    clause_set.waiting_conj_disj.reserve(waiting_clauses.len());
                    for clause in waiting_clauses.into_iter() {
                        if visited_clauses.insert(clause.clone()) {
                            clause_set.waiting_conj_disj.push(clause);
                        }
                    }
                    false
                }
            }
        }
    }
}

impl ClauseSetWaiting {
    pub fn check_unifiable(self) -> Result<bool, ClauseSetWaiting> {
        let mut visited_clauses: BTreeSet<ClauseWaitingConj> = BTreeSet::new();
        let mut visited_atoms: BTreeSet<ClauseAtoms> = BTreeSet::new();
        // Add the current clauses to the set of visited clauses

        for clause in self.irreducibles.iter() {
            visited_clauses.insert(clause.clone().into());
        }
        for clause in self.waiting_atoms.iter() {
            visited_atoms.insert(clause.clone());
        }
        for clause in self.waiting_conj_disj.iter() {
            visited_clauses.insert(clause.clone());
        }
        let visited_clauses: Arc<Mutex<_>> = Arc::new(Mutex::new(visited_clauses));
        let visited_atoms: Arc<Mutex<_>> = Arc::new(Mutex::new(visited_atoms));

        let clause_set = Arc::new(Mutex::new(self));

        loop {
            {
                let is_irred = {
                    let mut clause_set = clause_set.lock().unwrap();
                    clause_set.unifiability_simplify();
                    clause_set.waiting_atoms.is_empty() && clause_set.waiting_conj_disj.is_empty()
                };
                if is_irred {
                    // Otherwise return
                    let clause_set: ClauseSetWaiting =
                        Arc::try_unwrap(clause_set).unwrap().into_inner().unwrap();
                    if let Some(b) = clause_set.is_unifiable() {
                        return Ok(b);
                    }
                    return Err(clause_set);
                }
            }
            {
                let clause_set_mutex = clause_set.clone();
                let waiting_conj_disj;
                {
                    let mut clause_set = clause_set.lock().unwrap();
                    waiting_conj_disj = std::mem::take(&mut clause_set.waiting_conj_disj);
                }

                if waiting_conj_disj.into_par_iter().any(|clause| {
                    check_unifiable_process_conjs(
                        clause,
                        visited_atoms.clone(),
                        clause_set_mutex.clone(),
                    )
                }) {
                    return Ok(true);
                }
            }
            {
                let clause_set_mutex = clause_set.clone();
                let waiting_atoms;
                {
                    let mut clause_set = clause_set.lock().unwrap();
                    waiting_atoms = std::mem::take(&mut clause_set.waiting_atoms);
                }

                if waiting_atoms.into_par_iter().any(|clause| {
                    check_unifiable_process_atoms(
                        clause,
                        visited_clauses.clone(),
                        clause_set_mutex.clone(),
                    )
                }) {
                    return Ok(true);
                }
            }
        }
    }
}

impl NNF {
    /// Returns `Some(true)` if the formula is unifiable.
    /// Returns `Some(false)` if the formula is not unifiable.
    /// Returns `None` if the algorithm can't decide.
    pub fn check_unifiable(self) -> Result<bool, ClauseSetWaiting> {
        // First turn the formula into a sequent.
        let ps = {
            if let Some(ps) = PSW::from_nnf(self).into_ps() {
                ps
            } else {
                // the formula is trivially valid. so in particular unifiable
                return Ok(true);
            }
        };

        // Add the sequent to a clause
        let clause_waiting = ClauseWaitingConj::from_sequent(ps);
        let clause_set: ClauseSetWaiting = ClauseSetWaiting::from_clause(clause_waiting);
        clause_set.check_unifiable()
    }
}

#[allow(unused_imports)]
use proptest::prelude::*;
use proptest::proptest;

proptest! {
    #![proptest_config(ProptestConfig::with_cases(10000))]
    #[test]
    fn find_box_bot(nnf in crate::nnf::arb_nnf()) {
        let nnf_simpl = nnf.clone().simpl_slow();
        let nnf_unif = nnf.check_unifiable();
        let nnf_simpl_unif = nnf_simpl.check_unifiable();
        match (nnf_unif, nnf_simpl_unif) {
            (Ok(b0), Ok(b1)) => assert_eq!(b0, b1),
            (Err(_), _) => {},
            (_, Err(_)) => {},
        }
    }
}
