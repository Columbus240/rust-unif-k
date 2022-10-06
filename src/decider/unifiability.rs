use super::*;
use crate::nnf::NNF;
use std::collections::BTreeSet;

use std::sync::{Arc, Mutex};

use rayon::prelude::*;

//IDEA/TODO: To save memory in `visited_clauses`, we can (because the
// current algorithm always reduces the complexity of the clauses)
// remove clauses in `visited_clauses` if their complexity exceeds the
// complexity of all clauses in the current `clause_set`.
// But this first needs a precise (& working) measure of complexity.

fn clause_waiting_unif_step(mut clause: ClauseWaiting) -> ClauseWaiting {
    clause.process_easy_conjs();
    let mut clause = clause.process_easy_boxes();
    clause.process_conjs_step();
    clause
}

// Invariant: The cut-rule is only ever applied to `ClauseIrred`.

#[derive(Debug)]
struct UnifCheckState {
    clause_set: ClauseSet,
    /// The set of clauses on which the cut rule was applied
    cut_applied: BTreeSet<ClauseIrred>,
    /// The set of clauses which were encountered
    visited_clauses: BTreeSet<ClauseWaiting>,
}

impl UnifCheckState {
    fn new(clause: ClauseWaiting) -> UnifCheckState {
        let mut state = UnifCheckState {
            clause_set: ClauseSet::new(),
            cut_applied: BTreeSet::new(),
            visited_clauses: BTreeSet::new(),
        };
        state.insert_clause_waiting(clause);
        state
    }

    /// For methods that insert clauses:
    /// If the cut-rule has already been applied to the clause, then store it separately.
    /// If the clause has been visited already, then forget it.
    /// Otherwise add it into the respective subset.

    fn insert_clause_irred(&mut self, clause_irred: ClauseIrred) {
        let clause_irred = match clause_irred.unifiability_simplify() {
            Ok(clause_irred) => clause_irred,
            Err(Ok(clause_atoms)) => {
                self.insert_clause_atoms(clause_atoms);
                return;
            }
            Err(Err(clause_waiting)) => {
                self.insert_clause_waiting(clause_waiting);
                return;
            }
        };
        // If cut has been applied to this rule already, then store it separately
        if self.cut_applied.contains(&clause_irred) {
            self.clause_set.cut_clauses.insert(ClauseCut {
                irreducibles: clause_irred.irreducibles,
            });
        } else {
            // if the cut-rule has not been applied to it, check whether we visited it already
            if self.visited_clauses.insert(clause_irred.clone().into()) {
                self.clause_set.irreducibles.insert(clause_irred);
            }
        }
    }

    fn insert_clause_atoms(&mut self, clause: ClauseAtoms) {
        match TryInto::<ClauseIrred>::try_into(clause) {
            Ok(clause_irred) => {
                self.insert_clause_irred(clause_irred);
            }
            Err(clause_atom) => {
                if self.visited_clauses.insert(clause_atom.clone().into()) {
                    self.clause_set.waiting_atoms.push(clause_atom);
                }
            }
        }
    }

    fn insert_clause_waiting(&mut self, clause: ClauseWaiting) {
        match TryInto::<ClauseAtoms>::try_into(clause) {
            Ok(clause_atoms) => {
                self.insert_clause_atoms(clause_atoms);
            }
            Err(clause_waiting) => {
                if self.visited_clauses.insert(clause_waiting.clone()) {
                    self.clause_set.waiting_conj_disj.push(clause_waiting);
                }
            }
        }
    }

    fn insert_clause_waiting_vec(&mut self, clause_vec: Vec<ClauseWaiting>) {
        self.clause_set.waiting_conj_disj.reserve(clause_vec.len());
        for clause in clause_vec {
            self.insert_clause_waiting(clause);
        }
    }
}

/// Returns `true` if the clause is unifiable, returns `false` if it is undecided or not unifiable.
/// All further clauses that are created by this function are stored both in `visited_clauses` and `clause_set`.
fn check_unifiable_process_conjs(
    mut clause: ClauseWaiting,
    state: Arc<Mutex<UnifCheckState>>,
) -> bool {
    loop {
        match TryInto::<ClauseIrred>::try_into(clause) {
            Ok(clause_irred) => {
                if let Some(b) = clause_irred.simple_check_unifiability() {
                    return b;
                }
                let clause_irred = clause_irred.simplify();
                state.lock().unwrap().insert_clause_irred(clause_irred);
                return false;
            }
            Err(mut clause_waiting) => {
                clause_waiting.unifiability_simplify_empty();
                if let Some(b) = clause_waiting.simple_check_unifiability() {
                    return b;
                }
                match TryInto::<ClauseAtoms>::try_into(clause_waiting) {
                    Err(clause_waiting) => {
                        clause = clause_waiting_unif_step(clause_waiting);
                    }
                    Ok(clause_atoms) => {
                        let mut state = state.lock().unwrap();
                        state.insert_clause_atoms(clause_atoms);
                        return false;
                    }
                }
            }
        }
    }
}

fn check_unifiable_process_cut(clause: ClauseIrred, state: Arc<Mutex<UnifCheckState>>) -> bool {
    {
        let mut state = state.lock().unwrap();
        // Check whether we already did a cut on this clause.
        if !state.cut_applied.contains(&clause) {
            // If yes, then skip the cut.
            state.clause_set.cut_clauses.insert(ClauseCut {
                irreducibles: clause.irreducibles,
            });
            return false;
        }
    }
    let mut state = state.lock().unwrap();
    let clause = match clause.unifiability_simplify() {
        Ok(clause) => clause,
        Err(Ok(clause_atoms)) => {
            state.insert_clause_atoms(clause_atoms);
            return false;
        }
        Err(Err(clause_waiting)) => {
            state.insert_clause_waiting(clause_waiting);
            return false;
        }
    };
    match clause.clone().unifiability_simplify_perform_cut_rule() {
        Ok(clause_cut) => {
            state.cut_applied.insert(clause);
            state.clause_set.cut_clauses.insert(clause_cut);
        }
        Err(clause_atoms) => {
            state.cut_applied.insert(clause);
            state.insert_clause_atoms(clause_atoms);
        }
    }
    false
}

fn check_unifiable_process_atoms(clause: ClauseAtoms, state: Arc<Mutex<UnifCheckState>>) -> bool {
    if let Some(b) = clause.simple_check_unifiability() {
        return b;
    }
    match clause.process_atoms_step() {
        ProcessAtomsResult::Valid => true,
        ProcessAtomsResult::Contradictory => false,
        ProcessAtomsResult::Irred(clause_irred) => {
            match clause_irred.unifiability_simplify() {
                Ok(clause_irred) => {
                    state.lock().unwrap().insert_clause_irred(clause_irred);
                }
                Err(Ok(clause_atoms)) => {
                    state.lock().unwrap().insert_clause_atoms(clause_atoms);
                }
                Err(Err(clause_waiting)) => {
                    state.lock().unwrap().insert_clause_waiting(clause_waiting);
                }
            }
            false
        }
        ProcessAtomsResult::Clause(clause_next) => {
            state.lock().unwrap().insert_clause_atoms(clause_next);
            false
        }
        ProcessAtomsResult::Waiting(waiting_clauses) => {
            let mut state = state.lock().unwrap();
            state.insert_clause_waiting_vec(waiting_clauses);
            false
        }
    }
}

impl UnifCheckState {
    fn process(state: UnifCheckState) -> Result<bool, ClauseSet> {
        let state: Arc<Mutex<UnifCheckState>> = Arc::new(Mutex::new(state));

        loop {
            {
                let is_irred = {
                    let mut state = state.lock().unwrap();
                    state.clause_set.unifiability_simplify();
                    state.clause_set.is_irred()
                };
                if is_irred {
                    // Otherwise return
                    let state: UnifCheckState =
                        Arc::try_unwrap(state).unwrap().into_inner().unwrap();
                    //state.clause_set.unifiability_simplify_sat();
                    if let Some(b) = state.clause_set.simple_check_unifiable() {
                        return Ok(b);
                    }

                    return Err(state.clause_set);
                }
            }
            {
                let state_mutex = state.clone();
                let waiting_conj_disj;
                {
                    let mut state = state.lock().unwrap();
                    waiting_conj_disj = std::mem::take(&mut state.clause_set.waiting_conj_disj);
                }

                if waiting_conj_disj
                    .into_par_iter()
                    .any(|clause| check_unifiable_process_conjs(clause, state_mutex.clone()))
                {
                    return Ok(true);
                }
            }
            {
                let state_mutex = state.clone();
                let waiting_atoms;
                {
                    let mut state = state.lock().unwrap();
                    waiting_atoms = std::mem::take(&mut state.clause_set.waiting_atoms);
                }

                if waiting_atoms
                    .into_par_iter()
                    .any(|clause| check_unifiable_process_atoms(clause, state_mutex.clone()))
                {
                    return Ok(true);
                }
            }
            {
                let state_mutex = state.clone();
                let waiting_precut;
                {
                    let mut state = state.lock().unwrap();
                    waiting_precut = std::mem::take(&mut state.clause_set.irreducibles);
                }

                if waiting_precut
                    .into_par_iter()
                    .any(|clause| check_unifiable_process_cut(clause, state_mutex.clone()))
                {
                    return Ok(true);
                }
            }
        }
    }
}

impl ClauseWaiting {
    fn check_unifiable(self) -> Result<bool, ClauseSet> {
        UnifCheckState::process(UnifCheckState::new(self))
    }
}

impl NNF {
    /// Returns `Some(true)` if the formula is unifiable.
    /// Returns `Some(false)` if the formula is not unifiable.
    /// Returns `None` if the algorithm can't decide.
    pub fn check_unifiable(self) -> Result<bool, ClauseSet> {
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
        let clause_waiting = ClauseWaiting::from_sequent(ps);
        clause_waiting.check_unifiable()
    }
}

#[allow(unused_imports)]
use proptest::prelude::*;
use proptest::proptest;

proptest! {
    #![proptest_config(ProptestConfig::with_cases(10000))]
    #[test]
    fn find_box_bot(nnf in crate::nnf::arb_nnf()) {
        let nnf_simpl = nnf.clone().simpl();
        let nnf_unif = nnf.check_unifiable();
        let nnf_simpl_unif = nnf_simpl.check_unifiable();
        match (nnf_unif, nnf_simpl_unif) {
            (Ok(b0), Ok(b1)) => assert_eq!(b0, b1),
            (Err(e), Ok(_)) => panic!("{}", e.display_beautiful()),
            (_, Err(_)) => {},
        }
    }
}
