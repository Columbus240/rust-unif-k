#![allow(non_snake_case)]

extern crate generator;
use generator::decider::{ClauseIrred, ClauseWaiting, LeftRight, PSI};
use generator::NNF;
use std::collections::{BTreeMap, BTreeSet};

use proptest::strategy::{Strategy, ValueTree};
use proptest::test_runner::TestRunner;

fn create_stuck_candidate(
    Γ0: BTreeSet<NNF>,
    Δ0: BTreeSet<NNF>,
    Γ1: BTreeSet<NNF>,
    Δ1: BTreeSet<NNF>,
) -> ClauseWaiting {
    let psi0 = PSI {
        atoms: {
            let mut map = BTreeMap::new();
            map.insert(0, LeftRight::Left);
            map
        },
        lb: Γ0,
        rb: Δ0,
    };
    let psi1 = PSI {
        atoms: {
            let mut map = BTreeMap::new();
            map.insert(0, LeftRight::Right);
            map
        },
        lb: Γ1,
        rb: Δ1,
    };
    let clause: ClauseWaiting = ClauseIrred {
        irreducibles: {
            let mut set = BTreeSet::new();
            set.insert(psi0);
            set.insert(psi1);
            set
        },
    }
    .into();
    clause
}

fn main() {
    let mut runner = TestRunner::default();

    let clause_out;
    loop {
        let mut Γ0 = BTreeSet::new();
        Γ0.insert(
            generator::arb_nnf_var(1)
                .new_tree(&mut runner)
                .unwrap()
                .current()
                .simpl(),
        );
        let mut Δ0 = BTreeSet::new();
        Δ0.insert(
            generator::arb_nnf_var(1)
                .new_tree(&mut runner)
                .unwrap()
                .current()
                .simpl(),
        );
        let mut Γ1 = BTreeSet::new();
        Γ1.insert(
            generator::arb_nnf_var(1)
                .new_tree(&mut runner)
                .unwrap()
                .current()
                .simpl(),
        );
        let mut Δ1 = BTreeSet::new();
        Δ1.insert(
            generator::arb_nnf_var(1)
                .new_tree(&mut runner)
                .unwrap()
                .current()
                .simpl(),
        );
        let clause: ClauseWaiting = create_stuck_candidate(Γ0, Δ0, Γ1, Δ1);
        match clause.check_unifiable() {
            Ok(_) => continue,
            Err(e) => {
                clause_out = e;
                break;
            }
        }
    }
    println!("{}", clause_out.display_beautiful());
}
