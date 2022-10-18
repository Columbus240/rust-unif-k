extern crate generator;
use generator::decider::{ClauseIrred, ClauseWaiting, LeftRight, PSI};
use generator::NNF;
use std::collections::{BTreeMap, BTreeSet};

fn main() {
    let psi0: PSI = PSI {
        atoms: {
            let mut map = BTreeMap::new();
            map.insert(0, LeftRight::Left);
            map
        },
        lb: {
            let mut set = BTreeSet::new();
            set.insert(NNF::boxx(NNF::boxx(NNF::AtomPos(0))));
            set
        },
        rb: {
            let mut set = BTreeSet::new();
            set.insert(NNF::boxx(NNF::bot()));
            set
        },
    };
    let psi1: PSI = PSI {
        atoms: {
            let mut map = BTreeMap::new();
            map.insert(0, LeftRight::Right);
            map
        },
        lb: {
            let mut set = BTreeSet::new();
            set.insert(NNF::boxx(NNF::bot()));
            set
        },
        rb: BTreeSet::new(),
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
    println!(
        "{}",
        clause.check_unifiable().unwrap_err().display_beautiful()
    );
}
