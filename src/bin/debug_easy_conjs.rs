extern crate generator;
use generator::decider::LeftRight;
use generator::decider::{PS, PSW};
use generator::NNF;
use std::collections::BTreeMap;
use std::collections::BTreeSet;

fn main() {
    let ps: PS = PS {
        atoms: {
            let mut map = BTreeMap::new();
            map.insert(0, LeftRight::Left);
            map
        },
        lb: BTreeSet::new(),
        rb: BTreeSet::new(),
        ld: Vec::new(),
        rc: vec![vec![NNF::Or(vec![NNF::Or(vec![NNF::AtomPos(0)])])]],
    };
    let mut ps_simpl = ps.clone();
    ps_simpl.process_easy_conjs();
    let ps: PSW = ps.into();
    let ps_simpl: PSW = ps_simpl.into();
    println!("{ps:?}");
    println!("{ps_simpl:?}");
    assert!(NNF::equiv_dec(&ps.to_nnf(), &ps_simpl.to_nnf()));
}
