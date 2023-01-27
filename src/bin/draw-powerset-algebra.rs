//! Draw the powerset algebra of a given degree of fine forms, and draw
//! in, whether they are unifiable, have finite c.f. for g.d. or are
//! difficult...

use generator::generated_formula::*;
use generator::BasicFineForm;
use generator::BasicFineFormIter;
use generator::NNF;
use num_bigint::*;
use num_traits::identities::{One, Zero};
use petgraph::graph::Graph;
use std::collections::{BTreeMap, BTreeSet};

fn main() {
    let mut graph = Graph::new();
    let node1 = graph.add_node(1);
    let node3 = graph.add_node(3);
    graph.add_edge(node3, node1, ());
    let node7 = graph.add_node(7);
    graph.add_edge(node7, node3, ());
    let node9 = graph.add_node(9);
    graph.add_edge(node9, node1, ());
    graph.add_edge(node9, node3, ());
    let node2 = graph.add_node(2);
    graph.add_edge(node2, node2, ());
    let node5 = graph.add_node(5);
    graph.add_edge(node5, node1, ());
    graph.add_edge(node5, node2, ());
    let node11 = graph.add_node(11);
    graph.add_edge(node11, node2, ());
    graph.add_edge(node11, node3, ());
    let node43 = graph.add_node(43);
    graph.add_edge(node43, node1, ());
    graph.add_edge(node43, node2, ());
    graph.add_edge(node43, node3, ());
    let node17 = graph.add_node(17);
    graph.add_edge(node17, node5, ());
    let node23 = graph.add_node(23);
    graph.add_edge(node23, node1, ());
    graph.add_edge(node23, node5, ());
    let node33 = graph.add_node(33);
    graph.add_edge(node33, node3, ());
    graph.add_edge(node33, node5, ());
    let node53 = graph.add_node(53);
    graph.add_edge(node53, node1, ());
    graph.add_edge(node53, node3, ());
    graph.add_edge(node53, node5, ());
    let node27 = graph.add_node(27);
    graph.add_edge(node27, node2, ());
    graph.add_edge(node27, node5, ());
    let node47 = graph.add_node(47);
    graph.add_edge(node47, node1, ());
    graph.add_edge(node47, node2, ());
    graph.add_edge(node47, node5, ());
    let node65 = graph.add_node(65);
    graph.add_edge(node65, node2, ());
    graph.add_edge(node65, node3, ());
    graph.add_edge(node65, node5, ());
    let node85 = graph.add_node(85);
    graph.add_edge(node85, node1, ());
    graph.add_edge(node85, node2, ());
    graph.add_edge(node85, node3, ());
    graph.add_edge(node85, node5, ());

    // Corresponding to Top
    let gs0: Vec<GroundFineForm> = vec![GroundFineForm::new({
        let mut set = BTreeSet::new();
        set.insert(BasicFineForm::new(0, 0, BTreeSet::new(), BTreeSet::new()).unwrap());
        set
    })
    .unwrap()];

    // Corresponding to BoxBot
    let gs1: Vec<GroundFineForm> = vec![GroundFineForm::new({
        let mut set = BTreeSet::new();
        set.insert(BasicFineForm::new(1, 0, BTreeSet::new(), BTreeSet::new()).unwrap());
        set
    })
    .unwrap()];

    // What formulas correspond to `gs0` and `gs1` in `graph`?
    let gs0_ff = compute_gs_ff(2, &graph, &gs0);
    let gs1_ff = compute_gs_ff(2, &graph, &gs1);

    //let gs0_ff_nnf: BTreeSet<NNF> = gs0_ff.iter().map(BasicFineForm::to_nnf).collect();
    //let gs1_ff_nnf: BTreeSet<NNF> = gs1_ff.iter().map(BasicFineForm::to_nnf).collect();

    println!("gs0:");
    for bff in &gs0_ff {
        println!("{bff}");
    }
    println!();

    println!("gs1:");
    for bff in &gs1_ff {
        println!("{bff}");
    }

    // Enumerate all g.s. of degree 3 over a single variable (which are true at the irrefl singleton).
    // for this first generate all bff of degree 3 over no variables.
    let gbff: Vec<BasicFineForm> = {
        let mut out = Vec::with_capacity(16);

        for bff in BasicFineFormIter::new(0) {
            if bff.get_degree() == 3 {
                out.push(bff);
            } else if bff.get_degree() > 3 {
                break;
            }
        }
        out
    };

    // Bit by bit, construct the powerset of `gbff`.
    let mut curr_set: BigInt = BigInt::zero();
    let mut gbff_set: BTreeSet<BasicFineForm> = BTreeSet::new();
    let mut index: usize = 0;

    // the key shall be the fine form generated by the gff mentioned in the value.
    let mut powset: BTreeMap<BTreeSet<BasicFineForm>, GroundFineForm> = BTreeMap::new();

    loop {
        let gff: GroundFineForm = GroundFineForm::new(gbff_set).unwrap();
        let gs = vec![gff];
        // Only consider sets which evaluate to true at the irrefl. singleton.
        if evaluate_gff(&graph, node1, &gs[0]) {
            // Now compute the formula induced by `gs`.
            let gs_ff = compute_gs_ff(2, &graph, &gs);

            // And add `gs_ff` to the powerset drawing.

            println!("gs_ff {index}");
            for bff in &gs_ff {
                println!("{bff}");
            }
            powset.insert(gs_ff, gs[0].clone());
            /* too inefficient
                println!(
                    "unifiability: {:?}",
                    NNF::Or(gs_ff.iter().map(BasicFineForm::to_nnf).collect())
                        .simpl()
                        .check_unifiable()
                );
            */
        }

        gbff_set = gs.into_iter().next().unwrap().into();
        index += 1;

        // determine which gbff to add/remove from `gbff_set`.
        let next_set: BigInt = curr_set.clone() + 1;

        if next_set.bits() > gbff.len() as u64 {
            break;
        }

        let new_indices = curr_set.clone() & (!next_set.clone());
        let removed_indices = next_set.clone() & (!curr_set.clone());
        curr_set = next_set;

        for (b, bff) in generator::fineform_iter::bigint_to_bitvec(new_indices, gbff.len())
            .iter()
            .zip(gbff.iter())
        {
            if *b {
                gbff_set.insert(bff.clone());
            }
        }
        for (b, bff) in generator::fineform_iter::bigint_to_bitvec(removed_indices, gbff.len())
            .iter()
            .zip(gbff.iter())
        {
            if *b {
                gbff_set.remove(bff);
            }
        }
    }

    println!("powset len: {}", powset.len());
}

/*
fn main() {
    let mut graph = Graph::new();
    let node_a = graph.add_node('a');
    let node_b = graph.add_node('b');
    let node_c = graph.add_node('c');
    let node_d = graph.add_node('d');
    graph.add_edge(node_b, node_b, ());
    graph.add_edge(node_b, node_a, ());
    graph.add_edge(node_d, node_a, ());
    graph.add_edge(node_c, node_c, ());

    // Corresponding to Top
    let gs0: Vec<GroundFineForm> = vec![GroundFineForm::new({
        let mut set = BTreeSet::new();
        set.insert(BasicFineForm::new(0, 0, BTreeSet::new(), BTreeSet::new()).unwrap());
        set
    })
    .unwrap()];

    // Corresponding to BoxBot
    let gs1: Vec<GroundFineForm> = vec![GroundFineForm::new({
        let mut set = BTreeSet::new();
        set.insert(BasicFineForm::new(1, 0, BTreeSet::new(), BTreeSet::new()).unwrap());
        set
    })
    .unwrap()];

    // Corresponding to Box

    // What formulas correspond to `gs0` and `gs1` in `graph`?
    let gs0_ff = compute_gs_ff(1, &graph, &gs0);
    let gs1_ff = compute_gs_ff(1, &graph, &gs1);

    let gs0_ff_nnf: BTreeSet<NNF> = gs0_ff.iter().map(BasicFineForm::to_nnf).collect();
    let gs1_ff_nnf: BTreeSet<NNF> = gs1_ff.iter().map(BasicFineForm::to_nnf).collect();

    println!("gs0:");
    for nnf in &gs0_ff_nnf {
        println!("{}", nnf.display_beautiful());
    }
    println!();

    println!("gs1:");
    for nnf in &gs1_ff_nnf {
        println!("{}", nnf.display_beautiful());
    }

    // Note that for every other gs whose formula is true at 'a', its
    // gs_ff will be a superset of the gs_ff of gs0.
    // And since the gs_ff of gs0 is unifiable, those will be unifiable as well.
}
*/
