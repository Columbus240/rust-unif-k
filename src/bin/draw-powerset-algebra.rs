//! Draw the powerset algebra of a given degree of fine forms, and draw
//! in, whether they are unifiable, have finite c.f. for g.d. or are
//! difficult...

use generator::generated_formula::*;
use generator::BasicFineForm;
use generator::NNF;
use petgraph::graph::Graph;
use std::collections::BTreeSet;

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
