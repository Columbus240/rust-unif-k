//! Given a ground-substitution and a frame, compute the minimal
//! fineform of a certain degree that is made true in this frame by
//! that ground-substitution.
//!
//! This may be correct, but I fear that working with normal forms creates
//! poor performance.

use crate::fineform::BasicFineForm;
use crate::nnf::NnfAtom;
use petgraph::stable_graph::IndexType;
use petgraph::{graph::NodeIndex, Directed, Graph};
use std::collections::BTreeSet;

/// Compute the `BasicFineForm` of a node of a graph. Over zero variables.
///
/// If the `node` does not exist in `graph`, it is treated like a node
/// without successors.
#[allow(clippy::missing_panics_doc)]
#[must_use]
pub fn compute_ground_bff<N, E, Ix: IndexType>(
    degree: usize,
    graph: &Graph<N, E, Directed, Ix>,
    node: NodeIndex<Ix>,
) -> BasicFineForm {
    if degree == 0 {
        return BasicFineForm::new(degree, 0, BTreeSet::new(), BTreeSet::new()).unwrap();
    }
    let prev_level: BTreeSet<_> = graph
        .neighbors(node)
        .map(|other_node| compute_ground_bff(degree - 1, graph, other_node))
        .collect();
    BasicFineForm::new(degree, 0, BTreeSet::new(), prev_level).unwrap()
}

/// Evaluate a ground `BasicFineForm` at a node of a graph.
///
/// If `node` does not exist in `graph` it is treated like a node with
/// no successors.
/// Returns `None` if the `bff` is not ground.
#[allow(clippy::missing_panics_doc)]
#[must_use]
pub fn evaluate_bff<N, E, Ix: IndexType>(
    graph: &Graph<N, E, Directed, Ix>,
    node: NodeIndex<Ix>,
    bff: &BasicFineForm,
) -> Option<bool> {
    if bff.get_num_variables() != 0 {
        return None;
    }

    // If the degree of `bff` is zero, then we must not look at the
    // successors of `node`.
    if bff.get_degree() == 0 {
        return Some(true);
    }

    // For every bff in `bff.prev_level` there must be a successor of
    // `node` at which that bff is true.
    // And for every successor of `node` there must be some bff in
    // `bff.prev_level` which is true at that node.
    // If yes, then return `true`, otherwise return `false`.

    let mut unmatched_bff = bff.get_prev_level().clone();
    'a: for succ in graph.neighbors(node) {
        for bff0 in bff.get_prev_level().iter() {
            if evaluate_bff(graph, succ, bff0).unwrap() {
                unmatched_bff.remove(bff0);
                continue 'a;
            }
        }

        // There has been no bff in `bff.prev_level` which is true at `succ`.
        // So `bff` is not true at `node`.
        return Some(false);
    }

    Some(unmatched_bff.is_empty())
}

/// Evaluate a `GroundFineForm` at a node of a graph.
/// If `node` does not exist in `graph` it is treated like a node with
/// no successors.
#[allow(clippy::missing_panics_doc)]
#[must_use]
pub fn evaluate_gff<N, E, Ix: IndexType>(
    graph: &Graph<N, E, Directed, Ix>,
    node: NodeIndex<Ix>,
    gff: &GroundFineForm,
) -> bool {
    gff.basic_formulas
        .iter()
        .any(|bff| evaluate_bff(graph, node, bff).unwrap())
}

pub struct GroundFineForm {
    basic_formulas: BTreeSet<BasicFineForm>,
}

impl GroundFineForm {
    /// Ensures that all bff in `basic_formulas` have the same degree
    /// and have zero variables.
    #[must_use]
    pub fn new(basic_formulas: BTreeSet<BasicFineForm>) -> Option<GroundFineForm> {
        let mut degree_opt: Option<usize> = None;

        for bff in &basic_formulas {
            if bff.get_num_variables() != 0 {
                return None;
            }
            if let Some(degree) = degree_opt {
                if bff.get_degree() != degree {
                    return None;
                }
            } else {
                degree_opt = Some(bff.get_degree());
            }
        }

        Some(GroundFineForm { basic_formulas })
    }
}

/// Compute the BasicFineForm of a node of a graph, given a ground
/// substitution which defines the valuation on the graph.
/// The number of variables in the output corresponds to the length of `gs`.
///
/// If `node` does not exist in `graph` it is treated like a node
/// without successors.
///
/// # Panics
/// If the length of `gs` is larger than `NnfAtom` can accomodate,
/// this function panics.
#[must_use]
pub fn compute_gs_bff<N, E, Ix: IndexType>(
    degree: usize,
    graph: &Graph<N, E, Directed, Ix>,
    gs: &Vec<GroundFineForm>,
    node: NodeIndex<Ix>,
) -> BasicFineForm {
    if gs.len() > NnfAtom::MAX as usize {
        // The "valuation" on `graph` defined by `gs` has more
        // variables than the type `NnfAtom` can account for.
        //
        // Otherwise the conversions from `usize` to `NnfAtom` would
        // overflow.
        panic!();
    }

    // Compute the `literals`.
    let literals: BTreeSet<NnfAtom> = gs
        .iter()
        .enumerate()
        .filter_map(|(idx, gff)| {
            if evaluate_gff(graph, node, gff) {
                Some(idx as NnfAtom)
            } else {
                None
            }
        })
        .collect();

    // If `degree > 0` then do a recursive call. Otherwise `prev_level` is empty.

    if degree == 0 {
        return BasicFineForm::new(degree, gs.len() as NnfAtom, literals, BTreeSet::new()).unwrap();
    }

    let prev_level: BTreeSet<BasicFineForm> = graph
        .neighbors(node)
        .map(|succ| compute_gs_bff(degree - 1, graph, gs, succ))
        .collect();
    BasicFineForm::new(degree, gs.len() as NnfAtom, literals, prev_level).unwrap()
}

/// # Panics
/// If the length of `gs` is larger than `NnfAtom` can accomodate,
/// this function panics.
#[must_use]
pub fn compute_gs_ff<N, E, Ix: IndexType>(
    degree: usize,
    graph: &Graph<N, E, Directed, Ix>,
    gs: &Vec<GroundFineForm>,
) -> BTreeSet<BasicFineForm> {
    graph
        .node_indices()
        .map(|node| compute_gs_bff(degree, graph, gs, node))
        .collect()
}
