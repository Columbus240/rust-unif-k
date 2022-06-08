use std::cmp;
use std::collections::btree_map::BTreeMap;
use std::collections::btree_set::BTreeSet;
use std::sync::Arc;

use crate::nnf::NNF;

#[derive(Debug, Clone, Eq, Ord, PartialEq, PartialOrd)]
pub enum FineForm {
    Top,
    Node(Box<FFNode>),
}

#[derive(Debug, Clone, Eq, Ord, PartialEq, PartialOrd)]
pub struct FFNode {
    atoms: BTreeMap<usize, bool>,
    dia_branch: Option<FineForm>,
    box_branches: BTreeSet<FineForm>,
}

impl FineForm {
    fn bot() -> FineForm {
        FineForm::Node(Box::new(FFNode {
            atoms: BTreeMap::new(),
            dia_branch: None,
            box_branches: BTreeSet::new(),
        }))
    }

    fn degree(&self) -> usize {
        if let FineForm::Node(node) = self {
            cmp::max(
                node.dia_branch.as_ref().map_or(0, |x| x.degree() + 1),
                node.box_branches
                    .iter()
                    .fold(0, |acc, x| cmp::max(acc, x.degree() + 1)),
            )
        } else {
            0
        }
    }

    fn to_nnf_helper(i: usize, b: bool) -> NNF {
        if b {
            NNF::AtomPos(i)
        } else {
            NNF::AtomNeg(i)
        }
    }

    pub fn to_nnf(&self) -> NNF {
        if let FineForm::Node(node) = self {
            let atoms = node
                .atoms
                .iter()
                .map(|(i, b)| FineForm::to_nnf_helper(*i, *b));
            let mut dia_branch = node
                .dia_branch
                .as_ref()
                .map_or(NNF::Bot, |x| NNF::NnfDia(Arc::new(x.to_nnf())));
            let mut box_branches = node
                .box_branches
                .iter()
                .map(|x| NNF::NnfBox(Arc::new(x.to_nnf())));
            let mut output = atoms.map(|x| Arc::new(x)).collect::<BTreeSet<_>>();
            output.insert(Arc::new(dia_branch));
            output.extend(box_branches.map(|x| Arc::new(x)));
            return NNF::Or(output);
        }
        NNF::Top
    }

    fn or(self, other: FineForm) -> FineForm {
        match (self, other) {
            (FineForm::Top, _) => FineForm::Top,
            (_, FineForm::Top) => FineForm::Top,
            (FineForm::Node(node0), FineForm::Node(node1)) => {
                let mut new_atoms = BTreeMap::new();
                new_atoms.append(&mut node0.atoms.clone());
                new_atoms.append(&mut node1.atoms.clone());

                // compute the diamond branch
                let dia_branch = {
                    if let Some(dia0) = node0.dia_branch {
                        if let Some(dia1) = node1.dia_branch {
                            Some(dia0.or(dia1))
                        } else {
                            Some(dia0)
                        }
                    } else {
                        node1.dia_branch
                    }
                };

                FineForm::Node(Box::new(FFNode {
                    atoms: new_atoms,
                    dia_branch: dia_branch,
                    box_branches: node0
                        .box_branches
                        .union(&node1.box_branches)
                        .cloned()
                        .collect(),
                }))
            }
        }
    }
}

fn enumerate_triple_powerset<T: Clone>(input: &[T]) -> Vec<Vec<(bool, T)>> {
    if input.is_empty() {
        return vec![vec![]];
    }
    let hd = input[0].clone();

    let e = enumerate_triple_powerset(&input[1..]);

    let mut out = Vec::with_capacity(3 * e.len());

    for v in e {
        let mut v0 = v.clone();
        let mut v1 = v.clone();
        out.push(v);
        v0.push((true, hd.clone()));
        v1.push((false, hd.clone()));
        out.push(v0);
        out.push(v1);
    }

    return out;
}

fn enumerate_step_nnf(input: Vec<Arc<NNF>>) -> Vec<Arc<NNF>> {
    let mut output = input.clone();

    let base_vectors = vec![vec![], vec![(true, 0)], vec![(false, 0)]];

    let powerset = enumerate_triple_powerset(&input);

    for base in base_vectors {
        for set in powerset.iter() {
            let mut dia_branch: BTreeSet<Arc<_>> = BTreeSet::new();

            let mut disjuncts: BTreeSet<Arc<_>> = BTreeSet::new();

            for (b, f) in set {
                if *b {
                    dia_branch.insert(f.clone());
                } else {
                    disjuncts.insert(Arc::new(NNF::NnfBox(Arc::new(f.neg()))));
                }
            }

            disjuncts.insert(Arc::new(NNF::NnfDia(Arc::new(NNF::Or(dia_branch)))));

            for (b, i) in &base {
                disjuncts.insert(Arc::new(FineForm::to_nnf_helper(*i, *b)));
            }

            output.push(Arc::new(NNF::Or(disjuncts)));
        }
    }

    output
}

fn enumerate_step(input: Vec<FineForm>) -> Vec<FineForm> {
    let mut output = input.clone();

    let base_vectors = {
        let base0 = BTreeMap::new();
        let mut base1 = BTreeMap::new();
        let mut base2 = BTreeMap::new();
        base1.insert(0, true);
        base2.insert(0, false);
        vec![base0, base1, base2]
    };

    let powerset = enumerate_triple_powerset(&input);

    for base in base_vectors {
        for set in powerset.iter() {
            let mut dia_branch = FineForm::bot();
            let mut box_branches = BTreeSet::new();

            for (b, f) in set {
                if *b {
                    dia_branch = dia_branch.or(f.clone());
                } else {
                    box_branches.insert(f.clone());
                }
            }
            let new_ff = FineForm::Node(Box::new(FFNode {
                atoms: base.clone(),
                dia_branch: Some(dia_branch),
                box_branches,
            }));

            // only add `new_ff` if no such element exists in
            // `output`
            if let Some(_) = output
                .iter()
                .find(|ff| NNF::equiv_dec(&ff.to_nnf(), &new_ff.to_nnf()))
            {
            } else {
                output.push(new_ff);
            }
        }
    }

    output
}

pub fn enumerate_formulae_nnf(i: usize) -> Vec<Arc<NNF>> {
    if i == 0 {
        vec![Arc::new(NNF::Top), Arc::new(NNF::Bot)]
    } else {
        enumerate_step_nnf(enumerate_formulae_nnf(i - 1))
    }
}

pub fn enumerate_formulae(i: usize) -> Vec<FineForm> {
    if i == 0 {
        vec![FineForm::Top, FineForm::bot()]
    } else {
        enumerate_step(enumerate_formulae(i - 1))
    }
}

/*
enum TripleEnumeratorState {
    Empty, Pos, Neg, Done
}

// Base enumerator. Goes three times through an iterator.
struct TripleEnumerator <T, I : Clone + Iterator<Item=T>> {
    orig_iter : I,
    curr_iter : I,
    state : TripleEnumeratorState,
}

impl TripleEnumerator<T, I> {
    fn new(i : I) -> Self {
        TripleEnumerator {
            orig_iter : i,
            curr_iter : i.clone(),
            state : TripleEnumeratorState::Empty,
        }
    }
}

impl Iterator<Item=Vec<(bool,T)>> {
    fn next(&mut self) -> Option<Item> {
        match self.state {
            TripleEnumeratorState::Empty => {

            },
        }
    }
}
*/
