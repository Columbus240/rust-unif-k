use std::cmp;
use std::collections::btree_map::BTreeMap;
use std::collections::btree_set::BTreeSet;

use crate::nnf::NNF;

#[derive(Debug, Clone, Eq, Ord, PartialEq, PartialOrd)]
pub enum FineForm {
    Top,
    Node(Box<FFNode>),
}

#[derive(Debug, Clone, Eq, Ord, PartialEq, PartialOrd)]
pub struct FFNode {
    pub atoms: BTreeMap<usize, bool>,
    pub dia_branch: Option<FineForm>,
    pub box_branches: BTreeSet<FineForm>,
}

impl FineForm {
    pub fn bot() -> FineForm {
        FineForm::Node(Box::new(FFNode {
            atoms: BTreeMap::new(),
            dia_branch: None,
            box_branches: BTreeSet::new(),
        }))
    }

    #[allow(dead_code)]
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

    fn len(&self) -> usize {
	if let FineForm::Node(node) = self {
	    node.atoms.len() + 
	    node.dia_branch.as_ref().map_or(0, |x| x.len() + 1) +
		node.box_branches.iter().fold(0, |acc, x| acc + x.len() + 1)
	} else {
	    1
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
            let dia_branch = node
                .dia_branch
                .as_ref()
                .map_or(NNF::Bot, |x| NNF::NnfDia(Box::new(x.to_nnf())));
            let box_branches = node
                .box_branches
                .iter()
                .map(|x| NNF::NnfBox(Box::new(x.to_nnf().neg())));
            let mut output = atoms.collect::<BTreeSet<_>>();
            output.insert(dia_branch);
            output.extend(box_branches);
            return NNF::Or(output);
        }
        NNF::Top
    }

    pub fn or(self, other: FineForm) -> FineForm {
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
    /*
    // Two non-trivial FineForms are equivalent if each of their three
    // parts are equivalent.
    #[allow(unused_variables)]
    fn equiv_dec(&self, other: &FineForm) -> Option<bool> {
        // first compare the atoms.
    if self.atoms != other.atoms {
        return Some(false);
    }

    // is true if we don't know whether the `dia_branch` are equivalent
    let dia_result_unknown : bool;

    if let Some(dia0) = self.dia_branch {
        if let Some(dia1) = other.dia_branch {
        match dia0.equiv_dec(dia1) {
            None => { dia_result_unknown = true },
            Some(false) => return Some(false),
            Some(true) => { dia_result_unknown = false },
        }
        } else {
        match dia0.equiv_dec(FineForm::bot()) {
            None => { dia_result_unknown = true },
            Some(false) => return Some(false),
            Some(true) => { dia_result_unknown = false },
        }
        }
    } else {
        if let Some(dia1) = other.dia_branch {
        match dia1.equiv_dec(FineForm::bot()) {
            None => { dia_result_unknown = true },
            Some(false) => return Some(false),
            Some(true) => { dia_result_unknown = false },
        }
        } else {
        dia_result_unknown = false;
        }
    }
        panic!();
    }
    */
}

#[allow(dead_code)]
pub fn enumerate_powerset<T: Clone>(input: &[T]) -> Vec<Vec<(bool, T)>> {
    if input.is_empty() {
        return vec![vec![]];
    }
    let hd = input[0].clone();

    let e = enumerate_powerset(&input[1..]);

    let mut out = Vec::with_capacity(e.len());

    for v in e {
        let mut v0 = v.clone();
        let mut v1 = v;
        v0.push((true, hd.clone()));
        v1.push((false, hd.clone()));
        out.push(v0);
        out.push(v1);
    }

    return out;
}

pub fn enumerate_triple_powerset<T: Clone>(input: &[T]) -> Vec<Vec<(bool, T)>> {
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
            if let Some((idx, old_ff)) = output
                .iter().enumerate()
                .find(|(_, ff)| NNF::equiv_dec(&ff.to_nnf(), &new_ff.to_nnf()))
            {
		if old_ff.len() > new_ff.len() {
		    // replace the old_ff with the new_ff
		    output[idx] = new_ff;
		}
            } else {
                output.push(new_ff);
            }
        }
    }

    output
}

pub fn enumerate_formulae(i: usize) -> Vec<FineForm> {
    if i == 0 {
        let mut base1 = BTreeMap::new();
        let mut base2 = BTreeMap::new();
        base1.insert(0, true);
        base2.insert(0, false);
        let p = FineForm::Node(Box::new(FFNode {
            atoms: base1,
            dia_branch: None,
            box_branches: BTreeSet::new(),
        }));
        let p_neg = FineForm::Node(Box::new(FFNode {
            atoms: base2,
            dia_branch: None,
            box_branches: BTreeSet::new(),
        }));
        vec![FineForm::Top, FineForm::bot(), p, p_neg]
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

/*
fn enumerate_step_nnf(input: Vec<NNF>) -> Vec<NNF> {
    let mut output = input.clone();

    let base_vectors = vec![vec![], vec![(true, 0)], vec![(false, 0)]];

    let powerset = enumerate_triple_powerset(&input);

    for base in base_vectors {
        for set in powerset.iter() {
            let mut dia_branch: BTreeSet<NNF> = BTreeSet::new();

            let mut disjuncts: BTreeSet<NNF> = BTreeSet::new();

            for (b, f) in set {
		println!("{}, {:?}", b, f);
                if *b {
                    dia_branch.insert(f.clone());
                } else {
                    disjuncts.insert(NNF::NnfBox(Box::new(f.neg())));
                }
            }

            disjuncts.insert(NNF::NnfDia(Box::new(NNF::Or(dia_branch))));

            for (b, i) in &base {
                disjuncts.insert(FineForm::to_nnf_helper(*i, *b));
            }

            output.push(NNF::Or(disjuncts));
        }
    }

    output
}

fn enumerate_formulae_nnf(i: usize) -> Vec<NNF> {
    if i == 0 {
        vec![NNF::Top, NNF::Bot]
    } else {
        enumerate_step_nnf(enumerate_formulae_nnf(i - 1))
    }
}
*/
