// Implement the CNF_{\Box_m} algorithm of Peter F. Patel-Schneider and Roberto Sebastiani (2011)
// https://arxiv.org/abs/1106.5261

use super::NNF;
use rand::prelude::*;
use rand_distr::WeightedAliasIndex;
use std::collections::BTreeSet;

// `m` is the number of different boxes.
// `d` is the maximal modal depth
// `n` is the number of different atoms.

// `c` is a list of lists, telling it how many disjunts to put in each
// disjunction at each modal level.
// `p` is a list of lists of lists that controls the
// propositional/modal rate. The top-level elements are for each modal
// depth. The second-level elements are for disjunctions with
// 1,2,3,... disjunctions.
// Notice that the first element of the distributions in `c`
// represents the value `1`, whilst the first element of the
// distributions in `p` represents the value `0`. Setting the last
// element of each distribution to zero eliminates all strictly
// propositional clauses, which are the main cause of trivial
// unsatisfiability.
#[allow(dead_code)]
pub fn rnd_cnf_box_m(
    d: usize,
    m: u8,
    l: usize,
    n: u8,
    p: Vec<Vec<Vec<usize>>>,
    c: Vec<Vec<usize>>,
) -> Result<NNF, rand_distr::WeightedError> {
    // prepare weighted distributions
    let p = {
        let mut new_p = Vec::with_capacity(p.len());
        for pp in p {
            let mut new_pp = Vec::with_capacity(pp.len());

            for weights in pp {
                new_pp.push(WeightedAliasIndex::new(weights)?);
            }

            new_p.push(new_pp);
        }
        new_p
    };
    let c = {
        let mut new_c = Vec::with_capacity(p.len());

        for weights in c {
            new_c.push(WeightedAliasIndex::new(weights)?);
        }

        new_c
    };

    // generate `L` distinct random clauses
    let mut clause_set = BTreeSet::new();
    while clause_set.len() < l {
        clause_set.insert(rnd_clause(d, m, n, &p, &c));
    }
    Ok(NNF::And(clause_set.into_iter().collect()))
}

// Returns `phi` or `phi.neg()` with equal probability.
fn rnd_sign(phi: NNF) -> NNF {
    if rand::random() {
        phi
    } else {
        phi.neg()
    }
}

fn rnd_length(d: usize, c: &[WeightedAliasIndex<usize>]) -> usize {
    // If `C[d]` does not exist, use the last element of `C`
    let default_weights = WeightedAliasIndex::new(vec![1]).unwrap();
    let weights = c
        .get(d)
        .unwrap_or_else(|| c.last().unwrap_or(&default_weights));

    weights.sample(&mut thread_rng()) + 1
}

fn rnd_propnum(d: usize, p: &Vec<Vec<WeightedAliasIndex<usize>>>, k: usize) -> usize {
    if p.is_empty() {
        return 0;
    }
    let default_weights = WeightedAliasIndex::new(vec![1]).unwrap();
    let weights_vec = p.get(d + 1).unwrap_or_else(|| p.last().unwrap());
    let weights = weights_vec
        .get(k)
        .unwrap_or_else(|| weights_vec.last().unwrap_or(&default_weights));
    weights.sample(&mut thread_rng())
}

fn rnd_clause(
    d: usize,
    m: u8,
    n: u8,
    p: &Vec<Vec<WeightedAliasIndex<usize>>>,
    c: &Vec<WeightedAliasIndex<usize>>,
) -> NNF {
    // select randomly the clause length
    let k_num: usize = rnd_length(d, c);
    // select randomly the prop/modal rate
    let p_num: usize = rnd_propnum(d, p, k_num);

    let mut atom_set = BTreeSet::new();

    while atom_set.len() < p_num {
        atom_set.insert(rnd_sign(rnd_atom(0, m, n, p, c)));
    }
    while atom_set.len() < k_num {
        atom_set.insert(rnd_sign(rnd_atom(d, m, n, p, c)));
    }

    NNF::Or(atom_set.into_iter().collect())
}

fn rnd_atom(
    d: usize,
    m: u8,
    n: u8,
    p: &Vec<Vec<WeightedAliasIndex<usize>>>,
    c: &Vec<WeightedAliasIndex<usize>>,
) -> NNF {
    if d == 0 {
        // select randomly a prop. atom
        NNF::AtomPos(thread_rng().gen_range(0..n))
    } else {
        // select randomly an indexed box
        // (because the rest of the program only uses a single box there is no choice to make.)
        NNF::NnfBox(Box::new(rnd_clause(d - 1, m, n, p, c)))
    }
}
