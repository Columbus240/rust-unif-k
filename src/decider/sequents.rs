use std::collections::{BTreeMap, BTreeSet};

use crate::nnf::NNF;

use super::clauses::push_if_not_exists;

#[derive(Clone, Debug, Eq, PartialEq, PartialOrd, Ord)]
pub enum LeftRight {
    Left,
    Right,
}

/// Processing Sequent Waiting
#[derive(Debug)]
pub struct PSW {
    // atoms (left or right)
    pub atoms: BTreeMap<usize, LeftRight>,

    // left boxes
    pub lb: Vec<NNF>,
    // right boxes
    pub rb: Vec<NNF>,

    // left disjunctions
    pub ld: Vec<Vec<NNF>>,
    // right conjunctions
    pub rc: Vec<Vec<NNF>>,

    // left waiting
    pub lw: Vec<NNF>,
    // right waiting
    pub rw: Vec<NNF>,
}

/// Processing Sequent
#[derive(Debug)]
pub struct PS {
    // atoms (left or right)
    pub atoms: BTreeMap<usize, LeftRight>,

    // left boxes
    pub lb: Vec<NNF>,
    // right boxes
    pub rb: Vec<NNF>,

    // left disjunctions
    pub ld: Vec<Vec<NNF>>,
    // right conjunctions
    pub rc: Vec<Vec<NNF>>,
}

/// Procesing Sequent Irreducible
#[derive(Debug, Clone, Eq, PartialEq, PartialOrd, Ord)]
pub struct PSI {
    // atoms (left or right)
    pub atoms: BTreeMap<usize, LeftRight>,

    // left boxes
    pub lb: Vec<NNF>,
    // right boxes
    pub rb: Vec<NNF>,
}

impl PSI {
    pub fn new_empty() -> PSI {
        PSI {
            atoms: BTreeMap::new(),
            lb: Vec::new(),
            rb: Vec::new(),
        }
    }

    pub fn is_empty(&self) -> bool {
        self.atoms.is_empty() && self.lb.is_empty() && self.rb.is_empty()
    }

    /// requires that the two sets don't intersect.
    /// Returns `None` if the resulting sequent is trivially valid.
    pub fn substitute_top_bot(
        mut self,
        subst_top: &BTreeSet<usize>,
        subst_bot: &BTreeSet<usize>,
    ) -> Option<PSI> {
        // if the two sets intersect, abort
        if let Some(_) = subst_top.intersection(&subst_bot).next() {
            unreachable!();
        }

        for prop_top in subst_top.iter() {
            match self.atoms.remove(prop_top) {
                None | Some(LeftRight::Left) => {}
                Some(LeftRight::Right) => {
                    // this sequent is trivial
                    return None;
                }
            }
        }

        for prop_bot in subst_bot.iter() {
            match self.atoms.remove(prop_bot) {
                None | Some(LeftRight::Right) => {}
                Some(LeftRight::Left) => {
                    // this sequent is trivial
                    return None;
                }
            }
        }

	// now perform the substitution on the boxed formulae
	for box_left in self.lb.iter_mut() {
	    *box_left = box_left.clone().substitute_top_bot(subst_top, subst_bot).simpl();
	}
	for box_right in self.lb.iter_mut() {
	    *box_right = box_right.clone().substitute_top_bot(subst_top, subst_bot).simpl();
	}
	// and simplify the boxed formulae
	return Some(self)
    }

    // Keep the left and right half of the sequent separate
    fn to_nnf_lr(&self) -> (NNF, NNF) {
        let mut atoms_l = Vec::new();
        let mut atoms_r = Vec::new();
        for (i, lr) in self.atoms.iter() {
            match lr {
                LeftRight::Left => atoms_l.push(i),
                LeftRight::Right => atoms_r.push(i),
            }
        }

        let left = atoms_l
            .iter()
            .map(|x| NNF::AtomPos(**x))
            .chain(self.lb.iter().map(|x| NNF::NnfBox(Box::new(x.clone()))))
            .collect();
        let right = atoms_r
            .iter()
            .map(|x| NNF::AtomPos(**x))
            .chain(self.rb.iter().map(|x| NNF::NnfBox(Box::new(x.clone()))))
            .collect();
        (NNF::And(left), NNF::Or(right))
    }

    pub fn to_nnf(&self) -> NNF {
        let (l, r) = self.to_nnf_lr();
        NNF::impli(l, r).simpl_slow()
    }

    pub fn display_beautiful<'a>(&'a self) -> PSIDisplayBeautiful<'a> {
        PSIDisplayBeautiful { psi: self }
    }
    /*
        pub fn display_latex<'a>(&'a self) -> PSIDisplayLaTeX<'a> {
            PSIDisplayLaTeX { psi: self }
        }

        pub fn display_spartacus<'a>(&'a self) -> PSIDisplaySpartacus<'a> {
            PSIDisplaySpartacus { psi: self }
        }
    */
}

pub struct PSIDisplayBeautiful<'a> {
    psi: &'a PSI,
}

impl<'a> std::fmt::Display for PSIDisplayBeautiful<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let (left, right) = self.psi.to_nnf_lr();
        write!(
            f,
            "{}→{}",
            left.display_beautiful(),
            right.display_beautiful()
        )
    }
}

impl PSW {
    pub fn from_nnf(phi: NNF) -> PSW {
        PSW {
            atoms: BTreeMap::new(),
            lb: Vec::new(),
            rb: Vec::new(),
            ld: Vec::new(),
            rc: Vec::new(),
            lw: Vec::new(),
            rw: vec![phi],
        }
    }

    /// Transforms the given `PSW` into an equivalent but simpler `PS`.
    /// Returns `None` if the input is valid.
    pub fn to_ps(mut self) -> Option<PS> {
        let mut new_left_waiting = Vec::with_capacity(self.lw.len());
        for left_waiting in self.lw.into_iter() {
            match left_waiting {
                NNF::AtomPos(i) => {
                    if let Some(LeftRight::Right) = self.atoms.insert(i, LeftRight::Left) {
                        return None;
                    }
                }
                NNF::AtomNeg(i) => {
                    if let Some(LeftRight::Left) = self.atoms.insert(i, LeftRight::Right) {
                        return None;
                    }
                }
                NNF::Bot => {
                    return None;
                }
                NNF::Top => {
                    // do nothing
                }
                NNF::And(mut conjuncts) => {
                    new_left_waiting.append(&mut conjuncts);
                }
                NNF::Or(disjuncts) => {
                    self.ld.push(disjuncts);
                }
                NNF::NnfBox(phi) => {
		    push_if_not_exists(&mut self.lb, *phi);
                }
                NNF::NnfDia(phi) => {
		    push_if_not_exists(&mut self.rb, phi.neg());
                }
            }
        }

        let mut new_right_waiting = Vec::with_capacity(self.rw.len());
        for right_waiting in self.rw.into_iter() {
            match right_waiting {
                NNF::AtomPos(i) => match self.atoms.insert(i, LeftRight::Right) {
                    Some(LeftRight::Left) => return None,
                    _ => {}
                },
                NNF::AtomNeg(i) => match self.atoms.insert(i, LeftRight::Left) {
                    Some(LeftRight::Right) => return None,
                    _ => {}
                },
                NNF::Bot => {
                    // do nothing
                }
                NNF::Top => {
                    return None;
                }
                NNF::And(conjuncts) => {
                    self.rc.push(conjuncts);
                }
                NNF::Or(mut disjuncts) => {
                    new_right_waiting.append(&mut disjuncts);
                }
                NNF::NnfBox(phi) => {
		    push_if_not_exists(&mut self.rb, *phi);
                }
                NNF::NnfDia(phi) => {
                    push_if_not_exists(&mut self.lb, phi.neg());
                }
            }
        }

        if new_left_waiting.is_empty() && new_right_waiting.is_empty() {
            // Otherwise there is more processing that needs to be done.
            return Some(PS {
                atoms: self.atoms,
                lb: self.lb,
                rb: self.rb,
                ld: self.ld,
                rc: self.rc,
            });
        }
        self.lw = new_left_waiting;
        self.rw = new_right_waiting;
        self.to_ps()
    }
}

enum PSstepResult {
    Waiting(Vec<PSW>),
    Next(PSI),
}

impl PS {
    fn step(mut self) -> PSstepResult {
        if let Some(disjuncts) = self.ld.pop() {
            let mut new_psw = Vec::with_capacity(disjuncts.len());
            for disj in disjuncts.into_iter() {
                new_psw.push(PSW {
                    atoms: self.atoms.clone(),
                    lb: self.lb.clone(),
                    rb: self.rb.clone(),
                    ld: self.ld.clone(),
                    rc: self.rc.clone(),
                    lw: vec![disj],
                    rw: Vec::new(),
                });
            }
            return PSstepResult::Waiting(new_psw);
        }
        if let Some(conjuncts) = self.rc.pop() {
            let mut new_psw = Vec::with_capacity(conjuncts.len());
            for conj in conjuncts.into_iter() {
                new_psw.push(PSW {
                    atoms: self.atoms.clone(),
                    lb: self.lb.clone(),
                    rb: self.rb.clone(),
                    ld: self.ld.clone(),
                    rc: self.rc.clone(),
                    lw: Vec::new(),
                    rw: vec![conj],
                });
            }
            return PSstepResult::Waiting(new_psw);
        }
        return PSstepResult::Next(PSI {
            atoms: self.atoms,
            lb: self.lb,
            rb: self.rb,
        });
    }

    fn to_psi(self) -> Vec<PSI> {
        match self.step() {
            PSstepResult::Waiting(psw_vec) => {
                let mut output = Vec::with_capacity(psw_vec.len());
                for psw in psw_vec {
                    if let Some(ps) = psw.to_ps() {
                        output.append(&mut ps.to_psi());
                    }
                }
                return output;
            }
            PSstepResult::Next(psi) => vec![psi],
        }
    }
}
