#![feature(once_cell)]
#![feature(btree_drain_filter)]
#![feature(map_first_last)]

#[allow(unused_imports)]
use std::collections::btree_map::BTreeMap;
#[allow(unused_imports)]
use std::collections::btree_set::BTreeSet;

#[allow(unused_imports)]
use rayon::prelude::*;

#[macro_use]
extern crate lalrpop_util;

lalrpop_mod!(#[allow(clippy::all)] pub nnf_parser, "/src/nnf_parser.rs");

mod decider;
mod fineform_correct;
//mod lazy_decider;
//mod lazy_nnf;
mod nnf;
mod powerset;

pub use fineform_correct::FineFormIter;
pub use nnf::{arb_nnf_var, NnfAtom, NNF};
