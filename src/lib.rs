#![feature(once_cell)]
#![feature(btree_drain_filter)]
#![feature(test)]
#![feature(drain_filter)]
#![warn(clippy::manual_assert)]
#![warn(clippy::missing_panics_doc)]
#![warn(clippy::explicit_iter_loop)]
#![warn(clippy::explicit_into_iter_loop)]

#[allow(unused_imports)]
use std::collections::btree_map::BTreeMap;
#[allow(unused_imports)]
use std::collections::btree_set::BTreeSet;

#[allow(unused_imports)]
use rayon::prelude::*;

extern crate lalrpop_util;

#[allow(clippy::all)]
pub mod nnf_parser;

pub mod decider;
mod fineform;
mod fineform_iter;
//mod lazy_decider;
//mod lazy_nnf;
mod nnf;
mod powerset;

pub use fineform::{BasicFineForm, BasicFineFormIter};
pub use fineform_iter::{BasicFineFormNNFIter, FineFormNNFIter};
pub use nnf::{arb_nnf_var, NnfAtom, NNF};
