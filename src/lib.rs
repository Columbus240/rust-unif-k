#![feature(once_cell)]
#![feature(btree_drain_filter)]
#![feature(test)]
#![feature(drain_filter)]
#![warn(clippy::manual_assert)]
#![warn(clippy::missing_panics_doc)]
#![warn(clippy::explicit_iter_loop)]
#![warn(clippy::explicit_into_iter_loop)]
#![warn(clippy::if_not_else)]
#![warn(clippy::missing_errors_doc)]
#![warn(clippy::needless_pass_by_value)]
#![warn(clippy::must_use_candidate)]
#![warn(clippy::semicolon_if_nothing_returned)]

#[allow(unused_imports)]
use std::collections::btree_map::BTreeMap;
#[allow(unused_imports)]
use std::collections::btree_set::BTreeSet;

#[allow(unused_imports)]
use rayon::prelude::*;

extern crate lalrpop_util;

pub mod nnf_parser;

pub mod decider;
mod fineform;
pub mod fineform_iter;
pub mod generated_formula;
//mod lazy_decider;
//mod lazy_nnf;
mod nnf;
mod powerset;

pub use fineform::{BasicFineForm, BasicFineFormIter};
pub use fineform_iter::{BasicFineFormNNFIter, FineFormNNFIter, PowersetIter};
pub use nnf::{arb_nnf_var, NnfAtom, NNF};
