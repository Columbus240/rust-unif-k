//! Contains a parser for reading modal formulae from strings.
//!
//! The parser is generated using LALRPOP.

#![allow(clippy::pedantic)]
#![allow(clippy::all)]
include!(concat!(env!("OUT_DIR"), "/nnf_parser.rs"));
