//! Generated benchmarks. Benchmarks are generated in build.rs and are
//! sourced from tests/compliance/benchmarks.json

#![feature(test)]

extern crate jmespath;
extern crate test;

use jmespath::{Expression, Variable, parse};
use test::Bencher;

include!(concat!(env!("OUT_DIR"), "/benches.rs"));
