//! JMESPath AST

extern crate rustc_serialize;

use self::rustc_serialize::json::{Json};

pub use self::Ast::*;

/// Represents the abstract syntax tree of a JMESPath expression.
#[derive(Clone, PartialEq, Debug)]
pub enum Ast {
    Comparison(Comparator, Box<Ast>, Box<Ast>),
    Condition(Box<Ast>, Box<Ast>),
    CurrentNode,
    Expref(Box<Ast>),
    Flatten(Box<Ast>),
    Function(String, Vec<Ast>),
    Identifier(String),
    Index(i32),
    Literal(Json),
    MultiList(Vec<Ast>),
    MultiHash(Vec<KeyValuePair>),
    ArrayProjection(Box<Ast>, Box<Ast>),
    ObjectProjection(Box<Ast>, Box<Ast>),
    Or(Box<Ast>, Box<Ast>),
    Slice(Option<i32>, Option<i32>, Option<i32>),
    Subexpr(Box<Ast>, Box<Ast>),
}

/// Represents a key value pair in a multi-hash
#[derive(Clone, PartialEq, Debug)]
pub struct KeyValuePair {
    pub key: Ast,
    pub value: Ast
}

/// Comparators (i.e., less than, greater than, etc.)
#[derive(Clone, PartialEq, Debug)]
pub enum Comparator { Eq, Lt, Lte, Ne, Gte, Gt }
