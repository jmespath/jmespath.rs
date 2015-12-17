//! JMESPath AST
use std::rc::Rc;

use super::variable::Variable;

/// Represents the abstract syntax tree of a JMESPath expression.
#[derive(Clone, PartialEq, PartialOrd, Debug)]
pub enum Ast {
    Comparison(Comparator, Box<Ast>, Box<Ast>),
    Condition(Box<Ast>, Box<Ast>),
    CurrentNode,
    Expref(Box<Ast>),
    Flatten(Box<Ast>),
    Function(String, Vec<Ast>),
    Identifier(String),
    Index(i32),
    Literal(Rc<Variable>),
    MultiList(Vec<Ast>),
    MultiHash(Vec<KeyValuePair>),
    Not(Box<Ast>),
    Projection(Box<Ast>, Box<Ast>),
    ObjectValues(Box<Ast>),
    And(Box<Ast>, Box<Ast>),
    Or(Box<Ast>, Box<Ast>),
    Slice(Option<i32>, Option<i32>, i32),
    Subexpr(Box<Ast>, Box<Ast>),
}

/// Represents a key value pair in a multi-hash
#[derive(Clone, PartialEq, PartialOrd, Debug)]
pub struct KeyValuePair {
    pub key: Ast,
    pub value: Ast
}

/// Comparators (i.e., less than, greater than, etc.)
#[derive(Clone, PartialEq, PartialOrd, Debug)]
pub enum Comparator {
    Eq,
    Lt,
    Lte,
    Ne,
    Gte,
    Gt
}
