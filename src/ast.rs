//! JMESPath AST

use std::fmt;

use super::RcVar;

/// Abstract syntax tree of a JMESPath expression.
#[derive(Clone, PartialEq, PartialOrd, Debug)]
pub enum Ast {
    /// Compares two nodes using a comparator, returning true/false.
    Comparison {
        comparator: Comparator,
        lhs: Box<Ast>,
        rhs: Box<Ast>
    },
    /// If `predicate` evaluates to a truthy value, returns the
    /// result `then`
    Condition {
        /// The predicate to test.
        predicate: Box<Ast>,
        /// The node to traverse if the predicate is truthy.
        then: Box<Ast>
    },
    /// Returns the current node.
    Identity,
    /// Used by functions to dynamically evaluate argument values.
    Expref(Box<Ast>),
    /// Evaluates the node, then flattens it one level.
    Flatten(Box<Ast>),
    /// Function name and a vec or function argument expressions.
    Function {
        /// Function name to invoke.
        name: String,
        /// Function arguments.
        args: Vec<Ast>
    },
    /// Extracts a key by name from a map.
    Field(String),
    /// Extracts an index from a Vec.
    Index(i32),
    /// Resolves to a literal value.
    Literal(RcVar),
    /// Evaluates to a list of evaluated expressions.
    MultiList(Vec<Ast>),
    /// Evaluates to a map of key value pairs.
    MultiHash(Vec<KeyValuePair>),
    /// Evaluates to true/false based on if the expression is not truthy.
    Not(Box<Ast>),
    /// Evaluates LHS, and pushes each value through RHS.
    Projection {
        lhs: Box<Ast>,
        rhs: Box<Ast>
    },
    /// Evaluates LHS. If it resolves to an object, returns a Vec of values.
    ObjectValues(Box<Ast>),
    /// Evaluates LHS. If not truthy returns. Otherwise evaluates RHS.
    And {
        lhs: Box<Ast>,
        rhs: Box<Ast>
    },
    /// Evaluates LHS. If truthy returns. Otherwise evaluates RHS.
    Or {
        lhs: Box<Ast>,
        rhs: Box<Ast>
    },
    /// Returns a slice of a vec, using start, stop, and step.
    Slice {
        start: Option<i32>,
        stop: Option<i32>,
        step: i32
    },
    /// Evaluates RHS, then provides that value to the evaluation of RHS.
    Subexpr {
        lhs: Box<Ast>,
        rhs: Box<Ast>
    },
}

/// Represents a key value pair in a multi-hash
#[derive(Clone, PartialEq, PartialOrd, Debug)]
pub struct KeyValuePair {
    /// Key expression used to determine the key. This expression must
    /// resolve to a string variable.
    pub key: Ast,
    /// Value expression used to determine the value.
    pub value: Ast
}

/// Comparators used in Comparison nodes
#[derive(Clone, PartialEq, PartialOrd, Debug)]
pub enum Comparator {
    /// Equivalance (e.g., `==`)
    Eq,
    /// Less than (e.g., `<`)
    Lt,
    /// Less than or equal to (e.g., `<=`)
    Lte,
    /// Not equal (e.g., `!=`)
    Ne,
    /// Greater than (e.g., `>`)
    Gt,
    /// Greater than or equal to (e.g., `>=`)
    Gte,
}

impl fmt::Display for Ast {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(fmt, "{:#?}", self)
    }
}
