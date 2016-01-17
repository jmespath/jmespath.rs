//! JMESPath AST

use std::fmt;

use super::lexer::Token;
use super::RcVar;
use super::Coordinates;

/// Abstract syntax tree of a JMESPath expression.
#[derive(Clone, PartialEq, PartialOrd, Debug)]
pub enum Ast {
    /// Compares two nodes using a comparator, returning true/false.
    Comparison {
        /// Approximate absolute position in the parsed expression.
        offset: usize,
        /// Comparator that compares the two results
        comparator: Comparator,
        /// Left hand side of the comparison
        lhs: Box<Ast>,
        /// Right hand side of the comparison
        rhs: Box<Ast>,
    },
    /// If `predicate` evaluates to a truthy value, returns the
    /// result `then`
    Condition {
        /// Approximate absolute position in the parsed expression.
        offset: usize,
        /// The predicate to test.
        predicate: Box<Ast>,
        /// The node to traverse if the predicate is truthy.
        then: Box<Ast>,
    },
    /// Returns the current node.
    Identity {
        /// Approximate absolute position in the parsed expression.
        offset: usize,
    },
    /// Used by functions to dynamically evaluate argument values.
    Expref {
        /// Approximate absolute position in the parsed expression.
        offset: usize,
        /// Node to execute
        ast: Box<Ast>,
    },
    /// Evaluates the node, then flattens it one level.
    Flatten {
        /// Approximate absolute position in the parsed expression.
        offset: usize,
        /// Node to execute and flatten
        node: Box<Ast>,
    },
    /// Function name and a vec or function argument expressions.
    Function {
        /// Approximate absolute position in the parsed expression.
        offset: usize,
        /// Function name to invoke.
        name: String,
        /// Function arguments.
        args: Vec<Ast>,
    },
    /// Extracts a key by name from a map.
    Field {
        /// Approximate absolute position in the parsed expression.
        offset: usize,
        /// Field name to extract.
        name: String,
    },
    /// Extracts an index from a Vec.
    Index {
        /// Approximate absolute position in the parsed expression.
        offset: usize,
        /// Index to extract
        idx: i32,
    },
    /// Resolves to a literal value.
    Literal {
        /// Approximate absolute position in the parsed expression.
        offset: usize,
        /// Literal value
        value: RcVar,
    },
    /// Evaluates to a list of evaluated expressions.
    MultiList {
        /// Approximate absolute position in the parsed expression.
        offset: usize,
        /// Elements of the list
        elements: Vec<Ast>,
    },
    /// Evaluates to a map of key value pairs.
    MultiHash {
        /// Approximate absolute position in the parsed expression.
        offset: usize,
        /// Elements of the hash
        elements: Vec<KeyValuePair>,
    },
    /// Evaluates to true/false based on if the expression is not truthy.
    Not {
        /// Approximate absolute position in the parsed expression.
        offset: usize,
        /// node to negate
        node: Box<Ast>,
    },
    /// Evaluates LHS, and pushes each value through RHS.
    Projection {
        /// Approximate absolute position in the parsed expression.
        offset: usize,
        /// Left hand side of the projection.
        lhs: Box<Ast>,
        /// Right hand side of the projection.
        rhs: Box<Ast>,
    },
    /// Evaluates LHS. If it resolves to an object, returns a Vec of values.
    ObjectValues {
        /// Approximate absolute position in the parsed expression.
        offset: usize,
        /// Node to extract object values from.
        node: Box<Ast>,
    },
    /// Evaluates LHS. If not truthy returns. Otherwise evaluates RHS.
    And {
        /// Approximate absolute position in the parsed expression.
        offset: usize,
        /// Left hand side of the expression.
        lhs: Box<Ast>,
        /// Right hand side of the expression.
        rhs: Box<Ast>,
    },
    /// Evaluates LHS. If truthy returns. Otherwise evaluates RHS.
    Or {
        /// Approximate absolute position in the parsed expression.
        offset: usize,
        /// Left hand side of the expression.
        lhs: Box<Ast>,
        /// Right hand side of the expression.
        rhs: Box<Ast>,
    },
    /// Returns a slice of a vec, using start, stop, and step.
    Slice {
        /// Approximate absolute position in the parsed expression.
        offset: usize,
        /// Starting index
        start: Option<i32>,
        /// Stopping index
        stop: Option<i32>,
        /// Step amount between extractions.
        step: i32,
    },
    /// Evaluates RHS, then provides that value to the evaluation of RHS.
    Subexpr {
        /// Approximate absolute position in the parsed expression.
        offset: usize,
        /// Left hand side of the expression.
        lhs: Box<Ast>,
        /// Right hand side of the expression.
        rhs: Box<Ast>,
    },
}

impl Ast {
    /// Create a coordinates struct for the AST node.
    pub fn make_coordinates(&self, expr: &str) -> Coordinates {
        let offset = match self {
            &Ast::Comparison { offset, .. } => offset,
            &Ast::Condition { offset, .. } => offset,
            &Ast::Identity { offset, .. } => offset,
            &Ast::Expref { offset, .. } => offset,
            &Ast::Flatten { offset, .. } => offset,
            &Ast::Function { offset, .. } => offset,
            &Ast::Field { offset, .. } => offset,
            &Ast::Index { offset, .. } => offset,
            &Ast::Literal { offset, .. } => offset,
            &Ast::MultiList { offset, .. } => offset,
            &Ast::MultiHash { offset, .. } => offset,
            &Ast::Not { offset, .. } => offset,
            &Ast::Projection { offset, .. } => offset,
            &Ast::ObjectValues { offset, .. } => offset,
            &Ast::And { offset, .. } => offset,
            &Ast::Or { offset, .. } => offset,
            &Ast::Slice { offset, .. } => offset,
            &Ast::Subexpr { offset, .. } => offset,
        };
        Coordinates::from_offset(expr, offset)
    }
}

impl fmt::Display for Ast {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(fmt, "{:#?}", self)
    }
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

impl Comparator {
    /// Get the binding power of the operator.
    pub fn lbp(&self) -> usize {
        match self {
            &Comparator::Eq => Token::Eq.lbp(),
            &Comparator::Ne => Token::Ne.lbp(),
            &Comparator::Lt => Token::Lt.lbp(),
            &Comparator::Lte => Token::Lte.lbp(),
            &Comparator::Gt => Token::Gt.lbp(),
            &Comparator::Gte => Token::Gte.lbp(),
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use lexer::Token;

    #[test]
    fn makes_coordinates_from_ast_node() {
        let expr = "foo.abc";
        let node = Ast::Field { name: "abc".to_string(), offset: 4 };
        let coords = node.make_coordinates(expr);
        assert_eq!(0, coords.line);
        assert_eq!(4, coords.column);
        assert_eq!(4, coords.offset);
    }

    #[test]
    fn displays_pretty_printed_ast_node() {
        let node = Ast::Field { name: "abc".to_string(), offset: 4 };
        assert_eq!("Field {\n    offset: 4,\n    name: \"abc\"\n}", format!("{}", node));
    }

    #[test]
    fn gets_comparator_lbp() {
        assert_eq!(Token::Eq.lbp(), Comparator::Eq.lbp());
        assert_eq!(Token::Ne.lbp(), Comparator::Ne.lbp());
        assert_eq!(Token::Gt.lbp(), Comparator::Gt.lbp());
        assert_eq!(Token::Gte.lbp(), Comparator::Gte.lbp());
        assert_eq!(Token::Lt.lbp(), Comparator::Lt.lbp());
        assert_eq!(Token::Lte.lbp(), Comparator::Lte.lbp());
    }
}
