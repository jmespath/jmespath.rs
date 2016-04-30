//! JMESPath AST

use std::fmt;

use super::RcVar;
use super::Coordinates;
use lexer::Token;

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
        let offset = match *self {
            Ast::Comparison { offset, .. } => offset,
            Ast::Condition { offset, .. } => offset,
            Ast::Identity { offset, .. } => offset,
            Ast::Expref { offset, .. } => offset,
            Ast::Flatten { offset, .. } => offset,
            Ast::Function { offset, .. } => offset,
            Ast::Field { offset, .. } => offset,
            Ast::Index { offset, .. } => offset,
            Ast::Literal { offset, .. } => offset,
            Ast::MultiList { offset, .. } => offset,
            Ast::MultiHash { offset, .. } => offset,
            Ast::Not { offset, .. } => offset,
            Ast::Projection { offset, .. } => offset,
            Ast::ObjectValues { offset, .. } => offset,
            Ast::And { offset, .. } => offset,
            Ast::Or { offset, .. } => offset,
            Ast::Slice { offset, .. } => offset,
            Ast::Subexpr { offset, .. } => offset,
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
    /// Key name.
    pub key: String,
    /// Value expression used to determine the value.
    pub value: Ast
}

/// Comparators used in Comparison nodes
#[derive(Clone, PartialEq, PartialOrd, Debug)]
pub enum Comparator {
    Eq(EqComparator),
    Ord(OrdComparator),
}

/// Creates a Comparator from a Token.
/// Panics if the Token is invalid.
impl From<Token> for Comparator {
    fn from(token: Token) -> Self {
        match token {
            Token::Lt => Comparator::Ord(OrdComparator::LessThan),
            Token::Lte => Comparator::Ord(OrdComparator::LessThanEqual),
            Token::Gt => Comparator::Ord(OrdComparator::GreaterThan),
            Token::Gte => Comparator::Ord(OrdComparator::GreaterThanEqual),
            Token::Eq => Comparator::Eq(EqComparator::Equal),
            Token::Ne => Comparator::Eq(EqComparator::NotEqual),
            _ => panic!("Invalid token for comparator: {:?}", token)
        }
    }
}

#[derive(Clone, PartialEq, PartialOrd, Debug)]
pub enum EqComparator {
    Equal,
    NotEqual,
}

#[derive(Clone, PartialEq, PartialOrd, Debug)]
pub enum OrdComparator {
    LessThan,
    LessThanEqual,
    GreaterThan,
    GreaterThanEqual,
}

#[cfg(test)]
mod test {
    use super::*;

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
}
