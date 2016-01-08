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

/// Pushes the left padding necessary for the current depth.
fn left_padding(buffer: &mut String, depth: usize) {
    if depth > 0 {
        buffer.push_str(&(0..depth).map(|_| ' ').collect::<String>());
    }
}

impl Ast {
    /// Internal implementation for pretty printing the AST.
    fn pretty_print(&self, depth: usize) -> String {
        let mut buffer = String::new();
        left_padding(&mut buffer, depth);
        match self {
            &Ast::Comparison { ref comparator, ref lhs, ref rhs } => {
                buffer.push_str(&format!("(Comparison {:?}\n{}\n{})",
                    comparator,
                    lhs.pretty_print(depth + 4),
                    rhs.pretty_print(depth + 4)))
            },
            &Ast::Condition { ref predicate, ref then } => {
                buffer.push_str(&format!("(Condition if\n{} then\n{})",
                    predicate.pretty_print(depth + 4),
                    then.pretty_print(depth + 4)))
            },
            &Ast::Identity => buffer.push_str(&format!("(Identity)")),
            &Ast::Expref(ref n) => {
                buffer.push_str(&format!("(Expref\n{})", n.pretty_print(depth + 4)))
            },
            &Ast::Flatten(ref n) => {
                buffer.push_str(&format!("(Flatten\n{})", n.pretty_print(depth + 4)))
            },
            &Ast::Function { ref name, ref args } => {
                buffer.push_str(&format!("(Function {}", name));
                for arg in args {
                    buffer.push_str(&format!("\n{}", arg.pretty_print(depth + 4)));
                }
                buffer.push_str(")");
            },
            &Ast::Field(ref name) => buffer.push_str(&format!("(Field {})", name)),
            &Ast::Index(ref idx) => buffer.push_str(&format!("(Index {})", idx)),
            &Ast::Literal(ref value) => {
                buffer.push_str("(Literal\n");
                left_padding(&mut buffer, depth + 4);
                let mut depth_str = String::new();
                left_padding(&mut depth_str, depth + 4);
                buffer.push_str(&format!("{:?})", value).replace("\n", &depth_str));
            },
            &Ast::MultiList(ref elements) => {
                buffer.push_str("(MultiList");
                for element in elements {
                    buffer.push_str(&format!("\n{}", element.pretty_print(depth + 4)));
                }
                buffer.push_str(")");
            },
            &Ast::MultiHash(ref pairs) => {
                buffer.push_str("(MultiHash");
                for kvp in pairs {
                    buffer.push_str("\n");
                    left_padding(&mut buffer, depth + 4);
                    buffer.push_str(&format!("{{\n{}\n", kvp.key.pretty_print(depth + 8)));
                    buffer.push_str(&format!("{}\n", kvp.value.pretty_print(depth + 8)));
                    left_padding(&mut buffer, depth + 4);
                    buffer.push_str("}");
                }
                buffer.push_str(")");
            },
            &Ast::Not(ref n) => {
                buffer.push_str(&format!("(Not\n{})", n.pretty_print(depth + 4)))
            },
            &Ast::Projection { ref lhs, ref rhs } => {
                buffer.push_str(&format!("(Projection\n{}\n{})",
                    lhs.pretty_print(depth + 4),
                    rhs.pretty_print(depth + 4)))
            },
            &Ast::ObjectValues(ref node) => {
                buffer.push_str(&format!("(ObjectValues\n{})",
                    node.pretty_print(depth + 4)))
            },
            &Ast::And { ref lhs, ref rhs } => {
                buffer.push_str(&format!("(And\n{}\n{})",
                    lhs.pretty_print(depth + 4),
                    rhs.pretty_print(depth + 4)))
            },
            &Ast::Or { ref lhs, ref rhs } => {
                buffer.push_str(&format!("(Or\n{}\n{})",
                    lhs.pretty_print(depth + 4),
                    rhs.pretty_print(depth + 4)))
            },
            &Ast::Slice { ref start, ref stop, ref step } => {
                buffer.push_str(&format!("(Slice {:?} {:?} {})", start, stop, step))
            },
            &Ast::Subexpr { ref lhs, ref rhs } => {
                buffer.push_str(&format!("(Subexpr\n{}\n{})",
                    lhs.pretty_print(depth + 4),
                    rhs.pretty_print(depth + 4)))
            },
        }
        buffer
    }
}

/// Display/to_string() will pretty-print the AST
impl fmt::Display for Ast {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(fmt, "{}", self.pretty_print(0))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::rc::Rc;
    use super::super::Variable;

    #[test]
    fn field_to_string() {
        assert_eq!("(Field foo)", Ast::Field("foo".to_string()).to_string());
    }

    #[test]
    fn index_to_string() {
        assert_eq!("(Index 2)", Ast::Index(2).to_string());
        assert_eq!("(Index -2)", Ast::Index(-2).to_string());
    }

    #[test]
    fn comparison_to_string() {
        assert_eq!(
            "(Comparison Eq\n    (Identity)\n    (Field a))",
            Ast::Comparison {
                comparator: Comparator::Eq,
                lhs: Box::new(Ast::Identity),
                rhs: Box::new(Ast::Field("a".to_string()))
            }.to_string()
        );
    }

    #[test]
    fn predicate_to_string() {
        assert_eq!(
            "(Condition if\n    (Identity) then\n    (Field a))",
            Ast::Condition {
                predicate: Box::new(Ast::Identity),
                then: Box::new(Ast::Field("a".to_string()))
            }.to_string()
        );
    }

    #[test]
    fn identity_to_string() {
        assert_eq!("(Identity)", Ast::Identity.to_string());
    }

    #[test]
    fn expref_to_string() {
        assert_eq!(
            "(Expref\n    (Field a))",
            Ast::Expref(Box::new(Ast::Field("a".to_string()))).to_string());
    }

    #[test]
    fn flatten_to_string() {
        assert_eq!(
            "(Flatten\n    (Field a))",
            Ast::Flatten(Box::new(Ast::Field("a".to_string()))).to_string());
    }

    #[test]
    fn function_to_string() {
        assert_eq!(
            "(Function foo\n    (Field a)\n    (Expref\n        (Field b)))",
            Ast::Function {
                name: "foo".to_string(),
                args: vec![
                    Ast::Field("a".to_string()),
                    Ast::Expref(Box::new(Ast::Field("b".to_string())))]
            }.to_string()
        );
    }

    #[test]
    fn literal_to_string() {
        assert_eq!(
            "(Literal\n    String(\"a\"))",
            Ast::Literal(Rc::new(Variable::String("a".to_string()))).to_string());
    }

    #[test]
    fn multi_list_to_string() {
        assert_eq!(
            "(MultiList\n    (Field a)\n    (Identity))",
            Ast::MultiList(vec![
                Ast::Field("a".to_string()),
                Ast::Identity]).to_string());
    }

    #[test]
    fn multi_hash_to_string() {
        assert_eq!(
            "(MultiHash\n    \
                {\n        \
                    (Literal\n            \
                        String(\"a_key\"))\n        \
                    (Field a_value)\n    \
                }\n    \
                {\n        \
                    (Literal\n            \
                        String(\"b_key\"))\n        \
                    (Field b_value)\n    \
                })",
            Ast::MultiHash(vec![
                KeyValuePair {
                    key: Ast::Literal(Rc::new(Variable::String("a_key".to_string()))),
                    value: Ast::Field("a_value".to_string()),
                },
                KeyValuePair {
                    key: Ast::Literal(Rc::new(Variable::String("b_key".to_string()))),
                    value: Ast::Field("b_value".to_string()),
                }
            ]).to_string());
    }

    #[test]
    fn not_to_string() {
        assert_eq!(
            "(Not\n    (Field a))",
            Ast::Not(Box::new(Ast::Field("a".to_string()))).to_string());
    }

    #[test]
    fn projection_to_string() {
        assert_eq!(
            "(Projection\n    (Identity)\n    (Field a))",
            Ast::Projection {
                lhs: Box::new(Ast::Identity),
                rhs: Box::new(Ast::Field("a".to_string()))
            }.to_string()
        );
    }

    #[test]
    fn object_values_to_string() {
        assert_eq!(
            "(ObjectValues\n    (Field a))",
            Ast::ObjectValues(Box::new(Ast::Field("a".to_string()))).to_string());
    }

    #[test]
    fn and_to_string() {
        assert_eq!(
            "(And\n    (Field a)\n    (Field b))",
            Ast::And {
                lhs: Box::new(Ast::Field("a".to_string())),
                rhs: Box::new(Ast::Field("b".to_string()))
            }.to_string()
        );
    }

    #[test]
    fn or_to_string() {
        assert_eq!(
            "(Or\n    (Field a)\n    (Field b))",
            Ast::Or {
                lhs: Box::new(Ast::Field("a".to_string())),
                rhs: Box::new(Ast::Field("b".to_string()))
            }.to_string()
        );
    }

    #[test]
    fn slice_to_string() {
        assert_eq!(
            "(Slice Some(0) Some(1) 2)",
            Ast::Slice {
                start: Some(0),
                stop: Some(1),
                step: 2
            }.to_string()
        );
    }

    #[test]
    fn subexpr_to_string() {
        assert_eq!(
            "(Subexpr\n    (Field a)\n    (Field b))",
            Ast::Subexpr {
                lhs: Box::new(Ast::Field("a".to_string())),
                rhs: Box::new(Ast::Field("b".to_string()))
            }.to_string()
        );
    }
}
