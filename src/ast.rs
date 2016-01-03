//! JMESPath AST
use std::rc::Rc;
use std::fmt;

use super::variable::Variable;

/// Abstract syntax tree of a JMESPath expression.
#[derive(Clone, PartialEq, PartialOrd, Debug)]
pub enum Ast {
    Comparison(Comparator, Box<Ast>, Box<Ast>),
    Condition(Box<Ast>, Box<Ast>),
    Identity,
    Expref(Box<Ast>),
    Flatten(Box<Ast>),
    Function(String, Vec<Ast>),
    Field(String),
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

/// Comparators used in Comparison nodes
#[derive(Clone, PartialEq, PartialOrd, Debug)]
pub enum Comparator {
    Eq,
    Lt,
    Lte,
    Ne,
    Gte,
    Gt
}

/// Pushes the left padding necessary for the current depth.
fn left_padding(buffer: &mut String, depth: usize) {
    if depth > 0 {
        buffer.push_str(&(0..depth).map(|_| ' ').collect::<String>());
    }
}

impl Ast {
    /// Internal implementation for pretty printing the AST.
    fn pretty(&self, depth: usize) -> String {
        let mut buffer = String::new();
        left_padding(&mut buffer, depth);
        match self {
            &Ast::Comparison(ref comparator, ref lhs, ref rhs) => {
                buffer.push_str(&format!("(Comparison {:?}\n{}\n{})",
                    comparator,
                    lhs.pretty(depth + 4),
                    rhs.pretty(depth + 4)))
            },
            &Ast::Condition(ref l, ref r) => {
                buffer.push_str(&format!("(Condition if\n{} then\n{})",
                    l.pretty(depth + 4),
                    r.pretty(depth + 4)))
            },
            &Ast::Identity => buffer.push_str(&format!("(Identity)")),
            &Ast::Expref(ref n) => {
                buffer.push_str(&format!("(Expref\n{})", n.pretty(depth + 4)))
            },
            &Ast::Flatten(ref n) => {
                buffer.push_str(&format!("(Flatten\n{})", n.pretty(depth + 4)))
            },
            &Ast::Function(ref name, ref args) => {
                buffer.push_str(&format!("(Function {}", name));
                for arg in args {
                    buffer.push_str(&format!("\n{}", arg.pretty(depth + 4)));
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
                    buffer.push_str(&format!("\n{}", element.pretty(depth + 4)));
                }
                buffer.push_str(")");
            },
            &Ast::MultiHash(ref pairs) => {
                buffer.push_str("(MultiHash");
                for kvp in pairs {
                    buffer.push_str("\n");
                    left_padding(&mut buffer, depth + 4);
                    buffer.push_str(&format!("{{\n{}\n", kvp.key.pretty(depth + 8)));
                    buffer.push_str(&format!("{}\n", kvp.value.pretty(depth + 8)));
                    left_padding(&mut buffer, depth + 4);
                    buffer.push_str("}");
                }
                buffer.push_str(")");
            },
            &Ast::Not(ref n) => {
                buffer.push_str(&format!("(Not\n{})", n.pretty(depth + 4)))
            },
            &Ast::Projection(ref lhs, ref rhs) => {
                buffer.push_str(&format!("(Projection\n{}\n{})",
                    lhs.pretty(depth + 4),
                    rhs.pretty(depth + 4)))
            },
            &Ast::ObjectValues(ref node) => {
                buffer.push_str(&format!("(ObjectValues\n{})",
                    node.pretty(depth + 4)))
            },
            &Ast::And(ref lhs, ref rhs) => {
                buffer.push_str(&format!("(And\n{}\n{})",
                    lhs.pretty(depth + 4),
                    rhs.pretty(depth + 4)))
            },
            &Ast::Or(ref lhs, ref rhs) => {
                buffer.push_str(&format!("(Or\n{}\n{})",
                    lhs.pretty(depth + 4),
                    rhs.pretty(depth + 4)))
            },
            &Ast::Slice(ref a, ref b, ref c) => {
                buffer.push_str(&format!("(Slice {:?} {:?} {})", a, b, c))
            },
            &Ast::Subexpr(ref lhs, ref rhs) => {
                buffer.push_str(&format!("(Subexpr\n{}\n{})",
                    lhs.pretty(depth + 4),
                    rhs.pretty(depth + 4)))
            },
        }
        buffer
    }
}

/// Display/to_string() will pretty-print the AST
impl fmt::Display for Ast {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(fmt, "{}", self.pretty(0))
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
            Ast::Comparison(Comparator::Eq,
                Box::new(Ast::Identity),
                Box::new(Ast::Field("a".to_string()))).to_string());
    }

    #[test]
    fn condition_to_string() {
        assert_eq!(
            "(Condition if\n    (Identity) then\n    (Field a))",
            Ast::Condition(
                Box::new(Ast::Identity),
                Box::new(Ast::Field("a".to_string()))).to_string());
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
            Ast::Function(
                "foo".to_string(),
                vec![
                    Ast::Field("a".to_string()),
                    Ast::Expref(Box::new(Ast::Field("b".to_string())))
                ]).to_string());
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
            Ast::Projection(
                Box::new(Ast::Identity),
                Box::new(Ast::Field("a".to_string()))).to_string());
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
            Ast::And(
                Box::new(Ast::Field("a".to_string())),
                Box::new(Ast::Field("b".to_string()))).to_string());
    }

    #[test]
    fn or_to_string() {
        assert_eq!(
            "(Or\n    (Field a)\n    (Field b))",
            Ast::Or(
                Box::new(Ast::Field("a".to_string())),
                Box::new(Ast::Field("b".to_string()))).to_string());
    }

    #[test]
    fn slice_to_string() {
        assert_eq!(
            "(Slice Some(0) Some(1) 2)",
            Ast::Slice(Some(0), Some(1), 2).to_string());
    }

    #[test]
    fn subexpr_to_string() {
        assert_eq!(
            "(Subexpr\n    (Field a)\n    (Field b))",
            Ast::Subexpr(
                Box::new(Ast::Field("a".to_string())),
                Box::new(Ast::Field("b".to_string()))).to_string());
    }
}
