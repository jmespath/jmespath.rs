//! Rust implementation of JMESPath.
//!
//! # Compiling JMESPath expressions
//!
//! Use the `jmespath::Expression` struct to compile and execute JMESPath
//! expressions. The `Expression` struct can be used multiple times.
//!
//! # Parser
//!
//! Use the `parse()` function to parse a JMESPath expressions into an
//! abstract syntax tree (AST).
//!
//! ## Examples
//!
//! The following example parses a JMESPath expression into an AST.
//!
//! ```
//! use jmespath;
//!
//! let ast = jmespath::parse("foo.bar | baz");
//! ```

pub use parser::parse;
pub use variable::Variable;

use std::fmt;
use std::rc::Rc;

use ast::Ast;
use parser::ParseError;
use interpreter::interpret;

pub mod ast;
pub mod functions;
pub mod interpreter;
pub mod lexer;
pub mod parser;
mod variable;

/// A compiled JMESPath expression.
#[derive(Clone)]
pub struct Expression {
    ast: Ast,
    original: String
}

impl Expression {
    /// Creates a new JMESPath expression from an expression string.
    pub fn new(expression: &str) -> Result<Expression, ParseError> {
        Ok(Expression {
            original: expression.to_string(),
            ast: try!(parse(expression))
        })
    }

    /// Returns the result of searching data with the compiled expression.
    pub fn search(&self, data: Rc<Variable>) -> Result<Rc<Variable>, String> {
        interpret(data, &self.ast)
    }

    /// Returns the original string of this JMESPath expression.
    pub fn as_str<'a>(&'a self) -> &'a str {
        &self.original
    }
}

impl fmt::Display for Expression {
    /// Shows the original jmespath expression.
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.as_str())
    }
}

impl fmt::Debug for Expression {
    /// Shows the original regular expression.
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Display::fmt(self, f)
    }
}

/// Equality comparison is based on the original string.
impl PartialEq for Expression {
    fn eq(&self, other: &Expression) -> bool {
        self.as_str() == other.as_str()
    }
}


#[cfg(test)]
mod test {
    use super::*;
    use std::rc::Rc;

    #[test] fn formats_expression_as_string() {
        let expr = Expression::new("foo | baz").unwrap();
        assert_eq!("foo | baz/foo | baz", format!("{}/{:?}", expr, expr));
    }

    #[test] fn implements_partial_eq() {
        let a = Expression::new("@").unwrap();
        let b = Expression::new("@").unwrap();
        assert!(a == b);
    }

    #[test] fn can_evaluate_jmespath_expression() {
        let expr = Expression::new("foo.bar").unwrap();
        let var = Rc::new(Variable::from_str("{\"foo\":{\"bar\":true}}").unwrap());
        assert_eq!(Rc::new(Variable::Boolean(true)), expr.search(var).unwrap());
    }
}
