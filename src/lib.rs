//! Rust implementation of JMESPath.
//!
//! # Compiling JMESPath expressions
//!
//! Use the `jmespath::Expression` struct to compile and execute JMESPath
//! expressions. The `Expression` struct can be used multiple times.
//!
//! # Lexer
//!
//! Use the `tokenize()` function to tokenize JMESPath expressions into a
//! stream of `jmespath::lexer::Token` variants.
//!
//! ## Examples
//!
//! The following example tokenizes a JMESPath expression and iterates over
//! each token. Tokens have a `token_name()`, `lbp()`, `is_whitespace()`
//! and `span()` method.
//!
//! ```
//! use jmespath;
//!
//! for token in jmespath::tokenize("foo.bar") {
//!     println!("This token is a {} token with a span of {}",
//!              token.token_name(), token.span());
//! }
//! ```
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

extern crate rustc_serialize;

pub use parser::{parse, Parser, ParseResult, ParseError};
pub use lexer::{tokenize, Token, Lexer};
pub use ast::{Ast, KeyValuePair, Comparator};

use std::fmt;

use rustc_serialize::json::Json;
use interpreter::interpret;

mod ast;
mod interpreter;
mod lexer;
mod parser;

/// A compiled JMESPath expression.
#[derive(Clone)]
pub struct Expression {
    ast: Ast,
    original: String,
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
    pub fn search(&self, data: Json) -> Result<Json, String> {
        interpret(&data, &self.ast)
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
    extern crate rustc_serialize;
    use self::rustc_serialize::json::Json;
    use super::*;

    #[test] fn can_evaluate_jmespath_expression() {
        let expr = Expression::new("foo.bar").unwrap();
        let json = Json::from_str("{\"foo\":{\"bar\":true}}").unwrap();
        assert_eq!(Json::Boolean(true), expr.search(json).unwrap());
    }

    #[test] fn formats_expression_as_string() {
        let expr = Expression::new("foo | baz").unwrap();
        assert_eq!("foo | baz/foo | baz", format!("{}/{:?}", expr, expr));
    }

    #[test] fn implements_partial_eq() {
        let a = Expression::new("@").unwrap();
        let b = Expression::new("@").unwrap();
        assert!(a == b);
    }

    #[test] fn can_evaluate_wildcards() {
        let expr = Expression::new("foo[*].bar").unwrap();
        let json = Json::from_str("{\"foo\":[{\"bar\":true}]}").unwrap();
        assert_eq!(Json::Array(vec![Json::Boolean(true)]), expr.search(json).unwrap());
    }

    #[test] fn can_evaluate_or_with_current_node() {
        let expr = Expression::new("a || @").unwrap();
        let json = Json::from_str("true").unwrap();
        assert_eq!(Json::Boolean(true), expr.search(json).unwrap());
    }

    #[test] fn can_evaluate_flatten_projection() {
        let expr = Expression::new("@[].b").unwrap();
        let json = Json::from_str("[{\"b\": 1}, [{\"b\":2}]]").unwrap();
        assert_eq!(Json::Array(vec!(Json::U64(1), Json::U64(2))),
                   expr.search(json).unwrap());
    }

    #[test] fn can_evaluate_filter_projection() {
        let expr = Expression::new("[?a > b]").unwrap();
        let json = Json::from_str("[{\"a\": 2, \"b\": 1}, {\"a\": 0, \"b\":2}]").unwrap();
        assert_eq!(Json::from_str("[{\"a\": 2, \"b\": 1}]").unwrap(),
                   expr.search(json).unwrap());
    }
}
