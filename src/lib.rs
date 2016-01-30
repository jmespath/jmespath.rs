//! Rust implementation of JMESPath, a query language for JSON.
//!
//! # Usage
//!
//! This crate is [on crates.io](https://crates.io/crates/jmespath) and
//! can be used by adding `jmespath` to the dependencies in your
//! project's `Cargo.toml`.
//!
//! ```toml
//! [dependencies]
//! jmespath = "0.0.1"
//! ```
//!
//! and this to your crate root:
//!
//! ```rust
//! extern crate jmespath;
//! ```
//!
//! # Compiling JMESPath expressions
//!
//! Use the `jmespath::Expression` struct to compile and execute JMESPath
//! expressions. The `Expression` struct can be used multiple times on
//! different values without having to recompile the expression.
//!
//! ```
//! use jmespath;
//!
//! let expr = jmespath::Expression::new("foo.bar | baz").unwrap();
//!
//! // Parse some JSON data into a JMESPath variable
//! let json_str = "{\"foo\":{\"bar\":{\"baz\":true}}}";
//! let data = jmespath::Variable::from_json(json_str).unwrap();
//!
//! // Search the data with the compiled expression
//! let result = expr.search(data).unwrap();
//! assert_eq!(true, result.as_boolean().unwrap());
//! ```
//!
//! You can get the original expression as a string and the parsed expression
//! AST from the `Expression` struct:
//!
//! ```
//! use jmespath;
//! use jmespath::ast::Ast;
//!
//! let expr = jmespath::Expression::new("foo").unwrap();
//! assert_eq!("foo", expr.as_str());
//! assert_eq!(&Ast::Field {name: "foo".to_string(), offset: 0}, expr.as_ast());
//! ```
//!
//! # Using `jmespath::search`
//!
//! The `jmespath::search` function can be used for more simplified searching
//! when expression reuse is not important. `jmespath::search` will compile
//! the given expression and evaluate the expression against the provided
//! data.
//!
//! ```
//! use jmespath;
//!
//! let data = jmespath::Variable::from_json("{\"foo\":null}").unwrap();
//! let result = jmespath::search("foo", data).unwrap();
//! assert!(result.is_null());
//! ```
//!
//! ## JMESPath variables
//!
//! In order to evaluate expressions against a known data type, the
//! `jmespath::Variable` enum is used as both the input and output type.
//! More specifically, `Rc<Variable>` (or `jmespath::RcVar`) is used to allow
//! shared, reference counted data to be used by the JMESPath interpreter at
//! runtime.
//!
//! Because `jmespath::Variable` implements `serde::ser::Serialize`, many
//! existing types can be searched without needing an explicit coercion,
//! and any type that needs coercion can be implemented using serde's macros
//! or code generation capabilities. Any value that implements the
//! `serde::ser::Serialize` trait can be searched without needing explicit
//! coercions. This includes a number of common types, including serde's
//! `serde_json::Value` enum.
//!
//! The return value of searching data with JMESPath is also an `RcVar` (an
//! `Rc<Variable>`). `Variable` has a number of helper methods that make
//! it a data type that can be used directly, or you can convert `Variable`
//! to any serde value implementing `serde::de::Deserialize`.
//!
//! ```
//! // Search an arbitrary data type that implements serde::ser::Serialize
//! let data = vec![true, false];
//! // Get the result as an RcVar
//! let result = jmespath::search("[0]", data).unwrap();
//! // Convert the result to a type that implements serde::de::Deserialize
//! let my_bool: bool = result.to_deserialize().unwrap();
//! assert_eq!(true, my_bool);
//! ```

#![cfg_attr(feature="clippy", feature(plugin))]
#![cfg_attr(feature="clippy", plugin(clippy))]

extern crate serde;
extern crate serde_json;

pub use errors::{Error, ErrorReason, RuntimeError, Coordinates};
pub use parser::{parse, ParseResult};
pub use lexer::tokenize;
pub use variable::Variable;

use std::fmt;
use std::rc::Rc;

use self::serde::Serialize;

use ast::Ast;
use functions::{FnDispatcher, BuiltinDispatcher};
use variable::Serializer;
use interpreter::{interpret, Context, SearchResult};

pub mod ast;
pub mod functions;
pub mod interpreter;

mod parser;
mod lexer;
mod errors;
mod variable;

pub type RcVar = Rc<Variable>;

/// Parses an expression and performs a search over the data.
pub fn search<T: Serialize>(expression: &str, data: T) -> Result<RcVar, Error> {
    Expression::new(expression).and_then(|expr| expr.search(data))
}

/// A compiled JMESPath expression.
pub struct Expression {
    ast: Ast,
    original: String,
    fn_dispatcher: Rc<FnDispatcher>
}

impl Expression {
    /// Creates a new JMESPath expression from an expression string.
    pub fn new(expression: &str) -> Result<Expression, Error> {
        Self::with_fn_dispatcher(expression, Rc::new(BuiltinDispatcher))
    }

    /// Creates a new JMESPath expression using a custom tree interpreter.
    /// Customer interpreters may be desired when you wish to utilize custom
    /// JMESPath functions in your expressions.
    #[inline]
    pub fn with_fn_dispatcher(expression: &str,
                              fn_dispatcher: Rc<FnDispatcher>)
                              -> Result<Expression, Error> {
        Ok(Expression {
            original: expression.to_owned(),
            ast: try!(parse(expression)),
            fn_dispatcher: fn_dispatcher
        })
    }

    /// Returns the result of searching Serde data with the compiled expression.
    pub fn search<T: Serialize>(&self, data: T) -> SearchResult {
        let mut ser = Serializer::new();
        data.serialize(&mut ser).ok().unwrap();
        self.search_variable(&Rc::new(ser.unwrap()))
    }

    /// Returns the result of searching a JMESPath variable with the compiled expression.
    ///
    /// NOTE: This specific method could eventually be removed once specialization
    ///     lands in Rust. See https://github.com/rust-lang/rfcs/pull/1210
    pub fn search_variable(&self, data: &RcVar) -> SearchResult {
        let mut ctx = Context::new(&self.original, &*self.fn_dispatcher);
        interpret(data, &self.ast, &mut ctx)
    }

    /// Returns the JMESPath expression from which the Expression was compiled.
    pub fn as_str(&self) -> &str {
        &self.original
    }

    /// Returns the AST of the parsed JMESPath expression.
    pub fn as_ast(&self) -> &Ast {
        &self.ast
    }
}

impl fmt::Display for Expression {
    /// Shows the original jmespath expression.
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.as_str())
    }
}

impl fmt::Debug for Expression {
    /// Shows the original jmespath expression.
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
    use std::rc::Rc;

    use super::*;
    use super::ast::Ast;

    #[test]
    fn formats_expression_as_string_or_debug() {
        let expr = Expression::new("foo | baz").unwrap();
        assert_eq!("foo | baz/foo | baz", format!("{}/{:?}", expr, expr));
    }

    #[test]
    fn implements_partial_eq() {
        let a = Expression::new("@").unwrap();
        let b = Expression::new("@").unwrap();
        assert!(a == b);
    }

    #[test]
    fn can_evaluate_jmespath_expression() {
        let expr = Expression::new("foo.bar").unwrap();
        let var = Variable::from_json("{\"foo\":{\"bar\":true}}").unwrap();
        assert_eq!(Rc::new(Variable::Bool(true)), expr.search(var).unwrap());
    }

    #[test]
    fn can_search() {
        assert_eq!(Rc::new(Variable::Bool(true)), search("`true`", ()).unwrap());
    }

    #[test]
    fn can_get_expression_ast() {
        let expr = Expression::new("foo").unwrap();
        assert_eq!(&Ast::Field {offset: 0, name: "foo".to_string()}, expr.as_ast());
    }
}
