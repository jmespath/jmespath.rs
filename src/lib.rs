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
//! let data = jmespath::Variable::from_str(json_str).unwrap();
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
//! assert_eq!(&Ast::Field("foo".to_string()), expr.as_ast());
//! assert_eq!("(Field foo)", expr.as_ast().to_string());
//! ```
//!
//! # Using `jmespath::search`
//!
//! The `jmespath::search` function can be used for more simplified searching
//! when expression reuse is not important. `jmespath::search` will compile
//! the given expression and evaluate the expression against the provided
//! data. If a parse error occurs, a `jmespath::Error::ParseError` is
//! returned in a `Result`. If the expression is able to be parsed but an
//! error occurs, a `jmespath::Error::Runtime` error is returned in a
//! `Result`.
//!
//! ```
//! use jmespath;
//!
//! let data = jmespath::Variable::from_str("{\"foo\":null}").unwrap();
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
//! Any value that implements the `jmespath::ToJMESPath` trait can be
//! searched without needing explicit coercions. This includes a number of
//! common types, including serde's `serde_json::Value` enum.

extern crate serde_json;

pub use parser::{parse, ParseError, ParseResult};
pub use variable::Variable;
pub use interpreter::{TreeInterpreter, SearchResult};

use std::collections::BTreeMap;
use std::fmt;
use std::rc::Rc;

use self::serde_json::Value;

use ast::Ast;

pub mod ast;
pub mod functions;
mod parser;
mod lexer;
mod interpreter;
mod variable;

pub type RcVar = Rc<Variable>;

/// Parses an expression and performs a search over the data.
pub fn search<T: ToJMESPath>(expression: &str, data: T) -> Result<RcVar, Error> {
    Expression::new(expression)
        .map_err(|e| Error::from(e))
        .and_then(|expr| expr.search(data).map_err(|e| Error::from(e)))
}

/// Aggregate JMESPath error for both parse and runtime errors.
#[derive(Clone,Debug,PartialEq)]
pub enum Error {
    /// An error occurred while parsing an expression.
    Parse(ParseError),
    /// An error occurred while evaluating an expression.
    Runtime(RuntimeError)
}

/// Displaying/to_string() of an error simply proxies to the wrapped error.
impl fmt::Display for Error {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            &self::Error::Parse(ref err) => write!(fmt, "Parse error: {}", err),
            &self::Error::Runtime(ref err) => write!(fmt, "Runtime error: {}", err)
        }
    }
}

/// Converts a RuntimeError to an Error
impl From<RuntimeError> for Error {
    fn from(err: RuntimeError) -> Error {
        Error::Runtime(err)
    }
}

/// Converts a ParseError to an Error
impl From<ParseError> for Error {
    fn from(err: ParseError) -> Error {
        Error::Parse(err)
    }
}

/// Runtime JMESPath error
#[derive(Clone,Debug,PartialEq)]
pub enum RuntimeError {
    /// Encountered when a slice expression uses a step of 0
    InvalidSlice,
    /// Encountered when a key is not a string.
    InvalidKey {
        actual: String,
    },
    /// Encountered when too many arguments are provided to a function.
    TooManyArguments {
        expected: usize,
        actual: usize,
    },
    /// Encountered when too few arguments are provided to a function.
    NotEnoughArguments {
        expected: usize,
        actual: usize,
    },
    /// Encountered when an unknown function is called.
    UnknownFunction {
        function: String,
    },
    /// Encountered when a type of variable given to a function is invalid.
    InvalidType {
        expected: String,
        actual: String,
        actual_value: RcVar,
        position: usize,
    },
    /// Encountered when an expression reference returns an invalid type.
    InvalidReturnType {
        expected: String,
        actual: String,
        actual_value: RcVar,
        position: usize,
        invocation: usize,
    },
}

impl fmt::Display for RuntimeError {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        use self::RuntimeError::*;
        match self {
            &UnknownFunction { ref function } => {
                write!(fmt, "Call to undefined function {}", function)
            },
            &TooManyArguments { ref expected, ref actual } => {
                write!(fmt, "Too many arguments, expected {}, found {}", expected, actual)
            },
            &NotEnoughArguments { ref expected, ref actual } => {
                write!(fmt, "Not enough arguments, expected {}, found {}", expected, actual)
            },
            &InvalidType { ref expected, ref actual, ref position, ref actual_value } => {
                write!(fmt, "Argument {} expects type {}, given {} {}",
                            position, expected, actual,
                            actual_value.to_string().unwrap_or(format!("{:?}", actual_value)))
            },
            &InvalidSlice => write!(fmt, "Invalid slice"),
            &InvalidReturnType { ref expected, ref actual, ref position, ref invocation,
                ref actual_value } => {
                write!(fmt, "Argument {} must return {} but invocation {} returned {} {}",
                       position, expected, invocation, actual,
                       actual_value.to_string().unwrap_or(format!("{:?}", actual_value)))
            },
            &InvalidKey { ref actual } => {
                write!(fmt, "Invalid key. Expected string, found {:?}", actual)
            },
        }
    }
}

/// A compiled JMESPath expression.
pub struct Expression<'a> {
    ast: Ast,
    original: &'a str,
    interpreter: Option<&'a TreeInterpreter>
}

impl<'a> Expression<'a> {
    /// Creates a new JMESPath expression from an expression string.
    pub fn new(expression: &'a str) -> Result<Expression<'a>, ParseError> {
        Expression::with_interpreter(expression, None)
    }

    /// Creates a new JMESPath expression using a custom tree interpreter.
    /// Customer interpreters may be desired when you wish to utilize custom
    /// JMESPath functions in your expressions.
    #[inline]
    pub fn with_interpreter(expression: &'a str,
                            interpreter: Option<&'a TreeInterpreter>)
                            -> Result<Expression<'a>, ParseError> {
        Ok(Expression {
            original: expression,
            ast: try!(parse(expression)),
            interpreter: interpreter
        })
    }

    /// Returns the result of searching data with the compiled expression.
    pub fn search<T: ToJMESPath>(&self, data: T) -> SearchResult {
        let to_jmespath = data.to_jmespath();
        match self.interpreter {
            Some(i) => i.interpret(to_jmespath, &self.ast),
            None => TreeInterpreter::new().interpret(to_jmespath, &self.ast)
        }
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

impl<'a> fmt::Display for Expression<'a> {
    /// Shows the original jmespath expression.
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.as_str())
    }
}

impl<'a> fmt::Debug for Expression<'a> {
    /// Shows the original jmespath expression.
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Display::fmt(self, f)
    }
}

/// Equality comparison is based on the original string.
impl<'a> PartialEq for Expression<'a> {
    fn eq(&self, other: &Expression) -> bool {
        self.as_str() == other.as_str()
    }
}

/// Converts a value into a reference-counted JMESPath Variable that
/// can be used by the JMESPath runtime.
pub trait ToJMESPath {
    fn to_jmespath(self) -> RcVar;
}

impl ToJMESPath for RcVar {
    fn to_jmespath(self) -> RcVar {
        self
    }
}

impl ToJMESPath for Variable {
    fn to_jmespath(self) -> RcVar {
        Rc::new(self)
    }
}

impl ToJMESPath for Value {
    fn to_jmespath(self) -> RcVar {
        Rc::new(Variable::from_json(&self))
    }
}

impl <'a> ToJMESPath for &'a Value {
    fn to_jmespath(self) -> RcVar {
        Rc::new(Variable::from_json(self))
    }
}

impl ToJMESPath for bool {
    fn to_jmespath(self) -> RcVar {
        Rc::new(Variable::Bool(self))
    }
}

impl ToJMESPath for usize {
    fn to_jmespath(self) -> RcVar {
        Rc::new(Variable::U64(self as u64))
    }
}

impl ToJMESPath for u64 {
    fn to_jmespath(self) -> RcVar {
        Rc::new(Variable::U64(self))
    }
}

impl ToJMESPath for f64 {
    fn to_jmespath(self) -> RcVar {
        Rc::new(Variable::F64(self))
    }
}

impl ToJMESPath for i64 {
    fn to_jmespath(self) -> RcVar {
        Rc::new(Variable::I64(self))
    }
}

/// Creates a Variable::Null value.
impl ToJMESPath for () {
    fn to_jmespath(self) -> RcVar {
        Rc::new(Variable::Null)
    }
}

impl ToJMESPath for String {
    fn to_jmespath(self) -> RcVar {
        Rc::new(Variable::String(self))
    }
}

impl <'a> ToJMESPath for &'a str {
    fn to_jmespath(self) -> RcVar {
        Rc::new(Variable::String(self.to_string()))
    }
}

/// Creates a Variable::Expref value bound to the Ast node.
impl ToJMESPath for Ast {
    fn to_jmespath(self) -> RcVar {
        Rc::new(Variable::Expref(self))
    }
}

/// Creates a Variable::Array value.
impl ToJMESPath for Vec<RcVar> {
    fn to_jmespath(self) -> RcVar {
        Rc::new(Variable::Array(self))
    }
}

/// Creates a Variable::Object value.
impl ToJMESPath for BTreeMap<String, RcVar> {
    fn to_jmespath(self) -> RcVar {
        Rc::new(Variable::Object(self))
    }
}


#[cfg(test)]
mod test {
    use super::*;
    use std::rc::Rc;

    #[test]
    fn formats_expression_as_string() {
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
        let var = Variable::from_str("{\"foo\":{\"bar\":true}}").unwrap();
        assert_eq!(Rc::new(Variable::Bool(true)), expr.search(var).unwrap());
    }

    #[test]
    fn can_search() {
        assert_eq!(Rc::new(Variable::Bool(true)), search("`true`", ()).unwrap());
    }
}
