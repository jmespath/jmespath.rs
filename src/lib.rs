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
//! let expr = jmespath::Expression::new("foo.bar | baz").unwrap();
//! ```
extern crate serde_json;

pub use parser::{parse, ParseError};
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

/// Parses an expression and performs a search over data
pub fn search<T: ToJMESPath>(expression: &str, data: T) -> Result<Rc<Variable>, Error> {
    Expression::new(expression)
        .map_err(|e| Error::from(e))
        .and_then(|expr| expr.search(data).map_err(|e| Error::from(e)))
}

/// JMESPath error
#[derive(Clone,Debug,PartialEq)]
pub enum Error {
    /// An error occurred while parsing an expression.
    Parse(ParseError),
    /// An error occurred while evaluating an expression.
    Runtime(RuntimeError)
}

impl fmt::Display for Error {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            &self::Error::Parse(ref err) => write!(fmt, "Parse error: {}", err),
            &self::Error::Runtime(ref err) => write!(fmt, "Runtime error: {}", err)
        }
    }
}

impl From<RuntimeError> for Error {
    fn from(err: RuntimeError) -> Error {
        Error::Runtime(err)
    }
}

impl From<ParseError> for Error {
    fn from(err: ParseError) -> Error {
        Error::Parse(err)
    }
}

/// Runtime JMESPath error
#[derive(Clone,Debug,PartialEq)]
pub enum RuntimeError {
    InvalidSlice,
    InvalidKey {
        actual: String,
    },
    TooManyArguments {
        expected: usize,
        actual: usize,
    },
    NotEnoughArguments {
        expected: usize,
        actual: usize,
    },
    UnknownFunction {
        function: String,
    },
    InvalidType {
        expected: String,
        actual: String,
        actual_value: Rc<Variable>,
        position: usize,
    },
    InvalidReturnType {
        expected: String,
        actual: String,
        actual_value: Rc<Variable>,
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
    interpreter: TreeInterpreter
}

impl<'a> Expression<'a> {
    /// Creates a new JMESPath expression from an expression string.
    pub fn new(expression: &'a str) -> Result<Expression<'a>, ParseError> {
        Expression::with_interpreter(expression, TreeInterpreter::new())
    }

    /// Creates a new JMESPath expression using a custom tree interpreter.
    pub fn with_interpreter(expression: &'a str,
                            interpreter: TreeInterpreter)
                            -> Result<Expression<'a>, ParseError> {
        Ok(Expression {
            original: expression,
            ast: try!(parse(expression)),
            interpreter: interpreter
        })
    }

    /// Returns the result of searching data with the compiled expression.
    pub fn search<T: ToJMESPath>(&self, data: T) -> SearchResult {
        self.interpreter.interpret(data.to_jmespath(), &self.ast)
    }

    /// Returns the original string of this JMESPath expression.
    pub fn as_str(&self) -> &str {
        &self.original
    }

    /// Returns the parsed AST of this JMESPath expression.
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
    fn to_jmespath(self) -> Rc<Variable>;
}

impl ToJMESPath for Rc<Variable> {
    fn to_jmespath(self) -> Rc<Variable> {
        self
    }
}

impl ToJMESPath for Variable {
    fn to_jmespath(self) -> Rc<Variable> {
        Rc::new(self)
    }
}

impl ToJMESPath for Value {
    fn to_jmespath(self) -> Rc<Variable> {
        Rc::new(Variable::from_json(&self))
    }
}

impl <'a> ToJMESPath for &'a Value {
    fn to_jmespath(self) -> Rc<Variable> {
        Rc::new(Variable::from_json(self))
    }
}

impl ToJMESPath for bool {
    fn to_jmespath(self) -> Rc<Variable> {
        Rc::new(Variable::Bool(self))
    }
}

impl ToJMESPath for usize {
    fn to_jmespath(self) -> Rc<Variable> {
        Rc::new(Variable::U64(self as u64))
    }
}

impl ToJMESPath for u64 {
    fn to_jmespath(self) -> Rc<Variable> {
        Rc::new(Variable::U64(self))
    }
}

impl ToJMESPath for f64 {
    fn to_jmespath(self) -> Rc<Variable> {
        Rc::new(Variable::F64(self))
    }
}

impl ToJMESPath for i64 {
    fn to_jmespath(self) -> Rc<Variable> {
        Rc::new(Variable::I64(self))
    }
}

/// Creates a Variable::Null value.
impl ToJMESPath for () {
    fn to_jmespath(self) -> Rc<Variable> {
        Rc::new(Variable::Null)
    }
}

impl ToJMESPath for String {
    fn to_jmespath(self) -> Rc<Variable> {
        Rc::new(Variable::String(self))
    }
}

impl <'a> ToJMESPath for &'a str {
    fn to_jmespath(self) -> Rc<Variable> {
        Rc::new(Variable::String(self.to_string()))
    }
}

/// Creates a Variable::Expref value.
impl ToJMESPath for Ast {
    fn to_jmespath(self) -> Rc<Variable> {
        Rc::new(Variable::Expref(self))
    }
}

/// Creates a Variable::Array value.
impl ToJMESPath for Vec<Rc<Variable>> {
    fn to_jmespath(self) -> Rc<Variable> {
        Rc::new(Variable::Array(self))
    }
}

/// Creates a Variable::Object value.
impl ToJMESPath for BTreeMap<String, Rc<Variable>> {
    fn to_jmespath(self) -> Rc<Variable> {
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
