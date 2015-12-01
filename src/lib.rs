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
extern crate rustc_serialize;

pub use variable::Variable;

use std::collections::BTreeMap;
use std::fmt;
use std::rc::Rc;
use self::rustc_serialize::json::Json;

use ast::Ast;
use functions::FnDispatcher;
use interpreter::TreeInterpreter;
use parser::{parse, ParseError};

pub mod ast;
pub mod lexer;
pub mod parser;
mod functions;
mod interpreter;
mod variable;

/// A compiled JMESPath expression.
#[derive(Clone)]
pub struct Expression {
    pub ast: Ast,
    original: String,
    tree_interpreter: TreeInterpreter
}

impl Expression {
    /// Creates a new JMESPath expression from an expression string.
    pub fn new(expression: &str) -> Result<Expression, ParseError> {
        Expression::with_tree_interpreter(expression, TreeInterpreter::new(FnDispatcher::new()))
    }

    /// Creates a new JMESPath expression using a custom tree interpreter.
    pub fn with_tree_interpreter(expression: &str, tree_interpreter: TreeInterpreter)
            -> Result<Expression, ParseError> {
        Ok(Expression {
            original: expression.to_string(),
            ast: try!(parse(expression)),
            tree_interpreter: tree_interpreter
        })
    }

    /// Returns the result of searching data with the compiled expression.
    pub fn search<S>(&self, data: S) -> Result<Rc<Variable>, String>
            where S: IntoJMESPath {
        self.tree_interpreter.interpret(data.into_jmespath(), &self.ast)
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

/// Converts a value into a reference-counted JMESPath Variable that
/// can be used by the JMESPath runtime.
pub trait IntoJMESPath {
    fn into_jmespath(self) -> Rc<Variable>;
}

impl IntoJMESPath for Rc<Variable> {
    fn into_jmespath(self) -> Rc<Variable> {
        self
    }
}

impl IntoJMESPath for Variable {
    fn into_jmespath(self) -> Rc<Variable> {
        Rc::new(self)
    }
}

impl <'a> IntoJMESPath for &'a Json {
    fn into_jmespath(self) -> Rc<Variable> {
        Rc::new(Variable::from_json(self))
    }
}

impl IntoJMESPath for bool {
    fn into_jmespath(self) -> Rc<Variable> {
        Rc::new(Variable::Boolean(self))
    }
}

impl IntoJMESPath for usize {
    fn into_jmespath(self) -> Rc<Variable> {
        Rc::new(Variable::U64(self as u64))
    }
}

impl IntoJMESPath for u64 {
    fn into_jmespath(self) -> Rc<Variable> {
        Rc::new(Variable::U64(self))
    }
}

impl IntoJMESPath for f64 {
    fn into_jmespath(self) -> Rc<Variable> {
        Rc::new(Variable::F64(self))
    }
}

impl IntoJMESPath for i64 {
    fn into_jmespath(self) -> Rc<Variable> {
        Rc::new(Variable::I64(self))
    }
}

/// Creates a Variable::Null value.
impl IntoJMESPath for () {
    fn into_jmespath(self) -> Rc<Variable> {
        Rc::new(Variable::Null)
    }
}

impl IntoJMESPath for String {
    fn into_jmespath(self) -> Rc<Variable> {
        Rc::new(Variable::String(self))
    }
}

impl <'a> IntoJMESPath for &'a str {
    fn into_jmespath(self) -> Rc<Variable> {
        Rc::new(Variable::String(self.to_string()))
    }
}

/// Creates a Variable::Expref value.
impl IntoJMESPath for Ast {
    fn into_jmespath(self) -> Rc<Variable> {
        Rc::new(Variable::Expref(self))
    }
}

/// Creates a Variable::Array value.
impl IntoJMESPath for Vec<Rc<Variable>> {
    fn into_jmespath(self) -> Rc<Variable> {
        Rc::new(Variable::Array(self))
    }
}

/// Creates a Variable::Object value.
impl IntoJMESPath for BTreeMap<String, Rc<Variable>> {
    fn into_jmespath(self) -> Rc<Variable> {
        Rc::new(Variable::Object(self))
    }
}


#[cfg(test)]
mod test {
    extern crate rustc_serialize;

    use super::*;
    use std::rc::Rc;
    use self::rustc_serialize::json::Json;

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
        assert_eq!(Rc::new(Variable::Boolean(true)), expr.search(var).unwrap());
    }

    #[test]
    fn can_create_from_json_reference_and_release_ownership() {
        let expr = Expression::new("foo.bar").unwrap();
        let var = Json::from_str("{\"foo\":{\"bar\":true}}").unwrap();
        let result = expr.search(&var).unwrap();
        assert_eq!(Rc::new(Variable::Boolean(true)), result);
        assert!(var.is_object());
    }
}
