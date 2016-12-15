//! Rust implementation of JMESPath, a query language for JSON.
//!
//! Note: currently requires the nightly compiler for specialization.
//!
//! # Compiling JMESPath expressions
//!
//! Use the `jmespath::compile` function to compile JMESPath expressions
//! into reusable `Expression` structs. The `Expression` struct can be
//! used multiple times on different values without having to recompile
//! the expression.
//!
//! ```
//! use jmespath;
//!
//! let expr = jmespath::compile("foo.bar | baz").unwrap();
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
//! let expr = jmespath::compile("foo").unwrap();
//! assert_eq!("foo", expr.as_str());
//! assert_eq!(&Ast::Field {name: "foo".to_string(), offset: 0}, expr.as_ast());
//! ```
//!
//! ## JMESPath variables
//!
//! In order to evaluate expressions against a known data type, the
//! `jmespath::Variable` enum is used as both the input and output type.
//! More specifically, `Rcvar` (or `jmespath::Rcvar`) is used to allow
//! shared, reference counted data to be used by the JMESPath interpreter at
//! runtime.
//!
//! By default, `Rcvar` is an `std::rc::Rc<Variable>`. However, by specifying
//! the `sync` feature, you can utilize an `std::sync::Arc<Variable>` to
//! share `Expression` structs across threads.
//!
//! Any type that implements `ToJmespath` can be used in a JMESPath
//! Expression. Various types have default `ToJmespath` implementations,
//! including `serde::ser::Serialize`. Because `jmespath::Variable` implements
//! `serde::ser::Serialize`, many existing types can be searched without needing
//! an explicit coercion, and any type that needs coercion can be implemented
//! using serde's macros or code generation capabilities. This includes a
//! number of common types, including serde's `serde_json::Value` enum.
//!
//! The return value of searching data with JMESPath is also an `Rcvar`.
//! `Variable` has a number of helper methods that make it a data type that
//! can be used directly, or you can convert `Variable` to any serde value
//! implementing `serde::de::Deserialize`.
//!
//! # Custom Functions
//!
//! You can register custom functions with a JMESPath expression by using
//! a custom `Runtime`. When you call `jmespath::compile`, you are using a
//! shared `Runtime` instance that is created lazily using `lazy_static`.
//! This shared `Runtime` utilizes all of the builtin JMESPath functions
//! by default. However, custom functions may be utilized by creating a custom
//! `Runtime` and compiling expressions directly from the `Runtime`.
//!
//! ```
//! use jmespath::{Runtime, Context, Rcvar};
//! use jmespath::functions::{CustomFunction, Signature, ArgumentType};
//!
//! // Create a new Runtime.
//! let mut runtime = Runtime::new();
//! // Register builtin functions with the runtime.
//! runtime.register_builtin_functions();
//!
//! // Create an identity string function that returns string values as-is.
//! runtime.register_function("str_identity", Box::new(CustomFunction::new(
//!     Signature::new(vec![ArgumentType::String], None),
//!     Box::new(|args: &[Rcvar], _: &mut Context| Ok(args[0].clone()))
//! )));
//!
//! // You can also use normal closures as functions.
//! runtime.register_function("identity",
//!     Box::new(|args: &[Rcvar], _: &mut Context| Ok(args[0].clone())));
//!
//! let expr = runtime.compile("str_identity('foo')").unwrap();
//! assert_eq!("foo", expr.search(()).unwrap().as_string().unwrap());
//!
//! let expr = runtime.compile("identity('bar')").unwrap();
//! assert_eq!("bar", expr.search(()).unwrap().as_string().unwrap());
//! ```

#![feature(specialization)]
#![cfg_attr(feature="clippy", feature(plugin))]
#![cfg_attr(feature="clippy", plugin(clippy))]

#[macro_use]
extern crate lazy_static;

extern crate serde;
extern crate serde_json;

pub use errors::{JmespathError, ErrorReason, RuntimeError};
pub use parser::{parse, ParseResult};
pub use runtime::Runtime;
pub use variable::Variable;

pub mod ast;
pub mod functions;

use std::fmt;
use serde::ser;
use serde_json::Value;

use ast::Ast;
use variable::Serializer;
use interpreter::{interpret, SearchResult};

mod interpreter;
mod parser;
mod lexer;
mod runtime;
mod errors;
mod variable;

lazy_static! {
    pub static ref DEFAULT_RUNTIME: Runtime = {
        let mut runtime = Runtime::new();
        runtime.register_builtin_functions();
        runtime
    };
}

/// Reference counted JMESPath variable.
#[cfg(not(feature = "sync"))]
pub type Rcvar = std::rc::Rc<Variable>;
/// Reference counted JMESPath variable.
#[cfg(feature = "sync")]
pub type Rcvar = std::sync::Arc<Variable>;

/// Compiles a JMESPath expression using the default Runtime.
///
/// The provided expression is expected to adhere to the JMESPath
/// grammar: http://jmespath.org/specification.html
pub fn compile(expression: &str) -> Result<Expression<'static>, JmespathError> {
    DEFAULT_RUNTIME.compile(expression)
}

/// Converts a value into a reference-counted JMESPath Variable.
///
/// There are a number of implemenations for ToJmespath built into
/// the library that should work for most cases, including a generic
/// serde Serialize implemenation.
pub trait ToJmespath {
    fn to_jmespath(self) -> Rcvar;
}

/// Create searchable values from Serde serializable values.
impl<'a, T: ser::Serialize> ToJmespath for T {
    default fn to_jmespath(self) -> Rcvar {
        let mut ser = Serializer::new();
        self.serialize(&mut ser).ok().unwrap();
        Rcvar::new(ser.unwrap())
    }
}

impl ToJmespath for Value {
    fn to_jmespath(self) -> Rcvar {
        Rcvar::new(Variable::from(self))
    }
}

impl<'a> ToJmespath for &'a Value {
    fn to_jmespath(self) -> Rcvar {
        Rcvar::new(Variable::from(self))
    }
}

/// Identity coercion.
impl ToJmespath for Rcvar {
    fn to_jmespath(self) -> Rcvar {
        self
    }
}

impl<'a> ToJmespath for &'a Rcvar {
    fn to_jmespath(self) -> Rcvar {
        self.clone()
    }
}

impl ToJmespath for Variable {
    fn to_jmespath(self) -> Rcvar {
        Rcvar::new(self)
    }
}

impl<'a> ToJmespath for &'a Variable {
    fn to_jmespath(self) -> Rcvar {
        Rcvar::new(self.clone())
    }
}

impl ToJmespath for String {
    fn to_jmespath(self) -> Rcvar {
        Rcvar::new(Variable::String(self))
    }
}

impl<'a> ToJmespath for &'a str {
    fn to_jmespath(self) -> Rcvar {
        Rcvar::new(Variable::String(self.to_owned()))
    }
}

impl ToJmespath for i8 {
    fn to_jmespath(self) -> Rcvar {
        Rcvar::new(Variable::Number(self as f64))
    }
}

impl ToJmespath for i16 {
    fn to_jmespath(self) -> Rcvar {
        Rcvar::new(Variable::Number(self as f64))
    }
}

impl ToJmespath for i32 {
    fn to_jmespath(self) -> Rcvar {
        Rcvar::new(Variable::Number(self as f64))
    }
}

impl ToJmespath for i64 {
    fn to_jmespath(self) -> Rcvar {
        Rcvar::new(Variable::Number(self as f64))
    }
}

impl ToJmespath for u8 {
    fn to_jmespath(self) -> Rcvar {
        Rcvar::new(Variable::Number(self as f64))
    }
}

impl ToJmespath for u16 {
    fn to_jmespath(self) -> Rcvar {
        Rcvar::new(Variable::Number(self as f64))
    }
}

impl ToJmespath for u32 {
    fn to_jmespath(self) -> Rcvar {
        Rcvar::new(Variable::Number(self as f64))
    }
}

impl ToJmespath for u64 {
    fn to_jmespath(self) -> Rcvar {
        Rcvar::new(Variable::Number(self as f64))
    }
}

impl ToJmespath for isize {
    fn to_jmespath(self) -> Rcvar {
        Rcvar::new(Variable::Number(self as f64))
    }
}

impl ToJmespath for usize {
    fn to_jmespath(self) -> Rcvar {
        Rcvar::new(Variable::Number(self as f64))
    }
}

impl ToJmespath for f32 {
    fn to_jmespath(self) -> Rcvar {
        Rcvar::new(Variable::Number(self as f64))
    }
}

impl ToJmespath for f64 {
    fn to_jmespath(self) -> Rcvar {
        Rcvar::new(Variable::Number(self as f64))
    }
}

impl ToJmespath for () {
    fn to_jmespath(self) -> Rcvar {
        Rcvar::new(Variable::Null)
    }
}

impl ToJmespath for bool {
    fn to_jmespath(self) -> Rcvar {
        Rcvar::new(Variable::Bool(self))
    }
}

/// A compiled JMESPath expression.
///
/// The compiled expression can be used multiple times without incurring
/// the cost of re-parsing the expression each time. The expression may
/// be shared between threads if JMESPath is compiled with the `sync`
/// feature, which forces the use of an `Arc` instead of an `Rc` for
/// runtime variables.
pub struct Expression<'a> {
    ast: Ast,
    expression: String,
    runtime: &'a Runtime,
}

impl<'a> Expression<'a> {
    /// Creates a new JMESPath expression.
    #[inline]
    pub fn new<S>(expression: S, ast: Ast, runtime: &'a Runtime) -> Expression<'a>
        where S: Into<String>
    {
        Expression {
            expression: expression.into(),
            ast: ast,
            runtime: runtime,
        }
    }

    /// Returns the result of searching data with the compiled expression.
    ///
    /// The SearchResult contains a JMESPath Rcvar, or a reference counted
    /// Variable. This value can be used directly like a JSON object.
    /// Alternatively, Variable does implement Serde serialzation and
    /// deserialization, so it can easily be marshalled to another type.
    pub fn search<T: ToJmespath>(&self, data: T) -> SearchResult {
        let mut ctx = Context::new(&self.expression, self.runtime);
        interpret(&data.to_jmespath(), &self.ast, &mut ctx)
    }

    /// Returns the JMESPath expression from which the Expression was compiled.
    ///
    /// Note that this is the same value that is returned by calling
    /// `to_string`.
    pub fn as_str(&self) -> &str {
        &self.expression
    }

    /// Returns the AST of the parsed JMESPath expression.
    ///
    /// This can be useful for debugging purposes, caching, etc.
    pub fn as_ast(&self) -> &Ast {
        &self.ast
    }
}

impl<'a> fmt::Display for Expression<'a> {
    /// Shows the jmespath expression as a string.
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.as_str())
    }
}

impl<'a> fmt::Debug for Expression<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Display::fmt(self, f)
    }
}

impl<'a> PartialEq for Expression<'a> {
    fn eq(&self, other: &Expression) -> bool {
        self.as_str() == other.as_str()
    }
}

/// Context object used for error reporting.
///
/// The Context struct is mostly used when interacting between the
/// interpreter and function implemenations. Unless you're writing
/// custom JMESPath functions, this struct is an implementation
/// detail.
pub struct Context<'a> {
    /// Expression that is being interpreted.
    pub expression: &'a str,
    /// JMESPath runtime.
    pub runtime: &'a Runtime,
    /// Offset being evaluated
    pub offset: usize,
}

impl<'a> Context<'a> {
    /// Create a new context struct.
    #[inline]
    pub fn new(expression: &'a str, runtime: &'a Runtime) -> Context<'a> {
        Context {
            expression: expression,
            runtime: runtime,
            offset: 0,
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use super::ast::Ast;

    #[test]
    fn formats_expression_as_string_or_debug() {
        let expr = compile("foo | baz").unwrap();
        assert_eq!("foo | baz/foo | baz", format!("{}/{:?}", expr, expr));
    }

    #[test]
    fn implements_partial_eq() {
        let a = compile("@").unwrap();
        let b = compile("@").unwrap();
        assert!(a == b);
    }

    #[test]
    fn can_evaluate_jmespath_expression() {
        let expr = compile("foo.bar").unwrap();
        let var = Variable::from_json("{\"foo\":{\"bar\":true}}").unwrap();
        assert_eq!(Rcvar::new(Variable::Bool(true)), expr.search(var).unwrap());
    }

    #[test]
    fn can_get_expression_ast() {
        let expr = compile("foo").unwrap();
        assert_eq!(&Ast::Field {
                       offset: 0,
                       name: "foo".to_string(),
                   },
                   expr.as_ast());
    }

    #[test]
    fn test_creates_rcvar_from_tuple_serialization() {
        use super::ToJmespath;
        let t = (true, false);
        assert_eq!("[true,false]", t.to_jmespath().to_string());
    }
}
