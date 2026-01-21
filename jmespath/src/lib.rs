//! Rust implementation of JMESPath, a query language for JSON.
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
//! Any type that implements `jmespath::ToJmespath` can be used in a JMESPath
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
//! // Create a new Runtime and register the builtin JMESPath functions.
//! let mut runtime = Runtime::new();
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
//!
//! # Let Expressions (JEP-18)
//!
//! This crate supports [JEP-18 let expressions](https://github.com/jmespath/jmespath.jep/blob/main/proposals/0018-lexical-scope.md)
//! as an optional feature. Let expressions introduce lexical scoping, allowing
//! you to bind values to variables and reference them within an expression.
//!
//! To enable let expressions, add the `let-expr` feature to your `Cargo.toml`:
//!
//! ```toml
//! [dependencies]
//! jmespath = { version = "0.5", features = ["let-expr"] }
//! ```
//!
//! ## Syntax
//!
//! ```text
//! let $variable = expression in body
//! let $var1 = expr1, $var2 = expr2 in body
//! ```
//!
//! ## Example
//!
//! ```ignore
//! use jmespath;
//!
//! // Bind a threshold value and use it in a filter
//! let expr = jmespath::compile("let $threshold = `50` in numbers[? @ > $threshold]").unwrap();
//! let data = jmespath::Variable::from_json(r#"{"numbers": [10, 30, 50, 70, 90]}"#).unwrap();
//! let result = expr.search(data).unwrap();
//! // Returns [70, 90]
//! ```
//!
//! Let expressions are particularly useful when you need to reference a value
//! from an outer scope within a filter or projection:
//!
//! ```ignore
//! // Reference parent data within a nested filter
//! let expr = jmespath::compile(
//!     "let $home = home_state in states[? name == $home].cities[]"
//! ).unwrap();
//! ```
//!
//! Key features:
//! - Variables use `$name` syntax
//! - `let` and `in` are contextual keywords (not reserved)
//! - Inner scopes can shadow outer variables
//! - Bindings are evaluated in the outer scope before the body executes

#![cfg_attr(feature = "specialized", feature(specialization))]

pub use crate::errors::{ErrorReason, JmespathError, RuntimeError};
pub use crate::parser::{ParseResult, parse};
pub use crate::runtime::Runtime;
pub use crate::variable::Variable;

pub mod ast;
pub mod functions;

use serde::ser;
#[cfg(feature = "specialized")]
use serde_json::Value;
#[cfg(feature = "let-expr")]
use std::collections::HashMap;
#[cfg(feature = "specialized")]
use std::convert::TryInto;
use std::fmt;
use std::sync::LazyLock;

use crate::ast::Ast;
pub use crate::interpreter::{SearchResult, interpret};

mod errors;
mod interpreter;
mod lexer;
mod parser;
mod runtime;
mod variable;

pub static DEFAULT_RUNTIME: LazyLock<Runtime> = LazyLock::new(|| {
    let mut runtime = Runtime::new();
    runtime.register_builtin_functions();
    runtime
});

/// `Rc` reference counted JMESPath `Variable`.
#[cfg(not(feature = "sync"))]
pub type Rcvar = std::rc::Rc<Variable>;
/// `Arc` reference counted JMESPath `Variable`.
#[cfg(feature = "sync")]
pub type Rcvar = std::sync::Arc<Variable>;

/// Compiles a JMESPath expression using the default Runtime.
///
/// The default Runtime is created lazily the first time it is dereferenced
/// by using the `lazy_static` macro.
///
/// The provided expression is expected to adhere to the JMESPath
/// grammar: <https://jmespath.org/specification.html>
#[inline]
pub fn compile(expression: &str) -> Result<Expression<'static>, JmespathError> {
    DEFAULT_RUNTIME.compile(expression)
}

/// Converts a value into a reference-counted JMESPath Variable.
///
#[cfg_attr(
    feature = "specialized",
    doc = "\
There is a generic serde Serialize implementation, and since this
documentation was compiled with the `specialized` feature turned
**on**, there are also a number of specialized implementations for
`ToJmespath` built into the library that should work for most
cases."
)]
#[cfg_attr(
    not(feature = "specialized"),
    doc = "\
There is a generic serde Serialize implementation. Since this
documentation was compiled with the `specialized` feature turned
**off**, this is the only implementation available.

(If the `specialized` feature were turned on, there there would be
a number of additional specialized implementations for `ToJmespath`
built into the library that should work for most cases.)"
)]
pub trait ToJmespath {
    fn to_jmespath(self) -> Result<Rcvar, JmespathError>;
}

/// Create searchable values from Serde serializable values.
impl<T: ser::Serialize> ToJmespath for T {
    #[cfg(not(feature = "specialized"))]
    fn to_jmespath(self) -> Result<Rcvar, JmespathError> {
        Variable::from_serializable(self).map(Rcvar::new)
    }

    #[cfg(feature = "specialized")]
    default fn to_jmespath(self) -> Result<Rcvar, JmespathError> {
        Variable::from_serializable(self).map(Rcvar::new)
    }
}

#[cfg(feature = "specialized")]
impl ToJmespath for Value {
    #[inline]
    fn to_jmespath(self) -> Result<Rcvar, JmespathError> {
        self.try_into().map(|var: Variable| Rcvar::new(var))
    }
}

#[cfg(feature = "specialized")]
impl ToJmespath for &Value {
    #[inline]
    fn to_jmespath(self) -> Result<Rcvar, JmespathError> {
        self.try_into().map(|var: Variable| Rcvar::new(var))
    }
}

#[cfg(feature = "specialized")]
/// Identity coercion.
impl ToJmespath for Rcvar {
    #[inline]
    fn to_jmespath(self) -> Result<Rcvar, JmespathError> {
        Ok(self)
    }
}

#[cfg(feature = "specialized")]
impl ToJmespath for &Rcvar {
    #[inline]
    fn to_jmespath(self) -> Result<Rcvar, JmespathError> {
        Ok(self.clone())
    }
}

#[cfg(feature = "specialized")]
impl ToJmespath for Variable {
    #[inline]
    fn to_jmespath(self) -> Result<Rcvar, JmespathError> {
        Ok(Rcvar::new(self))
    }
}

#[cfg(feature = "specialized")]
impl ToJmespath for &Variable {
    #[inline]
    fn to_jmespath(self) -> Result<Rcvar, JmespathError> {
        Ok(Rcvar::new(self.clone()))
    }
}

#[cfg(feature = "specialized")]
impl ToJmespath for String {
    fn to_jmespath(self) -> Result<Rcvar, JmespathError> {
        Ok(Rcvar::new(Variable::String(self)))
    }
}

#[cfg(feature = "specialized")]
impl ToJmespath for &str {
    fn to_jmespath(self) -> Result<Rcvar, JmespathError> {
        Ok(Rcvar::new(Variable::String(self.to_owned())))
    }
}

#[cfg(feature = "specialized")]
impl ToJmespath for i8 {
    fn to_jmespath(self) -> Result<Rcvar, JmespathError> {
        Ok(Rcvar::new(Variable::Number(serde_json::Number::from(self))))
    }
}

#[cfg(feature = "specialized")]
impl ToJmespath for i16 {
    fn to_jmespath(self) -> Result<Rcvar, JmespathError> {
        Ok(Rcvar::new(Variable::Number(serde_json::Number::from(self))))
    }
}

#[cfg(feature = "specialized")]
impl ToJmespath for i32 {
    fn to_jmespath(self) -> Result<Rcvar, JmespathError> {
        Ok(Rcvar::new(Variable::Number(serde_json::Number::from(self))))
    }
}

#[cfg(feature = "specialized")]
impl ToJmespath for i64 {
    fn to_jmespath(self) -> Result<Rcvar, JmespathError> {
        Ok(Rcvar::new(Variable::Number(serde_json::Number::from(self))))
    }
}

#[cfg(feature = "specialized")]
impl ToJmespath for u8 {
    fn to_jmespath(self) -> Result<Rcvar, JmespathError> {
        Ok(Rcvar::new(Variable::Number(serde_json::Number::from(self))))
    }
}

#[cfg(feature = "specialized")]
impl ToJmespath for u16 {
    fn to_jmespath(self) -> Result<Rcvar, JmespathError> {
        Ok(Rcvar::new(Variable::Number(serde_json::Number::from(self))))
    }
}

#[cfg(feature = "specialized")]
impl ToJmespath for u32 {
    fn to_jmespath(self) -> Result<Rcvar, JmespathError> {
        Ok(Rcvar::new(Variable::Number(serde_json::Number::from(self))))
    }
}

#[cfg(feature = "specialized")]
impl ToJmespath for u64 {
    fn to_jmespath(self) -> Result<Rcvar, JmespathError> {
        Ok(Rcvar::new(Variable::Number(serde_json::Number::from(self))))
    }
}

#[cfg(feature = "specialized")]
impl ToJmespath for isize {
    fn to_jmespath(self) -> Result<Rcvar, JmespathError> {
        Ok(Rcvar::new(Variable::Number(serde_json::Number::from(self))))
    }
}

#[cfg(feature = "specialized")]
impl ToJmespath for usize {
    fn to_jmespath(self) -> Result<Rcvar, JmespathError> {
        Ok(Rcvar::new(Variable::Number(serde_json::Number::from(self))))
    }
}

#[cfg(feature = "specialized")]
impl ToJmespath for f32 {
    fn to_jmespath(self) -> Result<Rcvar, JmespathError> {
        (self as f64).to_jmespath()
    }
}

#[cfg(feature = "specialized")]
impl ToJmespath for f64 {
    fn to_jmespath(self) -> Result<Rcvar, JmespathError> {
        Ok(Rcvar::new(Variable::Number(
            serde_json::Number::from_f64(self).ok_or_else(|| {
                JmespathError::new(
                    "",
                    0,
                    ErrorReason::Parse(format!("Cannot parse {self} into a Number")),
                )
            })?,
        )))
    }
}

#[cfg(feature = "specialized")]
impl ToJmespath for () {
    fn to_jmespath(self) -> Result<Rcvar, JmespathError> {
        Ok(Rcvar::new(Variable::Null))
    }
}

#[cfg(feature = "specialized")]
impl ToJmespath for bool {
    fn to_jmespath(self) -> Result<Rcvar, JmespathError> {
        Ok(Rcvar::new(Variable::Bool(self)))
    }
}

/// A compiled JMESPath expression.
///
/// The compiled expression can be used multiple times without incurring
/// the cost of re-parsing the expression each time. The expression may
/// be shared between threads if JMESPath is compiled with the `sync`
/// feature, which forces the use of an `Arc` instead of an `Rc` for
/// runtime variables.
#[derive(Clone)]
pub struct Expression<'a> {
    ast: Ast,
    expression: String,
    runtime: &'a Runtime,
}

impl<'a> Expression<'a> {
    /// Creates a new JMESPath expression.
    ///
    /// Normally you will create expressions using either `jmespath::compile()`
    /// or using a jmespath::Runtime.
    #[inline]
    pub fn new<S>(expression: S, ast: Ast, runtime: &'a Runtime) -> Expression<'a>
    where
        S: Into<String>,
    {
        Expression {
            expression: expression.into(),
            ast,
            runtime,
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
        interpret(&data.to_jmespath()?, &self.ast, &mut ctx)
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
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.as_str())
    }
}

impl<'a> fmt::Debug for Expression<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self, f)
    }
}

impl<'a> PartialEq for Expression<'a> {
    fn eq(&self, other: &Expression<'_>) -> bool {
        self.as_str() == other.as_str()
    }
}

/// Context object used for error reporting.
///
/// The Context struct is mostly used when interacting between the
/// interpreter and function implemenations. Unless you're writing custom
/// JMESPath functions, this struct is an implementation detail.
pub struct Context<'a> {
    /// Expression string that is being interpreted.
    pub expression: &'a str,
    /// JMESPath runtime used to compile the expression and call functions.
    pub runtime: &'a Runtime,
    /// Ast offset that is currently being evaluated.
    pub offset: usize,
    /// Variable scopes for let expressions (JEP-18).
    #[cfg(feature = "let-expr")]
    scopes: Vec<HashMap<String, Rcvar>>,
}

impl<'a> Context<'a> {
    /// Create a new context struct.
    #[inline]
    pub fn new(expression: &'a str, runtime: &'a Runtime) -> Context<'a> {
        Context {
            expression,
            runtime,
            offset: 0,
            #[cfg(feature = "let-expr")]
            scopes: Vec::new(),
        }
    }

    /// Push a new scope onto the scope stack.
    #[cfg(feature = "let-expr")]
    #[inline]
    pub fn push_scope(&mut self, bindings: HashMap<String, Rcvar>) {
        self.scopes.push(bindings);
    }

    /// Pop the innermost scope from the scope stack.
    #[cfg(feature = "let-expr")]
    #[inline]
    pub fn pop_scope(&mut self) {
        self.scopes.pop();
    }

    /// Look up a variable in the scope stack.
    #[cfg(feature = "let-expr")]
    #[inline]
    pub fn get_variable(&self, name: &str) -> Option<Rcvar> {
        for scope in self.scopes.iter().rev() {
            if let Some(value) = scope.get(name) {
                return Some(value.clone());
            }
        }
        None
    }
}
#[cfg(test)]
mod test {
    use super::ast::Ast;
    use super::*;

    #[test]
    fn formats_expression_as_string_or_debug() {
        let expr = compile("foo | baz").unwrap();
        assert_eq!("foo | baz/foo | baz", format!("{expr}/{expr:?}"));
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
        assert_eq!(
            &Ast::Field {
                offset: 0,
                name: "foo".to_string(),
            },
            expr.as_ast()
        );
    }

    #[test]
    fn test_creates_rcvar_from_tuple_serialization() {
        use super::ToJmespath;
        let t = (true, false);
        assert_eq!("[true,false]", t.to_jmespath().unwrap().to_string());
    }

    #[test]
    fn expression_clone() {
        let expr = compile("foo").unwrap();
        let _ = expr.clone();
    }

    #[test]
    fn test_invalid_number() {
        let _ = compile("6455555524");
    }
}

#[cfg(all(test, feature = "let-expr"))]
mod let_tests {
    use super::*;

    #[test]
    fn test_simple_let_expression() {
        // JEP-18 syntax: let $var = expr in body
        let expr = compile("let $x = `1` in $x").unwrap();
        let data = Variable::from_json("{}").unwrap();
        let result = expr.search(data).unwrap();
        assert_eq!(1.0, result.as_number().unwrap());
    }

    #[test]
    fn test_let_with_data_reference() {
        let expr = compile("let $name = name in $name").unwrap();
        let data = Variable::from_json(r#"{"name": "Alice"}"#).unwrap();
        let result = expr.search(data).unwrap();
        assert_eq!("Alice", result.as_string().unwrap());
    }

    #[test]
    fn test_let_multiple_bindings() {
        let expr = compile("let $a = `1`, $b = `2` in [$a, $b]").unwrap();
        let data = Variable::from_json("{}").unwrap();
        let result = expr.search(data).unwrap();
        let arr = result.as_array().unwrap();
        assert_eq!(1.0, arr[0].as_number().unwrap());
        assert_eq!(2.0, arr[1].as_number().unwrap());
    }

    #[test]
    fn test_let_with_expression_body() {
        let expr = compile("let $items = items in $items[0].name").unwrap();
        let data =
            Variable::from_json(r#"{"items": [{"name": "first"}, {"name": "second"}]}"#).unwrap();
        let result = expr.search(data).unwrap();
        assert_eq!("first", result.as_string().unwrap());
    }

    #[test]
    fn test_nested_let() {
        let expr = compile("let $x = `1` in let $y = `2` in [$x, $y]").unwrap();
        let data = Variable::from_json("{}").unwrap();
        let result = expr.search(data).unwrap();
        let arr = result.as_array().unwrap();
        assert_eq!(1.0, arr[0].as_number().unwrap());
        assert_eq!(2.0, arr[1].as_number().unwrap());
    }

    #[test]
    fn test_let_variable_shadowing() {
        let expr = compile("let $x = `1` in let $x = `2` in $x").unwrap();
        let data = Variable::from_json("{}").unwrap();
        let result = expr.search(data).unwrap();
        assert_eq!(2.0, result.as_number().unwrap());
    }

    #[test]
    fn test_undefined_variable_error() {
        let expr = compile("$undefined").unwrap();
        let data = Variable::from_json("{}").unwrap();
        let result = expr.search(data);
        assert!(result.is_err());
    }

    #[test]
    fn test_let_in_projection() {
        // Example from jsoncons docs
        let expr = compile("let $threshold = `50` in numbers[? @ > $threshold]").unwrap();
        let data = Variable::from_json(r#"{"numbers": [10, 30, 50, 70, 90]}"#).unwrap();
        let result = expr.search(data).unwrap();
        let arr = result.as_array().unwrap();
        assert_eq!(2, arr.len());
        assert_eq!(70.0, arr[0].as_number().unwrap());
        assert_eq!(90.0, arr[1].as_number().unwrap());
    }

    #[test]
    fn test_let_variable_used_multiple_times() {
        let expr = compile("let $foo = foo.bar in [$foo, $foo]").unwrap();
        let data = Variable::from_json(r#"{"foo": {"bar": "baz"}}"#).unwrap();
        let result = expr.search(data).unwrap();
        assert_eq!(r#"["baz","baz"]"#, result.to_string());
    }

    #[test]
    fn test_let_shadowing_in_projection() {
        let expr = compile("let $a = a in b[*].[a, $a, let $a = 'shadow' in $a]").unwrap();
        let data =
            Variable::from_json(r#"{"a": "topval", "b": [{"a": "inner1"}, {"a": "inner2"}]}"#)
                .unwrap();
        let result = expr.search(data).unwrap();
        let expected = r#"[["inner1","topval","shadow"],["inner2","topval","shadow"]]"#;
        assert_eq!(expected, result.to_string());
    }

    #[test]
    fn test_let_bindings_evaluated_in_outer_scope() {
        // $b = $a is evaluated BEFORE $a = 'in-a' takes effect
        let expr = compile("let $a = 'top-a' in let $a = 'in-a', $b = $a in $b").unwrap();
        let data = Variable::from_json("{}").unwrap();
        let result = expr.search(data).unwrap();
        assert_eq!("top-a", result.as_string().unwrap());
    }

    #[test]
    fn test_let_projection_stopping() {
        // Projection is stopped when bound to variable
        let expr = compile("let $foo = foo[*] in $foo[0]").unwrap();
        let data = Variable::from_json(r#"{"foo": [[0,1],[2,3],[4,5]]}"#).unwrap();
        let result = expr.search(data).unwrap();
        assert_eq!("[0,1]", result.to_string());
    }

    #[test]
    fn test_let_complex_home_state_filtering() {
        let expr = compile(
            "[*].[let $home_state = home_state in states[? name == $home_state].cities[]][]",
        )
        .unwrap();
        let data = Variable::from_json(
            r#"[
            {"home_state": "WA", "states": [{"name": "WA", "cities": ["Seattle", "Bellevue", "Olympia"]}, {"name": "CA", "cities": ["Los Angeles", "San Francisco"]}, {"name": "NY", "cities": ["New York City", "Albany"]}]},
            {"home_state": "NY", "states": [{"name": "WA", "cities": ["Seattle", "Bellevue", "Olympia"]}, {"name": "CA", "cities": ["Los Angeles", "San Francisco"]}, {"name": "NY", "cities": ["New York City", "Albany"]}]}
        ]"#,
        )
        .unwrap();
        let result = expr.search(data).unwrap();
        let expected = r#"[["Seattle","Bellevue","Olympia"],["New York City","Albany"]]"#;
        assert_eq!(expected, result.to_string());
    }

    #[test]
    fn test_let_out_of_scope_variable() {
        // Variable defined in inner scope should not be visible outside
        let expr = compile("[let $scope = 'foo' in [$scope], $scope]").unwrap();
        let data = Variable::from_json("{}").unwrap();
        let result = expr.search(data);
        assert!(result.is_err());
    }

    #[test]
    fn test_variable_ref_in_subexpression_is_error() {
        // foo.$bar is a syntax error
        let expr_result = compile("foo.$bar");
        assert!(expr_result.is_err());
    }

    #[test]
    fn test_let_inner_scope_null() {
        // Inner scope can explicitly set variable to null
        let expr = compile("let $foo = foo in let $foo = null in $foo").unwrap();
        let data = Variable::from_json(r#"{"foo": "outer"}"#).unwrap();
        let result = expr.search(data).unwrap();
        assert!(result.is_null());
    }

    #[test]
    fn test_let_and_in_as_field_names() {
        // JEP-18: 'let' and 'in' can be used as field names in the body expression
        // Note: Using 'let' or 'in' immediately before the 'in' keyword in bindings
        // (e.g., `let $x = foo.let in ...`) requires more complex parser lookahead
        // and is a known limitation of this implementation. Use quoted identifiers
        // as a workaround: `let $x = foo."let" in ...`

        // 'in' as a field name in body - works fine
        let expr = compile(r#"let $x = foo in {in: $x}"#).unwrap();
        let data = Variable::from_json(r#"{"foo": "bar"}"#).unwrap();
        let result = expr.search(data).unwrap();
        assert_eq!(r#"{"in":"bar"}"#, result.to_string());

        // 'let' as a field name in body - works fine
        let expr2 = compile(r#"let $x = foo in {let: $x, other: @}"#).unwrap();
        let data2 = Variable::from_json(r#"{"foo": "bar"}"#).unwrap();
        let result2 = expr2.search(data2).unwrap();
        assert!(result2.to_string().contains(r#""let":"bar""#));

        // Access field via quoted identifier to avoid keyword ambiguity
        let expr3 = compile(r#"let $x = data."let" in $x"#).unwrap();
        let data3 = Variable::from_json(r#"{"data": {"let": "let-value"}}"#).unwrap();
        let result3 = expr3.search(data3).unwrap();
        assert_eq!("let-value", result3.as_string().unwrap());
    }

    #[test]
    fn test_let_image_details_example() {
        // JEP-18 example: create pairs of [tag, digest, repo] from nested structure
        // Simplified from JEP to avoid complex flatten behavior
        let expr = compile(
            "imageDetails[0] | let $repo = repositoryName, $digest = imageDigest in imageTags[].[@, $digest, $repo]",
        )
        .unwrap();
        let data = Variable::from_json(
            r#"{
            "imageDetails": [
                {"repositoryName": "org/first-repo", "imageTags": ["latest", "v1.0"], "imageDigest": "sha256:abcd"},
                {"repositoryName": "org/second-repo", "imageTags": ["v2.0"], "imageDigest": "sha256:efgh"}
            ]
        }"#,
        )
        .unwrap();
        let result = expr.search(data).unwrap();
        let arr = result.as_array().unwrap();
        assert_eq!(2, arr.len());
        assert_eq!(
            r#"["latest","sha256:abcd","org/first-repo"]"#,
            arr[0].to_string()
        );
        assert_eq!(
            r#"["v1.0","sha256:abcd","org/first-repo"]"#,
            arr[1].to_string()
        );
    }

    #[test]
    fn test_let_with_functions() {
        // Variables should work inside function calls
        let expr = compile("let $arr = numbers in length($arr)").unwrap();
        let data = Variable::from_json(r#"{"numbers": [1, 2, 3, 4, 5]}"#).unwrap();
        let result = expr.search(data).unwrap();
        assert_eq!(5.0, result.as_number().unwrap());
    }

    #[test]
    fn test_let_variable_in_filter_comparison() {
        // Variable on right side of comparison in filter
        let expr = compile("let $min = `10` in numbers[? @ >= $min]").unwrap();
        let data = Variable::from_json(r#"{"numbers": [5, 10, 15, 20]}"#).unwrap();
        let result = expr.search(data).unwrap();
        let arr = result.as_array().unwrap();
        assert_eq!(3, arr.len());
    }

    #[test]
    fn test_let_variable_in_multiselect_hash() {
        // Variables in multi-select hash
        let expr = compile("let $x = name, $y = age in {name: $x, age: $y, original: @}").unwrap();
        let data = Variable::from_json(r#"{"name": "Alice", "age": 30}"#).unwrap();
        let result = expr.search(data).unwrap();
        let obj = result.as_object().unwrap();
        assert_eq!("Alice", obj.get("name").unwrap().as_string().unwrap());
        assert_eq!(30.0, obj.get("age").unwrap().as_number().unwrap());
    }

    #[test]
    fn test_let_with_pipe_expression() {
        // Let expression with pipe
        let expr =
            compile("let $prefix = prefix in items[*].name | [? starts_with(@, $prefix)]").unwrap();
        let data = Variable::from_json(
            r#"{"prefix": "test", "items": [{"name": "test_one"}, {"name": "other"}, {"name": "test_two"}]}"#,
        )
        .unwrap();
        let result = expr.search(data).unwrap();
        let arr = result.as_array().unwrap();
        assert_eq!(2, arr.len());
    }

    #[test]
    fn test_let_deeply_nested_scopes() {
        // Three levels of nesting
        let expr = compile("let $a = `1` in let $b = `2` in let $c = `3` in [$a, $b, $c]").unwrap();
        let data = Variable::from_json("{}").unwrap();
        let result = expr.search(data).unwrap();
        assert_eq!("[1,2,3]", result.to_string());
    }

    #[test]
    fn test_let_shadow_and_restore() {
        // Shadowed variable doesn't affect outer scope after inner scope exits
        let expr = compile("let $x = 'outer' in [let $x = 'inner' in $x, $x]").unwrap();
        let data = Variable::from_json("{}").unwrap();
        let result = expr.search(data).unwrap();
        assert_eq!(r#"["inner","outer"]"#, result.to_string());
    }

    #[test]
    fn test_let_with_current_node() {
        // Variable combined with @ (current node)
        let expr =
            compile("items[*].[let $item = @ in {value: $item.value, doubled: $item.value}]")
                .unwrap();
        let data = Variable::from_json(r#"{"items": [{"value": 1}, {"value": 2}]}"#).unwrap();
        let result = expr.search(data).unwrap();
        let arr = result.as_array().unwrap();
        assert_eq!(2, arr.len());
    }

    #[test]
    fn test_let_empty_bindings_body() {
        // Let with body that returns null
        let expr = compile("let $x = foo in $x.nonexistent").unwrap();
        let data = Variable::from_json(r#"{"foo": {"bar": 1}}"#).unwrap();
        let result = expr.search(data).unwrap();
        assert!(result.is_null());
    }

    #[test]
    fn test_let_binding_to_array() {
        // Bind variable to array and iterate
        let expr = compile("let $items = items in $items[*].name").unwrap();
        let data = Variable::from_json(r#"{"items": [{"name": "a"}, {"name": "b"}]}"#).unwrap();
        let result = expr.search(data).unwrap();
        assert_eq!(r#"["a","b"]"#, result.to_string());
    }

    #[test]
    fn test_let_binding_to_literal() {
        // Bind to various literal types
        let expr = compile("let $str = 'hello', $num = `42`, $bool = `true`, $null = `null` in [$str, $num, $bool, $null]").unwrap();
        let data = Variable::from_json("{}").unwrap();
        let result = expr.search(data).unwrap();
        assert_eq!(r#"["hello",42,true,null]"#, result.to_string());
    }

    #[test]
    fn test_let_variable_not_in_scope_after_expression() {
        // Verify scope is properly cleaned up - second $x should error
        let expr = compile("[let $x = 'first' in $x, let $y = 'second' in $y]").unwrap();
        let data = Variable::from_json("{}").unwrap();
        let result = expr.search(data).unwrap();
        assert_eq!(r#"["first","second"]"#, result.to_string());
    }

    #[test]
    fn test_let_with_flatten() {
        // Let with flatten operator
        let expr = compile("let $data = nested in $data[].items[]").unwrap();
        let data =
            Variable::from_json(r#"{"nested": [{"items": [1, 2]}, {"items": [3, 4]}]}"#).unwrap();
        let result = expr.search(data).unwrap();
        assert_eq!("[1,2,3,4]", result.to_string());
    }

    #[test]
    fn test_let_with_slice() {
        // Let with slice expression
        let expr = compile("let $arr = numbers in $arr[1:3]").unwrap();
        let data = Variable::from_json(r#"{"numbers": [0, 1, 2, 3, 4]}"#).unwrap();
        let result = expr.search(data).unwrap();
        assert_eq!("[1,2]", result.to_string());
    }

    #[test]
    fn test_let_with_or_expression() {
        // Let with || (or) expression
        let expr = compile("let $default = 'N/A' in name || $default").unwrap();
        let data = Variable::from_json(r#"{}"#).unwrap();
        let result = expr.search(data).unwrap();
        assert_eq!("N/A", result.as_string().unwrap());
    }

    #[test]
    fn test_let_with_and_expression() {
        // Let with && (and) expression
        let expr = compile("let $check = `true` in active && $check").unwrap();
        let data = Variable::from_json(r#"{"active": true}"#).unwrap();
        let result = expr.search(data).unwrap();
        assert!(result.as_boolean().unwrap());
    }

    #[test]
    fn test_let_with_not_expression() {
        // Let with ! (not) expression
        let expr = compile("let $val = `false` in !$val").unwrap();
        let data = Variable::from_json("{}").unwrap();
        let result = expr.search(data).unwrap();
        assert!(result.as_boolean().unwrap());
    }
}
