//! Rust implementation of JMESPath.
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

pub use parser::{parse, Parser, ParseResult, ParseError};
pub use lexer::{tokenize, Token, Lexer};
pub use ast::{Ast, KeyValuePair, Comparator};

mod ast;
mod compiler;
mod lexer;
mod parser;
mod vm;
