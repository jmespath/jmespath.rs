//! This crate provides the `jmespath!` macro used to statically
//! compile JMESPath expressions.
//!
//! By statically compiling JMESPath expressions, you pay the cost of
//! parsing and compiling JMESPath expressions at compile time rather
//! than at runtime, and you can be sure that the expression is valid
//! if your program compiles.
//!
//! Note: This only works with a nightly compiler.
//!
//! ```
//! #![feature(plugin)]
//!
//! #![plugin(jmespath-macros)]
//! extern crate jmespath;
//!
//! fn main() {
//!     // Create our statically compiled expression. The build will fail
//!     // if the expression is invalid.
//!     let expr = jmespath!("foo.bar");
//!
//!     // Parse some JSON data into a JMESPath variable
//!     let json_str = "{\"foo\":{\"bar\":true}}";
//!     let data = jmespath::Variable::from_json(json_str).unwrap();
//!     let result = expr.search(data).unwrap();
//!     assert_eq!(true, result.as_boolean().unwrap());
//! }
//! ```

#![crate_type="dylib"]
#![feature(plugin_registrar, quote, rustc_private)]

extern crate syntax;
extern crate rustc;
extern crate rustc_plugin;

extern crate jmespath;

use syntax::ast;
use syntax::codemap;
use syntax::ext::base::{ExtCtxt, MacResult, MacEager, DummyResult};
use syntax::parse::token;
use syntax::print::pprust;
use syntax::tokenstream;
use syntax::fold::Folder;
use rustc_plugin::Registry;
use syntax::ptr::P;

use jmespath::{Variable, Rcvar};
use jmespath::ast::{Ast, Comparator};

#[plugin_registrar]
pub fn plugin_registrar(reg: &mut Registry) {
    reg.register_macro("jmespath", expand_jp);
}

fn expand_jp(cx: &mut ExtCtxt,
             sp: codemap::Span,
             tts: &[tokenstream::TokenTree])
             -> Box<MacResult+'static> {
    // Parse the arguments of the macro.
    let expression_str = match parse(cx, tts) {
        Some(e) => e,
        None => return DummyResult::any(sp),
    };

    // Parse the expression and show an error if needed.
    let ast = match jmespath::parse(&expression_str) {
        Ok(e) => e,
        Err(err) => {
            cx.span_err(sp, &format!("jmespath! error: {}", err));
            return DummyResult::any(sp);
        }
    };

    let jmespath_ast = generate_ast(cx, &ast);

    MacEager::expr(quote_expr!(cx, {
        use ::jmespath::ast::Ast;
        use ::jmespath::{Expression, DEFAULT_RUNTIME};
        Expression::new($expression_str, $jmespath_ast, &DEFAULT_RUNTIME)
    }))
}

/// Looks for a single string literal and returns it.
///
/// Based on rust-regex macro: https://github.com/rust-lang-nursery/regex
fn parse(cx: &mut ExtCtxt, tts: &[tokenstream::TokenTree]) -> Option<String> {
    let mut parser = cx.new_parser_from_tts(tts);
    if let Ok(expr) = parser.parse_expr() {
        let entry = cx.expander().fold_expr(expr);
        let expr = match entry.node {
            ast::ExprKind::Lit(ref lit) => {
                match lit.node {
                    ast::LitKind::Str(ref s, _) => s.to_string(),
                    _ => {
                        cx.span_err(entry.span, &format!(
                            "expected string literal but got `{}`",
                            pprust::lit_to_string(&**lit)));
                        return None
                    }
                }
            }
            _ => {
                cx.span_err(entry.span, &format!(
                    "expected string literal but got `{}`",
                    pprust::expr_to_string(&*entry)));
                return None
            }
        };
        if !parser.eat(&token::Eof) {
            cx.span_err(parser.span, "only one string literal allowed");
            return None;
        }
        Some(expr)
    } else {
        cx.parse_sess().span_diagnostic.err("failure parsing token tree");
        None
    }
}

/// Creates a Vec that contains a number of generated Ast elements.
fn generate_vec_ast(cx: &mut ExtCtxt, elements: &Vec<Ast>) -> P<ast::Expr> {
    // Creates the AST expressions necessary for pushing each node onto the Vec.
    let elements_ast = elements.iter()
        .fold(quote_expr!(cx, {}), |acc, element| {
            let element_expr = generate_ast(cx, &element);
            quote_expr!(cx, {
                $acc;
                nodes.push($element_expr);
            })
        });
    quote_expr!(cx, {
        let mut nodes = Vec::new();
        $elements_ast;
        nodes
    })
}

/// Creates the AST nodes for a Comparator.
fn generate_comparator_ast(cx: &mut ExtCtxt, comparator: &Comparator) -> P<ast::Expr> {
    match *comparator {
        Comparator::Equal => quote_expr!(cx, {::jmespath::ast::Comparator::Equal}),
        Comparator::NotEqual => quote_expr!(cx, {::jmespath::ast::Comparator::NotEqual}),
        Comparator::GreaterThan => quote_expr!(cx, {::jmespath::ast::Comparator::GreaterThan}),
        Comparator::GreaterThanEqual => {
            quote_expr!(cx, {::jmespath::ast::Comparator::GreaterThanEqual})
        },
        Comparator::LessThan => quote_expr!(cx, {::jmespath::ast::Comparator::LessThan}),
        Comparator::LessThanEqual => {
            quote_expr!(cx, {::jmespath::ast::Comparator::LessThanEqual})
        },
    }
}

/// Generates the Rust AST expression nodes for each JMESPath AST node.
fn generate_ast(cx: &mut ExtCtxt, ast: &Ast) -> P<ast::Expr> {
    use jmespath::ast::Ast::*;
    match *ast {
        Field { offset, ref name } => {
            quote_expr!(cx, Ast::Field {
                offset: $offset,
                name: $name.to_owned()
            })
        },
        Subexpr { offset, ref lhs, ref rhs } => {
            let left = generate_ast(cx, lhs);
            let right = generate_ast(cx, rhs);
            quote_expr!(cx, Ast::Subexpr {
                offset: $offset,
                lhs: Box::new($left),
                rhs: Box::new($right)
            })
        },
        Index { offset, idx } => {
            quote_expr!(cx, Ast::Index {
                offset: $offset,
                idx: $idx
            })
        },
        Condition { offset, ref predicate, ref then } => {
            let predicate = generate_ast(cx, &*predicate);
            let then = generate_ast(cx, then);
            quote_expr!(cx, Ast::Condition {
                offset: $offset,
                predicate: $predicate,
                then: $then
            })
        },
        Identity { offset } => {
            quote_expr!(cx, Ast::Identity {
                offset: $offset
            })
        },
        Expref { offset, ref ast } => {
            let inner = generate_ast(cx, ast);
            quote_expr!(cx, Ast::Expref {
                offset: $offset,
                ast: Box::new($inner)
            })
        },
        Flatten { offset, ref node } => {
            let inner = generate_ast(cx, node);
            quote_expr!(cx, Ast::Flatten {
                offset: $offset,
                node: Box::new($inner)
            })
        },
        Not { offset, ref node } => {
            let inner = generate_ast(cx, node);
            quote_expr!(cx, Ast::Not {
                offset: $offset,
                node: Box::new($inner)
            })
        },
        Projection { offset, ref lhs, ref rhs } => {
            let left = generate_ast(cx, lhs);
            let right = generate_ast(cx, rhs);
            quote_expr!(cx, Ast::Projection {
                offset: $offset,
                lhs: Box::new($left),
                rhs: Box::new($right)
            })
        },
        ObjectValues { offset, ref node } => {
            let inner = generate_ast(cx, node);
            quote_expr!(cx, Ast::ObjectValues {
                offset: $offset,
                node: Box::new($inner)
            })
        },
        And { offset, ref lhs, ref rhs } => {
            let left = generate_ast(cx, lhs);
            let right = generate_ast(cx, rhs);
            quote_expr!(cx, Ast::And {
                offset: $offset,
                lhs: Box::new($left),
                rhs: Box::new($right)
            })
        },
        Or { offset, ref lhs, ref rhs } => {
            let left = generate_ast(cx, lhs);
            let right = generate_ast(cx, rhs);
            quote_expr!(cx, Ast::Or {
                offset: $offset,
                lhs: Box::new($left),
                rhs: Box::new($right)
            })
        },
        Slice { offset, start, stop, step } => {
            let start = generate_slice_option_ast(cx, start);
            let stop = generate_slice_option_ast(cx, stop);
            quote_expr!(cx, Ast::Slice {
                offset: $offset,
                start: $start,
                stop: $stop,
                step: $step
            })
        },
        Comparison { offset, ref comparator, ref lhs, ref rhs } => {
            let left = generate_ast(cx, lhs);
            let right = generate_ast(cx, rhs);
            let comparator_ast = generate_comparator_ast(cx, comparator);
            quote_expr!(cx, Ast::Comparison {
                offset: $offset,
                comparator: $comparator_ast,
                lhs: Box::new($left),
                rhs: Box::new($right)
            })
        },
        Function { offset, ref name, ref args } => {
            let elements_ast = generate_vec_ast(cx, args);
            quote_expr!(cx, {
                Ast::Function {
                    offset: $offset,
                    name: $name.to_owned(),
                    args: $elements_ast,
                }
            })
        },
        MultiList { offset, ref elements } => {
            let elements_ast = generate_vec_ast(cx, elements);
            quote_expr!(cx, {
                Ast::MultiList {
                    offset: $offset,
                    elements: $elements_ast,
                }
            })
        },
        MultiHash { offset, ref elements } => {
            // Create the AST nodes for inserting each key value pair into the MultiHash map.
            let elements_ast = elements.iter()
                .fold(quote_expr!(cx, {}), |acc, element| {
                    let element_key = element.key.to_owned();
                    let element_expr = generate_ast(cx, &element.value);
                    quote_expr!(cx, {
                        $acc;
                        nodes.push(::jmespath::ast::KeyValuePair {
                            key: $element_key.to_owned(),
                            value: $element_expr,
                        });
                    })
                });
            quote_expr!(cx, {
                Ast::MultiHash {
                    offset: $offset,
                    elements: {
                        let mut nodes = Vec::new();
                        $elements_ast;
                        nodes
                    },
                }
            })
        },
        Literal { offset, ref value } => {
            let value_ast = generate_var_ast(cx, value);
            quote_expr!(cx, {
                Ast::Literal {
                    offset: $offset,
                    value: ::std::rc::Rc::new($value_ast),
                }
            })
        },
    }
}

/// Generate the AST expression for creating a JMESPath variable.
///
/// JMESPath variables are used in Literal nodes.
fn generate_var_ast(cx: &mut ExtCtxt, var: &Rcvar) -> P<ast::Expr> {
    match **var {
        Variable::Null => quote_expr!(cx, ::jmespath::Variable::Null),
        Variable::Bool(b) => quote_expr!(cx, ::jmespath::Variable::Bool($b)),
        Variable::String(ref s) => quote_expr!(cx, ::jmespath::Variable::String($s.to_owned())),
        Variable::Number(n) => {
            // f64 does not implement to_tokens, so we must parse a float from a string.
            let float_str = n.to_string();
            quote_expr!(cx, ::jmespath::Variable::Number($float_str.parse().unwrap()))
        },
        Variable::Expref(ref node) => {
            let node_ast = generate_ast(cx, node);
            quote_expr!(cx, ::jmespath::Variable::Expref($node_ast))
        },
        Variable::Array(ref array) => {
            // Create the AST nodes for inserting each value into the array.
            let elements_ast = array.iter()
                .fold(quote_expr!(cx, {}), |acc, element| {
                    let element_expr = generate_var_ast(cx, &element);
                    quote_expr!(cx, {
                        $acc;
                        nodes.push(::std::rc::Rc::new($element_expr));
                    })
                });
            quote_expr!(cx, ::jmespath::Variable::Array({
                let mut nodes = Vec::new();
                $elements_ast;
                nodes
            }))
        },
        Variable::Object(ref map) => {
            // Create the AST nodes for inserting each key value pair into the BTreeMap.
            let elements_ast = map.keys()
                .fold(quote_expr!(cx, {}), |acc, key| {
                    let element_expr = generate_var_ast(cx, map.get(key).unwrap());
                    quote_expr!(cx, {
                        $acc;
                        map.insert($key.to_owned(), ::std::rc::Rc::new($element_expr));
                    })
                });
            quote_expr!(cx, ::jmespath::Variable::Object({
                let mut map = ::std::collections::BTreeMap::new();
                $elements_ast;
                map
            }))
        },
    }
}

fn generate_slice_option_ast(cx: &mut ExtCtxt, value: Option<i32>) -> P<ast::Expr> {
    match value {
        Some(v) => quote_expr!(cx, Some($v)),
        None => quote_expr!(cx, None)
    }
}
