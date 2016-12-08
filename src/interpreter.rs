//! Interprets JMESPath expressions

extern crate serde;

use std::rc::Rc;
use std::collections::BTreeMap;

use super::{RcVar, Error, ErrorReason, RuntimeError};
use super::Context;
use super::ast::Ast;
use super::variable::Variable;

pub type SearchResult = Result<RcVar, Error>;

/// Interprets the given data using an AST node.
pub fn interpret(data: &RcVar, node: &Ast, ctx: &mut Context) -> SearchResult {
    match *node {
        Ast::Subexpr { ref lhs, ref rhs, .. } => {
            let left_result = try!(interpret(data, lhs, ctx));
            interpret(&left_result, rhs, ctx)
        },
        Ast::Field { ref name, .. } => Ok(data.get_field(name)),
        Ast::Identity { .. } => Ok(data.clone()),
        Ast::Literal { ref value, .. } => Ok(Rc::new(Variable::from(value))),
        Ast::Index { idx, .. } => {
            if idx >= 0 {
                Ok(data.get_index(idx as usize))
            } else {
                Ok(data.get_negative_index((-1 * idx) as usize))
            }
        },
        Ast::Or { ref lhs, ref rhs, .. } => {
            let left = try!(interpret(data, lhs, ctx));
            if left.is_truthy() {
                Ok(left)
            } else {
                interpret(data, rhs, ctx)
            }
        },
        Ast::And { ref lhs, ref rhs, .. } => {
            let left = try!(interpret(data, lhs, ctx));
            if !left.is_truthy() {
                Ok(left)
            } else {
                interpret(data, rhs, ctx)
            }
        },
        Ast::Not { ref node, .. } => {
            let result = try!(interpret(data, node, ctx));
            Ok(Rc::new(Variable::Bool(!result.is_truthy())))
        },
        // Returns the resut of RHS if cond yields truthy value.
        Ast::Condition { ref predicate, ref then, .. } => {
            let cond_result = try!(interpret(data, predicate, ctx));
            if cond_result.is_truthy() {
                interpret(data, then, ctx)
            } else {
                Ok(Rc::new(Variable::Null))
            }
        },
        Ast::Comparison { ref comparator, ref lhs, ref rhs, .. } => {
            let left = try!(interpret(data, lhs, ctx));
            let right = try!(interpret(data, rhs, ctx));
            Ok(left.compare(comparator, &*right)
                .map_or(Rc::new(Variable::Null), |result| Rc::new(Variable::Bool(result))))
        },
        // Converts an object into a JSON array of its values.
        Ast::ObjectValues { ref node, .. } => {
            let subject = try!(interpret(data, node, ctx));
            match *subject {
                Variable::Object(ref v) => {
                    Ok(Rc::new(Variable::Array(v.values().cloned().collect::<Vec<RcVar>>())))
                },
                _ => Ok(Rc::new(Variable::Null))
            }
        },
        // Passes the results of lhs into rhs if lhs yields an array and
        // each node of lhs that passes through rhs yields a non-null value.
        Ast::Projection { ref lhs, ref rhs, .. } => {
            match try!(interpret(data, lhs, ctx)).as_array() {
                None => Ok(Rc::new(Variable::Null)),
                Some(left) => {
                    let mut collected = vec![];
                    for element in left {
                        let current = try!(interpret(element, rhs, ctx));
                        if !current.is_null() {
                            collected.push(current);
                        }
                    }
                    Ok(Rc::new(Variable::Array(collected)))
                }
            }
        },
        Ast::Flatten { ref node, .. } => {
            match try!(interpret(data, node, ctx)).as_array() {
                None => Ok(Rc::new(Variable::Null)),
                Some(a) => {
                    let mut collected: Vec<RcVar> = vec![];
                    for element in a {
                        match element.as_array() {
                            Some(array) => collected.extend(array.iter().cloned()),
                            _ => collected.push(element.clone())
                        }
                    }
                    Ok(Rc::new(Variable::Array(collected)))
                }
            }
        },
        Ast::MultiList { ref elements, .. } => {
            if data.is_null() {
                Ok(Rc::new(Variable::Null))
            } else {
                let mut collected = vec![];
                for node in elements {
                    collected.push(try!(interpret(data, node, ctx)));
                }
                Ok(Rc::new(Variable::Array(collected)))
            }
        },
        Ast::MultiHash { ref elements, .. } => {
            if data.is_null() {
                Ok(Rc::new(Variable::Null))
            } else {
                let mut collected = BTreeMap::new();
                for kvp in elements {
                    let value = try!(interpret(data, &kvp.value, ctx));
                    collected.insert(kvp.key.clone(), value);
                }
                Ok(Rc::new(Variable::Object(collected)))
            }
        },
        Ast::Function { ref name, ref args, ref offset } => {
            let mut fn_args: Vec<RcVar> = vec![];
            for arg in args {
                fn_args.push(try!(interpret(data, arg, ctx)));
            }
            // Reset the offset so that it points to the function being evaluated.
            ctx.offset = *offset;
            ctx.fn_registry.evaluate(name, &fn_args, ctx).unwrap_or_else(|| {
                Err(Error::from_ctx(ctx, ErrorReason::Runtime(
                    RuntimeError::UnknownFunction(name.to_owned())
                )))
            })
        },
        Ast::Expref{ ref ast, .. } => {
            Ok(Rc::new(Variable::Expref(*ast.clone())))
        },
        Ast::Slice { ref start, ref stop, step, ref offset } => {
            ctx.offset = *offset;
            if step == 0 {
                Err(Error::from_ctx(ctx, ErrorReason::Runtime(RuntimeError::InvalidSlice)))
            } else {
                match data.slice(start, stop, step) {
                    Some(array) => Ok(Rc::new(Variable::Array(array))),
                    None => Ok(Rc::new(Variable::Null)),
                }
            }
        }
    }
}
