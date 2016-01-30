//! Interprets JMESPath expressions

extern crate serde;

use std::rc::Rc;
use std::collections::BTreeMap;
use std::cmp::max;

use super::{Coordinates, RcVar, Error, ErrorReason, RuntimeError};
use super::ast::Ast;
use super::functions::FnDispatcher;
use super::variable::Variable;

use self::serde::Serialize;

pub type SearchResult = Result<RcVar, Error>;

/// TreeInterpreter context object used primarily for error reporting.
pub struct Context<'a> {
    /// Original expression that is being interpreted.
    pub expression: &'a str,
    /// Function dispatcher
    pub fn_dispatcher: &'a FnDispatcher,
    /// Offset being evaluated
    pub offset: usize,
}

impl<'a> Context<'a> {
    /// Create a new context struct.
    #[inline]
    pub fn new(expression: &'a str, fn_dispatcher: &'a FnDispatcher) -> Context<'a> {
        Context {
            expression: expression,
            fn_dispatcher: fn_dispatcher,
            offset: 0,
        }
    }

    /// Allocate a null value
    #[inline]
    pub fn alloc_null(&self) -> RcVar {
        Rc::new(Variable::Null)
    }

    /// Convenience method to allocates a Variable.
    #[inline]
    pub fn alloc<S: Serialize>(&self, s: S) -> RcVar {
        Rc::new(Variable::from_serialize(&s))
    }

    /// Create a coordinates struct from the context.
    pub fn create_coordinates(&self) -> Coordinates {
        Coordinates::from_offset(self.expression, self.offset)
    }
}

/// Interprets the given data using an AST node.
#[inline(never)]
pub fn interpret(data: &RcVar, node: &Ast, ctx: &mut Context) -> SearchResult {
    match *node {
        Ast::Subexpr { ref lhs, ref rhs, .. } => {
            let left_result = try!(interpret(data, lhs, ctx));
            interpret(&left_result, rhs, ctx)
        },
        Ast::Field { ref name, .. } => Ok(get_field(data, name)),
        Ast::Identity { .. } => Ok(data.clone()),
        Ast::Literal { ref value, .. } => Ok(value.clone()),
        Ast::Index { idx, .. } => {
            if idx >= 0 {
                Ok(get_index(data, idx as usize))
            } else {
                Ok(get_negative_index(data, (-1 * idx) as usize))
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
                Ok(ctx.alloc_null())
            }
        },
        Ast::Comparison { ref comparator, ref lhs, ref rhs, .. } => {
            let left = try!(interpret(data, lhs, ctx));
            let right = try!(interpret(data, rhs, ctx));
            Ok(left.compare(comparator, &*right)
                .map_or(ctx.alloc_null(), |result| Rc::new(Variable::Bool(result))))
        },
        // Converts an object into a JSON array of its values.
        Ast::ObjectValues { ref node, .. } => {
            let subject = try!(interpret(data, node, ctx));
            match *subject {
                Variable::Object(ref v) => {
                    Ok(Rc::new(Variable::Array(v.values().cloned().collect::<Vec<RcVar>>())))
                },
                _ => Ok(ctx.alloc_null())
            }
        },
        // Passes the results of lhs into rhs if lhs yields an array and
        // each node of lhs that passes through rhs yields a non-null value.
        Ast::Projection { ref lhs, ref rhs, .. } => {
            match try!(interpret(data, lhs, ctx)).as_array() {
                None => Ok(ctx.alloc_null()),
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
                None => Ok(ctx.alloc_null()),
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
                Ok(ctx.alloc_null())
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
                Ok(ctx.alloc_null())
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
            ctx.fn_dispatcher.evaluate(name, fn_args, ctx)
        },
        Ast::Expref{ ref ast, .. } => {
            Ok(Rc::new(Variable::Expref(*ast.clone())))
        },
        Ast::Slice { ref start, ref stop, step, ref offset } => {
            ctx.offset = *offset;
            if step == 0 {
                Err(Error::from_ctx(ctx, ErrorReason::Runtime(RuntimeError::InvalidSlice)))
            } else {
                match data.as_array() {
                    Some(ref array) => {
                        Ok(Rc::new(Variable::Array(slice(array, start, stop, step))))
                    },
                    None => Ok(ctx.alloc_null())
                }
            }
        }
    }
}

#[inline]
fn get_field(data: &RcVar, key: &str) -> RcVar {
    if let Variable::Object(ref map) = **data {
        if let Some(result) = map.get(key) {
            return result.clone();
        }
    }
    Rc::new(Variable::Null)
}

#[inline]
fn get_index(data: &RcVar, index: usize) -> RcVar {
    if let Variable::Array(ref array) = **data {
        if let Some(result) = array.get(index) {
            return result.clone();
        }
    }
    Rc::new(Variable::Null)
}

/// Retrieves an index from the end of a Variable if the Variable is an array.
/// Returns Null if not an array or if the index is not present.
/// The formula for determining the index position is length - index (i.e., an
/// index of 0 or 1 is treated as the end of the array).
fn get_negative_index(data: &RcVar, index: usize) -> RcVar {
    if let Variable::Array(ref array) = **data {
        let adjusted_index = max(index, 1);
        if array.len() >= adjusted_index {
            return array[array.len() - adjusted_index].clone();
        }
    }
    Rc::new(Variable::Null)
}

fn slice(array: &[RcVar], start: &Option<i32>, stop: &Option<i32>, step: i32)
    -> Vec<RcVar>
{
    let mut result = vec![];
    let len = array.len() as i32;
    if len == 0 {
        return result;
    }
    let a: i32 = match *start {
        Some(starting_index) => adjust_slice_endpoint(len, starting_index, step),
        _ if step < 0 => len - 1,
        _ => 0
    };
    let b: i32 = match *stop {
        Some(ending_index) => adjust_slice_endpoint(len, ending_index, step),
        _ if step < 0 => -1,
        _ => len
    };
    let mut i = a;
    if step > 0 {
        while i < b {
            result.push(array[i as usize].clone());
            i += step;
        }
    } else {
        while i > b {
            result.push(array[i as usize].clone());
            i += step;
        }
    }
    result
}

#[inline]
fn adjust_slice_endpoint(len: i32, mut endpoint: i32, step: i32) -> i32 {
    if endpoint < 0 {
        endpoint += len;
        if endpoint >= 0 {
            endpoint
        } else if step < 0 {
            -1
        } else {
            0
        }
    } else if endpoint < len {
        endpoint
    } else if step < 0 {
        len - 1
    } else {
        len
    }
}


#[cfg(test)]
mod tests {
    use std::rc::Rc;
    use super::*;
    use functions::BuiltinDispatcher;
    use variable::Variable;

    #[test]
    fn context_allocates_values() {
        let fns = BuiltinDispatcher;
        let ctx = Context::new("foo.bar", &fns);
        assert_eq!(Rc::new(Variable::Bool(true)), ctx.alloc(true));
    }

    #[test]
    fn context_allocates_null() {
        let fns = BuiltinDispatcher;
        let ctx = Context::new("foo.bar", &fns);
        assert_eq!(Rc::new(Variable::Null), ctx.alloc_null());
    }

    #[test]
    fn context_creates_coordinates() {
        let fns = BuiltinDispatcher;
        let mut ctx = Context::new("foo.bar", &fns);
        ctx.offset = 3;
        let coords = ctx.create_coordinates();
        assert_eq!(3, coords.offset);
        assert_eq!(3, coords.column);
        assert_eq!(0, coords.line);
    }
}
