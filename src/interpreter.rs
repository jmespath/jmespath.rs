//! Interprets JMESPath expressions

extern crate serde;

use std::rc::Rc;
use std::collections::BTreeMap;

use super::{Coordinates, RcVar, Error, ErrorReason, RuntimeError};
use super::ast::Ast;
use super::functions::{FnDispatcher, BuiltinDispatcher};
use super::variable::Variable;

use self::serde::Serialize;

pub type SearchResult = Result<RcVar, Error>;

/// TreeInterpreter context object used primarily for error reporting.
pub struct Context<'a> {
    /// Tree interpreter used to make subsequent calls.
    pub interpreter: &'a TreeInterpreter,
    /// Original expression that is being interpreted.
    pub expression: &'a str,
    /// Offset being evaluated
    pub offset: usize
}

impl<'a> Context<'a> {
    /// Create a new context struct.
    pub fn new(interpreter: &'a TreeInterpreter, expression: &'a str) -> Context<'a> {
        Context {
            interpreter: interpreter,
            expression: expression,
            offset: 0
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

/// TreeInterpreter recursively extracts data using an AST.
pub struct TreeInterpreter {
    /// Provides a mapping between JMESPath function names and the function to execute.
    fn_dispatcher: Box<FnDispatcher>
}

impl TreeInterpreter {
    /// Creates a new TreeInterpreter
    pub fn new() -> TreeInterpreter {
        Self::with_fn_dispatcher(Box::new(BuiltinDispatcher))
    }

    /// Creates a new TreeInterpreter with a custom function dispatcher.
    #[inline]
    pub fn with_fn_dispatcher(fn_dispatcher: Box<FnDispatcher>) -> TreeInterpreter {
        TreeInterpreter {
            fn_dispatcher: fn_dispatcher
        }
    }

    /// Interprets the given data using an AST node.
    #[inline(never)]
    pub fn interpret(&self, data: &RcVar, node: &Ast, ctx: &mut Context) -> SearchResult {
        match *node {
            Ast::Subexpr { ref lhs, ref rhs, .. } => {
                let left_result = try!(self.interpret(data, lhs, ctx));
                self.interpret(&left_result, rhs, ctx)
            },
            Ast::Field { ref name, .. } => {
                match data.get_value(name) {
                    Some(v) => Ok(v),
                    None => Ok(ctx.alloc_null())
                }
            },
            Ast::Identity { .. } => {
                Ok(data.clone())
            },
            Ast::Literal { ref value, .. } => {
                Ok(value.clone())
            },
            Ast::Index { ref idx, .. } => {
                let result = if *idx >= 0 {
                    data.get_index(*idx as usize)
                } else {
                    data.get_negative_index((-1 * idx) as usize)
                };
                match result {
                    Some(value) => Ok(value),
                    None => Ok(ctx.alloc_null())
                }
            },
            Ast::Or { ref lhs, ref rhs, .. } => {
                let left = try!(self.interpret(data, lhs, ctx));
                if left.is_truthy() {
                    Ok(left)
                } else {
                    self.interpret(data, rhs, ctx)
                }
            },
            Ast::And { ref lhs, ref rhs, .. } => {
                let left = try!(self.interpret(data, lhs, ctx));
                if !left.is_truthy() {
                    Ok(left)
                } else {
                    self.interpret(data, rhs, ctx)
                }
            },
            Ast::Not { ref node, .. } => {
                let result = try!(self.interpret(data, node, ctx));
                Ok(Rc::new(Variable::Bool(!result.is_truthy())))
            },
            // Returns the resut of RHS if cond yields truthy value.
            Ast::Condition { ref predicate, ref then, .. } => {
                let cond_result = try!(self.interpret(data, predicate, ctx));
                if cond_result.is_truthy() {
                    self.interpret(data, then, ctx)
                } else {
                    Ok(ctx.alloc_null())
                }
            },
            Ast::Comparison { ref comparator, ref lhs, ref rhs, .. } => {
                let left = try!(self.interpret(data, lhs, ctx));
                let right = try!(self.interpret(data, rhs, ctx));
                Ok(left.compare(comparator, &*right)
                    .map_or(ctx.alloc_null(), |result| Rc::new(Variable::Bool(result))))
            },
            // Converts an object into a JSON array of its values.
            Ast::ObjectValues { ref node, .. } => {
                let subject = try!(self.interpret(data, node, ctx));
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
                match try!(self.interpret(data, lhs, ctx)).as_array() {
                    None => Ok(ctx.alloc_null()),
                    Some(left) => {
                        let mut collected = vec![];
                        for element in left {
                            let current = try!(self.interpret(element, rhs, ctx));
                            if !current.is_null() {
                                collected.push(current);
                            }
                        }
                        Ok(Rc::new(Variable::Array(collected)))
                    }
                }
            },
            Ast::Flatten { ref node, .. } => {
                match try!(self.interpret(data, node, ctx)).as_array() {
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
                        collected.push(try!(self.interpret(data, node, ctx)));
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
                        let value = try!(self.interpret(data, &kvp.value, ctx));
                        collected.insert(kvp.key.clone(), value);
                    }
                    Ok(Rc::new(Variable::Object(collected)))
                }
            },
            Ast::Function { ref name, ref args, ref offset } => {
                let mut fn_args: Vec<RcVar> = vec![];
                for arg in args {
                    fn_args.push(try!(self.interpret(data, arg, ctx)));
                }
                // Reset the offset so that it points to the function being evaluated.
                ctx.offset = *offset;
                self.fn_dispatcher.evaluate(name, fn_args, ctx)
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
    use variable::Variable;

    #[test]
    fn context_allocates_values() {
        let i = TreeInterpreter::new();
        let ctx = Context::new(&i, "foo.bar");
        assert_eq!(Rc::new(Variable::Bool(true)), ctx.alloc(true));
    }

    #[test]
    fn context_allocates_null() {
        let i = TreeInterpreter::new();
        let ctx = Context::new(&i, "foo.bar");
        assert_eq!(Rc::new(Variable::Null), ctx.alloc_null());
    }

    #[test]
    fn context_creates_coordinates() {
        let i = TreeInterpreter::new();
        let mut ctx = Context::new(&i, "foo.bar");
        ctx.offset = 3;
        let coords = ctx.create_coordinates();
        assert_eq!(3, coords.offset);
        assert_eq!(3, coords.column);
        assert_eq!(0, coords.line);
    }
}
