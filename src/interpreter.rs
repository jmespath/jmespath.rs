//! Interprets JMESPath expressions

use std::collections::{BTreeMap, HashMap};

use super::RcVar;
use super::RuntimeError;
use super::ast::Ast;
use super::functions::{register_core_functions, JPFunction, Functions};
use super::variable::{Variable, VariableAllocator};

pub type SearchResult = Result<RcVar, RuntimeError>;

/// TreeInterpreter recursively extracts data using an AST.
pub struct TreeInterpreter {
    /// Allocates runtime variables.
    pub allocator: VariableAllocator,
    /// Provides a mapping between JMESPath function names and the function to execute.
    functions: Functions
}

impl TreeInterpreter {
    /// Creates a new TreeInterpreter
    pub fn new() -> TreeInterpreter {
        let mut functions = HashMap::new();
        register_core_functions(&mut functions);
        Self::with_functions(functions)
    }

    /// Creates a new TreeInterpreter with a custom function map.
    #[inline]
    pub fn with_functions(functions: Functions) -> TreeInterpreter {
        TreeInterpreter {
            allocator: VariableAllocator::new(),
            functions: functions
        }
    }

    /// Interprets the given data using an AST node.
    pub fn interpret(&self, data: &RcVar, node: &Ast) -> SearchResult {
        match node {
            &Ast::Subexpr { ref lhs, ref rhs } => {
                let left_result = try!(self.interpret(data, lhs));
                self.interpret(&left_result, rhs)
            },
            &Ast::Field(ref f) => Ok(data.get_value(f).unwrap_or(self.allocator.alloc_null())),
            &Ast::Identity => Ok(data.clone()),
            &Ast::Literal(ref json) => Ok(json.clone()),
            &Ast::Index(ref i) => {
                match if *i >= 0 {
                    data.get_index(*i as usize)
                } else {
                    data.get_negative_index((-1 * i) as usize)
                } {
                    Some(value) => Ok(value),
                    None => Ok(self.allocator.alloc_null())
                }
            },
            &Ast::Or { ref lhs, ref rhs } => {
                let left = try!(self.interpret(data, lhs));
                if left.is_truthy() {
                    Ok(left)
                } else {
                    self.interpret(data, rhs)
                }
            },
            &Ast::And { ref lhs, ref rhs } => {
                let left = try!(self.interpret(data, lhs));
                if !left.is_truthy() {
                    Ok(left)
                } else {
                    self.interpret(data, rhs)
                }
            },
            &Ast::Not(ref expr) => {
                let result = try!(self.interpret(data, expr));
                Ok(self.allocator.alloc_bool(!result.is_truthy()))
            },
            // Returns the resut of RHS if cond yields truthy value.
            &Ast::Condition { ref predicate, ref then } => {
                let cond_result = try!(self.interpret(data, predicate));
                if cond_result.is_truthy() {
                    self.interpret(data, then)
                } else {
                    Ok(self.allocator.alloc_null())
                }
            },
            &Ast::Comparison { ref comparator, ref lhs, ref rhs } => {
                let left = try!(self.interpret(data, lhs));
                let right = try!(self.interpret(data, rhs));
                Ok(left.compare(comparator, &*right).map_or(
                    self.allocator.alloc_null(),
                    |result| self.allocator.alloc_bool(result)))
            },
            // Converts an object into a JSON array of its values.
            &Ast::ObjectValues(ref predicate) => {
                let subject = try!(self.interpret(data, predicate));
                match *subject {
                    Variable::Object(ref v) => {
                        Ok(self.allocator.alloc(v.values().cloned().collect::<Vec<RcVar>>()))
                    },
                    _ => Ok(self.allocator.alloc_null())
                }
            },
            // Passes the results of lhs into rhs if lhs yields an array and
            // each node of lhs that passes through rhs yields a non-null value.
            &Ast::Projection { ref lhs, ref rhs } => {
                match try!(self.interpret(data, lhs)).as_array() {
                    None => Ok(self.allocator.alloc_null()),
                    Some(left) => {
                        let mut collected = vec![];
                        for element in left {
                            let current = try!(self.interpret(element, rhs));
                            if !current.is_null() {
                                collected.push(current);
                            }
                        }
                        Ok(self.allocator.alloc(collected))
                    }
                }
            },
            &Ast::Flatten(ref node) => {
                match try!(self.interpret(data, node)).as_array() {
                    None => Ok(self.allocator.alloc_null()),
                    Some(a) => {
                        let mut collected: Vec<RcVar> = vec![];
                        for element in a {
                            match element.as_array() {
                                Some(array) => collected.extend(array.iter().cloned()),
                                _ => collected.push(element.clone())
                            }
                        }
                        Ok(self.allocator.alloc(collected))
                    }
                }
            },
            &Ast::MultiList(ref nodes) => {
                if data.is_null() {
                    Ok(self.allocator.alloc_null())
                } else {
                    let mut collected = vec![];
                    for node in nodes {
                        collected.push(try!(self.interpret(data, node)));
                    }
                    Ok(self.allocator.alloc(collected))
                }
            },
            &Ast::MultiHash(ref kvp_list) => {
                if data.is_null() {
                    Ok(self.allocator.alloc_null())
                } else {
                    let mut collected = BTreeMap::new();
                    for kvp in kvp_list {
                        let key = try!(self.interpret(data, &kvp.key));
                        let value = try!(self.interpret(data, &kvp.value));
                        if let Variable::String(ref s) = *key {
                            collected.insert(s.to_string(), value);
                        } else {
                            return Err(RuntimeError::InvalidKey {
                                actual: key.get_type().to_string()
                            });
                        }
                    }
                    Ok(self.allocator.alloc(collected))
                }
            },
            &Ast::Function { ref name, ref args } => {
                let mut fn_args: Vec<RcVar> = vec![];
                for arg in args {
                    fn_args.push(try!(self.interpret(data, arg)));
                }
                match self.functions.get(name) {
                    Some(f) => f.evaluate(fn_args, self),
                    None => Err(RuntimeError::UnknownFunction { function: name.clone() })
                }
            },
            &Ast::Expref(ref ast) => Ok(self.allocator.alloc(*ast.clone())),
            &Ast::Slice { ref start, ref stop, step } => {
                if step == 0 {
                    Err(RuntimeError::InvalidSlice)
                } else {
                    match data.as_array() {
                        Some(ref array) => {
                            Ok(self.allocator.alloc(slice(array, start, stop, step)))
                        },
                        None => Ok(self.allocator.alloc_null())
                    }
                }
            }
        }
    }
}

fn slice(array: &Vec<RcVar>, start: &Option<i32>, stop: &Option<i32>, step: i32)
    -> Vec<RcVar>
{
    let mut result = vec![];
    let len = array.len() as i32;
    if len == 0 {
        return result;
    }
    let a: i32 = match start {
        &Some(starting_index) => adjust_slice_endpoint(len, starting_index, step),
        _ if step < 0 => len - 1,
        _ => 0
    };
    let b: i32 = match stop {
        &Some(ending_index) => adjust_slice_endpoint(len, ending_index, step),
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
