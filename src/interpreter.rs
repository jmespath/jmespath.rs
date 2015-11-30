//! Extracts JSON data by interpreting a JMESPath AST
use std::rc::Rc;
use std::collections::BTreeMap;

use ast::Ast;
use functions::{FnDispatcher, BuiltinFunctions};
use variable::{Variable, VariableArena};

pub type InterpretResult = Result<Rc<Variable>, String>;

/// Creates a new TreeInterpreter and interprets data with a given AST.
pub fn interpret(data: Rc<Variable>, ast: &Ast) -> InterpretResult {
    TreeInterpreter::new(&BuiltinFunctions::new()).interpret(data, ast)
}

/// TreeInterpreter recursively extracts data using an AST.
#[derive(Clone)]
pub struct TreeInterpreter<'a> {
    /// Handles interpreting built-in functions from the AST.
    fn_dispatcher: &'a FnDispatcher,
    /// Allocates runtime variables.
    pub arena: VariableArena
}

impl<'a> TreeInterpreter<'a> {
    /// Creates a new TreeInterpreter using the given function dispatcher.
    pub fn new(fn_dispatcher: &'a FnDispatcher) -> TreeInterpreter<'a> {
        TreeInterpreter {
            fn_dispatcher: fn_dispatcher,
            arena: VariableArena::new()
        }
    }

    /// Interprets the given data using an AST node.
    pub fn interpret(&self, data: Rc<Variable>, node: &Ast) -> InterpretResult {
        match node {
            &Ast::Subexpr(ref lhs, ref rhs) =>
                self.interpret(try!(self.interpret(data, lhs)), rhs),
            &Ast::Identifier(ref f) => Ok(data.get_value(f).unwrap_or(self.arena.alloc_null())),
            &Ast::CurrentNode => Ok(data.clone()),
            &Ast::Literal(ref json) => Ok(json.clone()),
            &Ast::Index(ref i) => {
                match if *i >= 0 {
                    data.get_index(*i as usize)
                } else {
                    data.get_negative_index((-1 * i) as usize)
                } {
                    Some(value) => Ok(value),
                    None => Ok(self.arena.alloc_null())
                }
            },
            &Ast::Or(ref lhs, ref rhs) => {
                let left = try!(self.interpret(data.clone(), lhs));
                if left.is_truthy() {
                    Ok(left)
                } else {
                    self.interpret(data, rhs)
                }
            },
            &Ast::And(ref lhs, ref rhs) => {
                let left = try!(self.interpret(data.clone(), lhs));
                if !left.is_truthy() {
                    Ok(left)
                } else {
                    self.interpret(data, rhs)
                }
            },
            &Ast::Not(ref expr) => {
                let result = try!(self.interpret(data.clone(), expr));
                Ok(self.arena.alloc_bool(!result.is_truthy()))
            },
            // Returns the resut of RHS if cond yields truthy value.
            &Ast::Condition(ref cond, ref cond_rhs) => {
                let cond_result = try!(self.interpret(data.clone(), cond));
                if cond_result.is_truthy() {
                    self.interpret(data, cond_rhs)
                } else {
                    Ok(self.arena.alloc_null())
                }
            },
            &Ast::Comparison(ref cmp, ref lhs, ref rhs) => {
                let left = try!(self.interpret(data.clone(), lhs));
                let right = try!(self.interpret(data, rhs));
                Ok(left.compare(cmp, &*right).map_or(
                    self.arena.alloc_null(),
                    |result| self.arena.alloc_bool(result)))
            },
            // Converts an object into a JSON array of its values.
            &Ast::ObjectValues(ref predicate) => {
                Ok(match try!(self.interpret(data, predicate)).object_values() {
                    Some(values) => self.arena.alloc(values),
                    None => self.arena.alloc_null()
                })
            },
            // Passes the results of lhs into rhs if lhs yields an array and
            // each node of lhs that passes through rhs yields a non-null value.
            &Ast::Projection(ref lhs, ref rhs) => {
                match try!(self.interpret(data, lhs)).as_array() {
                    None => Ok(self.arena.alloc_null()),
                    Some(left) => {
                        let mut collected = vec!();
                        for element in left {
                            let current = try!(self.interpret(element.clone(), rhs));
                            if !current.is_null() {
                                collected.push(current);
                            }
                        }
                        Ok(self.arena.alloc(collected))
                    }
                }
            },
            &Ast::Flatten(ref node) => {
                match try!(self.interpret(data, node)).as_array() {
                    None => Ok(self.arena.alloc_null()),
                    Some(a) => {
                        let mut collected: Vec<Rc<Variable>> = vec!();
                        for element in a {
                            match element.as_array() {
                                Some(array) => collected.extend(array.iter().cloned()),
                                _ => collected.push(element.clone())
                            }
                        }
                        Ok(self.arena.alloc(collected))
                    }
                }
            },
            &Ast::MultiList(ref nodes) => {
                if data.is_null() {
                    Ok(self.arena.alloc_null())
                } else {
                    let mut collected = vec!();
                    for node in nodes {
                        collected.push(try!(self.interpret(data.clone(), node)));
                    }
                    Ok(self.arena.alloc(collected))
                }
            },
            &Ast::MultiHash(ref kvp_list) => {
                if data.is_null() {
                    Ok(self.arena.alloc_null())
                } else {
                    let mut collected = BTreeMap::new();
                    for kvp in kvp_list {
                        let key = try!(self.interpret(data.clone(), &kvp.key));
                        let value = try!(self.interpret(data.clone(), &kvp.value));
                        let key_value = key.as_string().expect("Expected string").to_string();
                        collected.insert(key_value, value);
                    }
                    Ok(self.arena.alloc(collected))
                }
            },
            &Ast::Function(ref fn_name, ref arg_nodes) => {
                let mut args: Vec<Rc<Variable>> = vec![];
                for arg in arg_nodes {
                    args.push(try!(self.interpret(data.clone(), arg)));
                }
                self.fn_dispatcher.call(fn_name, &args, &self)
            },
            &Ast::Expref(ref ast) => Ok(self.arena.alloc(*ast.clone())),
            &Ast::Slice(ref a, ref b, c) => {
                match data.as_array() {
                    Some(ref array) => Ok(self.arena.alloc(slice(array, a, b, c))),
                    None => Ok(self.arena.alloc_null())
                }
            }
        }
    }
}

fn slice(array: &Vec<Rc<Variable>>, start: &Option<i32>, stop: &Option<i32>, step: i32)
    -> Vec<Rc<Variable>>
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


#[cfg(test)]
mod tests {
    use std::rc::Rc;
    use std::collections::BTreeMap;

    use super::*;
    use ast::{Ast, Comparator, KeyValuePair};
    use variable::Variable;

    #[test]
    fn interprets_identifier() {
        let ast = Ast::Identifier("foo".to_string());
        let data = Rc::new(Variable::from_str("{\"foo\":\"baz\"}").unwrap());
        assert_eq!(Rc::new(Variable::String("baz".to_string())), interpret(data, &ast).unwrap());
    }

    #[test]
    fn interprets_current_node() {
        let ast = Ast::CurrentNode;
        let data = Rc::new(Variable::Boolean(true));
        assert_eq!(Rc::new(Variable::Boolean(true)), interpret(data, &ast).unwrap());
    }

    #[test]
    fn interprets_literal() {
        let ast = Ast::Literal(Rc::new(Variable::Boolean(true)));
        let data = Rc::new(Variable::Object(BTreeMap::new()));
        assert_eq!(Rc::new(Variable::Boolean(true)), interpret(data, &ast).unwrap());
    }

    #[test]
    fn interprets_subexpr() {
        let ast = Ast::Subexpr(Box::new(Ast::Identifier("foo".to_string())),
                               Box::new(Ast::Identifier("bar".to_string())));
        let data = Rc::new(Variable::from_str("{\"foo\":{\"bar\":\"baz\"}}").unwrap());
        assert_eq!(Rc::new(Variable::String("baz".to_string())), interpret(data, &ast).unwrap());
    }

    #[test]
    fn interprets_index() {
        let data = Rc::new(Variable::Array(vec![
            Rc::new(Variable::Boolean(false)),
            Rc::new(Variable::Boolean(true))]));
        assert_eq!(Rc::new(Variable::Boolean(true)),
                   interpret(data.clone(), &Ast::Index(-1)).unwrap());
        assert_eq!(Rc::new(Variable::Boolean(false)),
                   interpret(data.clone(), &Ast::Index(-2)).unwrap());
        assert_eq!(Rc::new(Variable::Boolean(false)),
                   interpret(data.clone(), &Ast::Index(0)).unwrap());
        assert_eq!(Rc::new(Variable::Boolean(true)),
                   interpret(data.clone(), &Ast::Index(1)).unwrap());
    }

    #[test]
    fn interprets_index_when_not_array_as_null() {
        let ast = Ast::Index(1);
        let data = Rc::new(Variable::String("foo".to_string()));
        assert_eq!(Rc::new(Variable::Null), interpret(data, &ast).unwrap());
    }

    #[test]
    fn interprets_or_expr() {
        let ast = Ast::Or(Box::new(Ast::Identifier("bar".to_string())),
                          Box::new(Ast::Identifier("foo".to_string())));
        let data = Rc::new(Variable::from_str("{\"foo\":true}").unwrap());
        assert_eq!(Rc::new(Variable::Boolean(true)), interpret(data, &ast).unwrap());
    }

    #[test]
    fn interprets_and_expr() {
        let ast = Ast::And(Box::new(Ast::Identifier("bar".to_string())),
                           Box::new(Ast::Identifier("foo".to_string())));
        let data = Rc::new(Variable::from_str("{\"foo\":true, \"bar\":true}").unwrap());
        assert_eq!(Rc::new(Variable::Boolean(true)), interpret(data, &ast).unwrap());
        let data = Rc::new(Variable::from_str("{\"foo\":true}").unwrap());
        assert_eq!(Rc::new(Variable::Null), interpret(data, &ast).unwrap());
    }

    #[test]
    fn interprets_not_expr() {
        let data = Rc::new(Variable::from_str("{\"a\":true,\"b\":0,\"c\":false}").unwrap());
        let ast = Ast::Not(Box::new(Ast::Identifier("a".to_string())));
        assert_eq!(Rc::new(Variable::Boolean(false)), interpret(data.clone(), &ast).unwrap());
        let ast = Ast::Not(Box::new(Ast::Identifier("b".to_string())));
        assert_eq!(Rc::new(Variable::Boolean(false)), interpret(data.clone(), &ast).unwrap());
        let ast = Ast::Not(Box::new(Ast::Identifier("c".to_string())));
        assert_eq!(Rc::new(Variable::Boolean(true)), interpret(data.clone(), &ast).unwrap());
    }

    #[test]
    fn interprets_cond_expr() {
        let ast = Ast::Condition(
            Box::new(Ast::Literal(Rc::new(Variable::Boolean(true)))),
            Box::new(Ast::Literal(Rc::new(Variable::String("foo".to_string())))));
        let data = Rc::new(Variable::Null);
        assert_eq!(Rc::new(Variable::String("foo".to_string())), interpret(data, &ast).unwrap());
    }

    #[test]
    fn interprets_cond_expr_negative() {
        let ast = Ast::Condition(
            Box::new(Ast::Literal(Rc::new(Variable::Boolean(false)))),
            Box::new(Ast::Literal(Rc::new(Variable::String("foo".to_string())))));
        let data = Rc::new(Variable::Null);
        assert_eq!(Rc::new(Variable::Null), interpret(data, &ast).unwrap());
    }

    #[test]
    fn interprets_comparison() {
        // Left, right, result, comparator.
        let cases = vec![vec!["true", "true", "true", "=="],
                         vec!["true", "false", "false", "=="],
                         vec!["true", "null", "false", "=="],
                         vec!["null", "null", "true", "=="],
                         vec!["10", "20", "false", ">"],
                         vec!["10", "20", "true", "<"]];
        for test_case in cases {
            let cmp = match test_case[3] {
                "==" => Comparator::Eq,
                ">" => Comparator::Gt,
                _ => Comparator::Lt,
            };
            let lhs = Rc::new(Variable::from_str(test_case[0]).unwrap());
            let rhs = Rc::new(Variable::from_str(test_case[1]).unwrap());
            let ast = Ast::Comparison(
                cmp, Box::new(Ast::Literal(lhs)), Box::new(Ast::Literal(rhs)));
            let result = Variable::from_str(test_case[2]).unwrap();
            assert_eq!(Rc::new(result), interpret(Rc::new(Variable::Null), &ast).unwrap());
        }
    }

    #[test]
    fn interprets_object_values_to_array_negative() {
        let ast = Ast::ObjectValues(Box::new(Ast::Literal(Rc::new(Variable::Boolean(false)))));
        let data = Rc::new(Variable::Null);
        assert_eq!(Rc::new(Variable::Null), interpret(data, &ast).unwrap());
    }

    #[test]
    fn interprets_object_values_to_array_affirmative() {
        let var = Rc::new(Variable::from_str("{\"foo\": \"bar\"}").unwrap());
        let ast = Ast::ObjectValues(Box::new(Ast::Literal(var)));
        let data = Rc::new(Variable::Null);
        assert_eq!(
            Rc::new(Variable::from_str("[\"bar\"]").unwrap()),
            interpret(data, &ast).unwrap());
    }

    #[test]
    fn projection_on_non_array_returns_null() {
        let ast = Ast::Projection(
            Box::new(Ast::Identifier("a".to_string())),
            Box::new(Ast::Identifier("b".to_string())));
        let data = Rc::new(Variable::Boolean(true));
        assert_eq!(Rc::new(Variable::Null), interpret(data, &ast).unwrap());
    }

    #[test]
    fn projection_applies_to_array() {
        let data = Rc::new(Variable::from_str("{\"a\": [{\"b\":1},{\"b\":2}]}").unwrap());
        let ast = Ast::Projection(
            Box::new(Ast::Identifier("a".to_string())),
            Box::new(Ast::Identifier("b".to_string())));
        assert_eq!(
            Rc::new(Variable::from_str("[1, 2]").unwrap()),
            interpret(data, &ast).unwrap());
    }

    #[test]
    fn flatten_of_non_array_is_null() {
        let data = Rc::new(Variable::from_str("{\"a\": true}").unwrap());
        let ast = Ast::Flatten(Box::new(Ast::Identifier("a".to_string())));
        assert_eq!(Rc::new(Variable::Null), interpret(data, &ast).unwrap());
    }

    #[test]
    fn flattens_arrays() {
        let data = Rc::new(Variable::from_str("{\"a\": [1, [2, 3], 4, [[5]]]}").unwrap());
        let ast = Ast::Flatten(Box::new(Ast::Identifier("a".to_string())));
        assert_eq!(
            Rc::new(Variable::from_str("[1, 2, 3, 4, [5]]").unwrap()),
            interpret(data, &ast).unwrap());
    }

    #[test]
    fn multi_list_on_null_is_null() {
        let ast = Ast::MultiList(vec!());
        assert_eq!(Rc::new(Variable::Null), interpret(Rc::new(Variable::Null), &ast).unwrap());
    }

    #[test]
    fn multi_list_creates_array() {
        let data = Rc::new(Variable::from_str("{\"a\": 1, \"b\": 2}").unwrap());
        let ast = Ast::MultiList(vec![Ast::Identifier("a".to_string()),
                                      Ast::Identifier("b".to_string())]);
        assert_eq!(
            Rc::new(Variable::from_str("[1, 2]").unwrap()),
            interpret(data, &ast).unwrap());
    }

    #[test]
    fn multi_hash_on_null_is_null() {
        let ast = Ast::MultiHash(vec![]);
        assert_eq!(Rc::new(Variable::Null), interpret(Rc::new(Variable::Null), &ast).unwrap());
    }

    #[test]
    fn multi_hash_creates_object() {
        let data = Rc::new(Variable::from_str("{\"aye\": 1, \"bee\": 2}").unwrap());
        let ast = Ast::MultiHash(vec![
            KeyValuePair {
                key: Ast::Literal(Rc::new(Variable::String("a".to_string()))),
                value: Ast::Identifier("aye".to_string())
            },
            KeyValuePair {
                key: Ast::Literal(Rc::new(Variable::String("b".to_string()))),
                value: Ast::Identifier("bee".to_string())
            }
        ]);
        assert_eq!(
            Rc::new(Variable::from_str("{\"a\": 1, \"b\": 2}").unwrap()),
            interpret(data, &ast).unwrap());
    }

    #[test]
    fn calls_functions() {
        let data = Rc::new(Variable::from_str("[1, 2, 3]").unwrap());
        let ast = Ast::Function("length".to_string(), vec![Ast::CurrentNode]);
        assert_eq!(Rc::new(Variable::U64(3)), interpret(data, &ast).unwrap());
    }

    #[test]
    fn slices_arrays() {
        let data = Rc::new(Variable::from_str("[0, 1, 2, 3, 4]").unwrap());
        let ast = Ast::Slice(Some(1), Some(3), 1);
        assert_eq!(Rc::new(Variable::from_str("[1, 2]").unwrap()),
                   interpret(data, &ast).unwrap());
    }

    #[test]
    fn slices_arrays_with_negative_index() {
        let data = Rc::new(Variable::from_str("[0, 1, 2, 3, 4, 5, 6]").unwrap());
        let ast = Ast::Slice(Some(-1), Some(3), -1);
        assert_eq!(Rc::new(Variable::from_str("[6, 5, 4]").unwrap()),
                   interpret(data, &ast).unwrap());
    }
}
