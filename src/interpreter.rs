//! Extracts JSON data by interpreting a JMESPath AST

extern crate rustc_serialize;

use std::rc::Rc;
use std::collections::BTreeMap;

use ast::Ast;
use functions::{FnDispatcher, BuiltinFunctions};
use variable::Variable;

pub type InterpretResult = Result<Rc<Variable>, String>;

/// Creates a new TreeInterpreter and interprets data with a given AST.
pub fn interpret(data: Rc<Variable>, ast: &Ast) -> InterpretResult {
    TreeInterpreter::new(&BuiltinFunctions::new()).interpret(data, ast)
}

/// TreeInterpreter recursively extracts data using an AST.
#[derive(Clone)]
pub struct TreeInterpreter<'a> {
    /// Handles interpreting built-in functions from the AST.
    fn_dispatcher: &'a FnDispatcher
}

impl<'a> TreeInterpreter<'a> {
    /// Creates a new TreeInterpreter using the given function dispatcher.
    pub fn new(fn_dispatcher: &'a FnDispatcher) -> TreeInterpreter<'a> {
        TreeInterpreter {
            fn_dispatcher: fn_dispatcher
        }
    }

    /// Interprets the given data using an AST node.
    pub fn interpret(&self, data: Rc<Variable>, node: &Ast) -> InterpretResult {
        match node {
            &Ast::CurrentNode => Ok(data.clone()),
            &Ast::Literal(ref json) => Ok(json.clone()),
            &Ast::Subexpr(ref lhs, ref rhs) => self.interpret(try!(interpret(data, lhs)), rhs),
            &Ast::Identifier(ref f) => Ok(data.get_value(f).unwrap_or(Rc::new(Variable::Null))),
            &Ast::Index(ref i) => {
                match if *i >= 0 {
                    data.get_index(*i as usize)
                } else {
                    data.get_negative_index((-1 * i) as usize)
                } {
                    Some(value) => Ok(value),
                    None => Ok(Rc::new(Variable::Null))
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
                Ok(Rc::new(Variable::Boolean(!result.is_truthy())))
            },
            // Returns the resut of RHS if cond yields truthy value.
            &Ast::Condition(ref cond, ref cond_rhs) => {
                let cond_result = try!(self.interpret(data.clone(), cond));
                if cond_result.is_truthy() {
                    self.interpret(data, cond_rhs)
                } else {
                    Ok(Rc::new(Variable::Null))
                }
            },
            &Ast::Comparison(ref cmp, ref lhs, ref rhs) => {
                let left = try!(self.interpret(data.clone(), lhs));
                let right = try!(self.interpret(data, rhs));
                Ok(left.compare(cmp, &*right).map_or(
                    Rc::new(Variable::Null),
                    |result| Rc::new(Variable::Boolean(result))))
            },
            // Converts an object into a JSON array of its values.
            &Ast::ObjectValues(ref predicate) => {
                Ok(match try!(self.interpret(data, predicate)).object_values_to_array() {
                    Some(values) => Rc::new(values),
                    None => Rc::new(Variable::Null)
                })
            },
            // Passes the results of lhs into rhs if lhs yields an array and
            // each node of lhs that passes through rhs yields a non-null value.
            &Ast::Projection(ref lhs, ref rhs) => {
                match try!(self.interpret(data, lhs)).as_array() {
                    None => Ok(Rc::new(Variable::Null)),
                    Some(left) => {
                        let mut collected = vec!();
                        for element in left {
                            let current = try!(self.interpret(element.clone(), rhs));
                            if !current.is_null() {
                                collected.push(current);
                            }
                        }
                        Ok(Rc::new(Variable::Array(collected)))
                    }
                }
            },
            &Ast::Flatten(ref node) => {
                match try!(self.interpret(data, node)).as_array() {
                    None => Ok(Rc::new(Variable::Null)),
                    Some(a) => {
                        let mut collected: Vec<Rc<Variable>> = vec!();
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
            &Ast::MultiList(ref nodes) => {
                if data.is_null() {
                    Ok(Rc::new(Variable::Null))
                } else {
                    let mut collected = vec!();
                    for node in nodes {
                        collected.push(try!(self.interpret(data.clone(), node)));
                    }
                    Ok(Rc::new(Variable::Array(collected)))
                }
            },
            &Ast::MultiHash(ref kvp_list) => {
                if data.is_null() {
                    Ok(Rc::new(Variable::Null))
                } else {
                    let mut collected = BTreeMap::new();
                    for kvp in kvp_list {
                        let key = try!(self.interpret(data.clone(), &kvp.key));
                        let value = try!(self.interpret(data.clone(), &kvp.value));
                        collected.insert(key.as_string().unwrap().to_string(), value);
                    }
                    Ok(Rc::new(Variable::Object(collected)))
                }
            },
            &Ast::Function(ref fn_name, ref arg_nodes) => {
                let mut args: Vec<Rc<Variable>> = vec![];
                for arg in arg_nodes {
                    args.push(try!(self.interpret(data.clone(), arg)));
                }
                self.fn_dispatcher.call(fn_name, &args, &self)
            },
            &Ast::Expref(ref ast) => Ok(Rc::new(Variable::Expref(*ast.clone()))),
            ref node @ _ => panic!(format!("not implemented yet: {:?}", node))
        }
    }
}


#[cfg(test)]
mod tests {
    extern crate rustc_serialize;

    use std::rc::Rc;
    use std::collections::BTreeMap;

    use self::rustc_serialize::json::Json;

    use super::*;
    use ast::{Ast, Comparator, KeyValuePair};
    use variable::Variable;

    #[test] fn interprets_identifier() {
        let ast = Ast::Identifier("foo".to_string());
        let data = Rc::new(Variable::from_str("{\"foo\":\"baz\"}").unwrap());
        assert_eq!(Rc::new(Variable::String("baz".to_string())), interpret(data, &ast).unwrap());
    }

    #[test] fn interprets_current_node() {
        let ast = Ast::CurrentNode;
        let data = Rc::new(Variable::Boolean(true));
        assert_eq!(Rc::new(Variable::Boolean(true)), interpret(data, &ast).unwrap());
    }

    #[test] fn interprets_literal() {
        let ast = Ast::Literal(Rc::new(Variable::Boolean(true)));
        let data = Rc::new(Variable::Object(BTreeMap::new()));
        assert_eq!(Rc::new(Variable::Boolean(true)), interpret(data, &ast).unwrap());
    }

    #[test] fn interprets_subexpr() {
        let ast = Ast::Subexpr(Box::new(Ast::Identifier("foo".to_string())),
                               Box::new(Ast::Identifier("bar".to_string())));
        let data = Rc::new(Variable::from_str("{\"foo\":{\"bar\":\"baz\"}}").unwrap());
        assert_eq!(Rc::new(Variable::String("baz".to_string())), interpret(data, &ast).unwrap());
    }

    #[test] fn interprets_index() {
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

    #[test] fn interprets_index_when_not_array_as_null() {
        let ast = Ast::Index(1);
        let data = Rc::new(Variable::String("foo".to_string()));
        assert_eq!(Rc::new(Variable::Null), interpret(data, &ast).unwrap());
    }

    #[test] fn interprets_or_expr() {
        let ast = Ast::Or(Box::new(Ast::Identifier("bar".to_string())),
                          Box::new(Ast::Identifier("foo".to_string())));
        let data = Rc::new(Variable::from_str("{\"foo\":true}").unwrap());
        assert_eq!(Rc::new(Variable::Boolean(true)), interpret(data, &ast).unwrap());
    }

    #[test] fn interprets_and_expr() {
        let ast = Ast::And(Box::new(Ast::Identifier("bar".to_string())),
                           Box::new(Ast::Identifier("foo".to_string())));
        let data = Rc::new(Variable::from_str("{\"foo\":true, \"bar\":true}").unwrap());
        assert_eq!(Rc::new(Variable::Boolean(true)), interpret(data, &ast).unwrap());
        let data = Rc::new(Variable::from_str("{\"foo\":true}").unwrap());
        assert_eq!(Rc::new(Variable::Null), interpret(data, &ast).unwrap());
    }

    #[test] fn interprets_not_expr() {
        let data = Rc::new(Variable::from_str("{\"a\":true,\"b\":0,\"c\":false}").unwrap());
        let ast = Ast::Not(Box::new(Ast::Identifier("a".to_string())));
        assert_eq!(Rc::new(Variable::Boolean(false)), interpret(data.clone(), &ast).unwrap());
        let ast = Ast::Not(Box::new(Ast::Identifier("b".to_string())));
        assert_eq!(Rc::new(Variable::Boolean(false)), interpret(data.clone(), &ast).unwrap());
        let ast = Ast::Not(Box::new(Ast::Identifier("c".to_string())));
        assert_eq!(Rc::new(Variable::Boolean(true)), interpret(data.clone(), &ast).unwrap());
    }

    #[test] fn interprets_cond_expr() {
        let ast = Ast::Condition(
            Box::new(Ast::Literal(Rc::new(Variable::Boolean(true)))),
            Box::new(Ast::Literal(Rc::new(Variable::String("foo".to_string())))));
        let data = Rc::new(Variable::Null);
        assert_eq!(Rc::new(Variable::String("foo".to_string())), interpret(data, &ast).unwrap());
    }

    #[test] fn interprets_cond_expr_negative() {
        let ast = Ast::Condition(
            Box::new(Ast::Literal(Rc::new(Variable::Boolean(false)))),
            Box::new(Ast::Literal(Rc::new(Variable::String("foo".to_string())))));
        let data = Rc::new(Variable::Null);
        assert_eq!(Rc::new(Variable::Null), interpret(data, &ast).unwrap());
    }

    #[test] fn interprets_comparison() {
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
            let lhs = Rc::new(Variable::from_json(&Json::from_str(test_case[0]).unwrap()));
            let rhs = Rc::new(Variable::from_json(&Json::from_str(test_case[1]).unwrap()));
            let ast = Ast::Comparison(
                cmp, Box::new(Ast::Literal(lhs)), Box::new(Ast::Literal(rhs)));
            let result = Variable::from_json(&Json::from_str(test_case[2]).unwrap());
            assert_eq!(Rc::new(result), interpret(Rc::new(Variable::Null), &ast).unwrap());
        }
    }

    #[test] fn interprets_object_values_to_array_negative() {
        let ast = Ast::ObjectValues(Box::new(Ast::Literal(Rc::new(Variable::Boolean(false)))));
        let data = Rc::new(Variable::Null);
        assert_eq!(Rc::new(Variable::Null), interpret(data, &ast).unwrap());
    }

    #[test] fn interprets_object_values_to_array_affirmative() {
        let var = Rc::new(Variable::from_str("{\"foo\": \"bar\"}").unwrap());
        let ast = Ast::ObjectValues(Box::new(Ast::Literal(var)));
        let data = Rc::new(Variable::Null);
        assert_eq!(
            Rc::new(Variable::from_json(&Json::from_str("[\"bar\"]").unwrap())),
            interpret(data, &ast).unwrap());
    }

    #[test] fn projection_on_non_array_returns_null() {
        let ast = Ast::Projection(
            Box::new(Ast::Identifier("a".to_string())),
            Box::new(Ast::Identifier("b".to_string())));
        let data = Rc::new(Variable::Boolean(true));
        assert_eq!(Rc::new(Variable::Null), interpret(data, &ast).unwrap());
    }

    #[test] fn projection_applies_to_array() {
        let data = Rc::new(Variable::from_str("{\"a\": [{\"b\":1},{\"b\":2}]}").unwrap());
        let ast = Ast::Projection(
            Box::new(Ast::Identifier("a".to_string())),
            Box::new(Ast::Identifier("b".to_string())));
        assert_eq!(
            Rc::new(Variable::from_json(&Json::from_str("[1, 2]").unwrap())),
            interpret(data, &ast).unwrap());
    }

    #[test] fn flatten_of_non_array_is_null() {
        let data = Rc::new(Variable::from_str("{\"a\": true}").unwrap());
        let ast = Ast::Flatten(Box::new(Ast::Identifier("a".to_string())));
        assert_eq!(Rc::new(Variable::Null), interpret(data, &ast).unwrap());
    }

    #[test] fn flattens_arrays() {
        let data = Rc::new(Variable::from_str("{\"a\": [1, [2, 3], 4, [[5]]]}").unwrap());
        let ast = Ast::Flatten(Box::new(Ast::Identifier("a".to_string())));
        assert_eq!(
            Rc::new(Variable::from_json(&Json::from_str("[1, 2, 3, 4, [5]]").unwrap())),
            interpret(data, &ast).unwrap());
    }

    #[test] fn multi_list_on_null_is_null() {
        let ast = Ast::MultiList(vec!());
        assert_eq!(Rc::new(Variable::Null), interpret(Rc::new(Variable::Null), &ast).unwrap());
    }

    #[test] fn multi_list_creates_array() {
        let data = Rc::new(Variable::from_str("{\"a\": 1, \"b\": 2}").unwrap());
        let ast = Ast::MultiList(vec![Ast::Identifier("a".to_string()),
                                      Ast::Identifier("b".to_string())]);
        assert_eq!(
            Rc::new(Variable::from_json(&Json::from_str("[1, 2]").unwrap())),
            interpret(data, &ast).unwrap());
    }

    #[test] fn multi_hash_on_null_is_null() {
        let ast = Ast::MultiHash(vec![]);
        assert_eq!(Rc::new(Variable::Null), interpret(Rc::new(Variable::Null), &ast).unwrap());
    }

    #[test] fn multi_hash_creates_object() {
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
            Rc::new(Variable::from_json(&Json::from_str("{\"a\": 1, \"b\": 2}").unwrap())),
            interpret(data, &ast).unwrap());
    }

    #[test] fn calls_functions() {
        let data = Rc::new(Variable::from_str("[1, 2, 3]").unwrap());
        let ast = Ast::Function("length".to_string(), vec![Ast::CurrentNode]);
        assert_eq!(Rc::new(Variable::U64(3)), interpret(data, &ast).unwrap());
    }
}
