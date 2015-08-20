//! Extracts JSON data by interpreting a JMESPath AST

extern crate rustc_serialize;

use self::rustc_serialize::json::Json;
use std::collections::BTreeMap;

use ast::Ast;
use utils;

pub fn interpret(data: &Json, node: &Ast) -> Result<Json, String> {
    match node {
        &Ast::CurrentNode => Ok(data.clone()),
        &Ast::Literal(ref json) => Ok(json.clone()),
        &Ast::Subexpr(ref lhs, ref rhs) => {
            let result = try!(interpret(data, lhs));
            interpret(&result, rhs)
        },
        &Ast::Identifier(ref f) => {
            match data.find(f) {
                Some(j) => Ok(j.clone()),
                _ => Ok(Json::Null)
            }
        },
        &Ast::Index(ref i) => {
            match data.as_array() {
                None => Ok(Json::Null),
                Some(a) => {
                    let result = if *i >= 0 {
                        a.get(*i as usize)
                    } else {
                        utils::negative_offset(a, i)
                    };
                    match result {
                        Some(result) => Ok(result.clone()),
                        None => Ok(Json::Null)
                    }
                }
            }
        },
        &Ast::Or(ref lhs, ref rhs) => {
            let left = try!(interpret(data, lhs));
            if utils::is_truthy(&left) {
                Ok(left)
            } else {
                interpret(data, rhs)
            }
        },
        // Returns the resut of RHS if cond yields truthy value.
        &Ast::Condition(ref cond, ref cond_rhs) => {
            let cond_result = try!(interpret(data, cond));
            if utils::is_truthy(&cond_result) {
                interpret(data, cond_rhs)
            } else {
                Ok(Json::Null)
            }
        },
        &Ast::Comparison(ref cmp, ref lhs, ref rhs) => {
            let left = try!(interpret(data, lhs));
            let right = try!(interpret(data, rhs));
            Ok(utils::comparison(cmp, &left, &right))
        },
        // Converts an object into a JSON array of its values.
        &Ast::ObjectValues(ref predicate) => {
            let result = try!(interpret(data, predicate));
            Ok(utils::object_to_array(&result))
        },
        // Passes the results of lhs into rhs if lhs yields an array and
        // each node of lhs that passes through rhs yields a non-null value.
        &Ast::Projection(ref lhs, ref rhs) => {
            match try!(interpret(data, lhs)).as_array() {
                None => Ok(Json::Null),
                Some(left) => {
                    let mut collected = vec!();
                    for element in left {
                        let current = try!(interpret(element, rhs));
                        if !current.is_null() {
                            collected.push(current);
                        }
                    }
                    Ok(Json::Array(collected))
                }
            }
        },
        &Ast::Flatten(ref node) => {
            match try!(interpret(data, node)).as_array() {
                None => Ok(Json::Null),
                Some(a) => {
                    let mut collected = vec!();
                    for element in a {
                        match element {
                            &Json::Array(ref a) => collected.extend(a.iter().cloned()),
                            _ => collected.push(element.clone())
                        }
                    }
                    Ok(Json::Array(collected))
                }
            }
        },
        &Ast::MultiList(ref nodes) => {
            if data.is_null() {
                return Ok(Json::Null);
            }
            let mut collected = vec!();
            for node in nodes {
                collected.push(try!(interpret(data, node)));
            }
            Ok(Json::Array(collected))
        },
        &Ast::MultiHash(ref kvp_list) => {
            if data.is_null() {
                return Ok(Json::Null);
            }
            let mut collected = BTreeMap::new();
            for kvp in kvp_list {
                let key = try!(interpret(data, &kvp.key));
                let value = try!(interpret(data, &kvp.value));
                collected.insert(key.as_string().unwrap().to_string(), value);
            }
            Ok(Json::Object(collected))
        },
        ref node @ _ => panic!(format!("not implemented yet: {:?}", node))
    }
}


#[cfg(test)]
mod tests {
    extern crate rustc_serialize;
    use self::rustc_serialize::json::Json;
    use super::*;
    use ast::{Ast, Comparator};

    #[test] fn interprets_identifier() {
        let ast = Ast::Identifier("foo".to_string());
        let data = Json::from_str("{\"foo\":\"baz\"}").unwrap();
        assert_eq!(Json::String("baz".to_string()), interpret(&data, &ast).unwrap());
    }

    #[test] fn interprets_current_node() {
        let ast = Ast::CurrentNode;
        let data = Json::Boolean(true);
        assert_eq!(Json::Boolean(true), interpret(&data, &ast).unwrap());
    }

    #[test] fn interprets_literal() {
        let ast = Ast::Literal(Json::Boolean(true));
        let data = Json::from_str("{}").unwrap();
        assert_eq!(Json::Boolean(true), interpret(&data, &ast).unwrap());
    }

    #[test] fn interprets_subexpr() {
        let ast = Ast::Subexpr(Box::new(Ast::Identifier("foo".to_string())),
                               Box::new(Ast::Identifier("bar".to_string())));
        let data = Json::from_str("{\"foo\":{\"bar\":\"baz\"}}").unwrap();
        assert_eq!(Json::String("baz".to_string()), interpret(&data, &ast).unwrap());
    }

    #[test] fn interprets_or() {
        let data = Json::Array(vec!(Json::Boolean(false), Json::Boolean(true)));
        assert_eq!(Json::Boolean(true), interpret(&data, &Ast::Index(-1)).unwrap());
        assert_eq!(Json::Boolean(false), interpret(&data, &Ast::Index(-2)).unwrap());
        assert_eq!(Json::Boolean(false), interpret(&data, &Ast::Index(0)).unwrap());
        assert_eq!(Json::Boolean(true), interpret(&data, &Ast::Index(1)).unwrap());
    }

    #[test] fn interprets_index() {
        let data = Json::Array(vec!(Json::Boolean(false), Json::Boolean(true)));
        assert_eq!(Json::Boolean(true), interpret(&data, &Ast::Index(-1)).unwrap());
        assert_eq!(Json::Boolean(false), interpret(&data, &Ast::Index(-2)).unwrap());
        assert_eq!(Json::Boolean(false), interpret(&data, &Ast::Index(0)).unwrap());
        assert_eq!(Json::Boolean(true), interpret(&data, &Ast::Index(1)).unwrap());
    }

    #[test] fn interprets_index_when_not_array_as_null() {
        let ast = Ast::Index(1);
        let data = Json::String("foo".to_string());
        assert_eq!(Json::Null, interpret(&data, &ast).unwrap());
    }

    #[test] fn interprets_or_expr() {
        let ast = Ast::Or(Box::new(Ast::Identifier("bar".to_string())),
                          Box::new(Ast::Identifier("foo".to_string())));
        let data = Json::from_str("{\"foo\":true}").unwrap();
        assert_eq!(Json::Boolean(true), interpret(&data, &ast).unwrap());
    }

    #[test] fn interprets_cond_expr() {
        let ast = Ast::Condition(
            Box::new(Ast::Literal(Json::Boolean(true))),
            Box::new(Ast::Literal(Json::String("foo".to_string()))));
        let data = Json::Null;
        assert_eq!(Json::String("foo".to_string()), interpret(&data, &ast).unwrap());
    }

    #[test] fn interprets_cond_expr_negative() {
        let ast = Ast::Condition(
            Box::new(Ast::Literal(Json::Boolean(false))),
            Box::new(Ast::Literal(Json::String("foo".to_string()))));
        let data = Json::Null;
        assert_eq!(Json::Null, interpret(&data, &ast).unwrap());
    }

    #[test] fn interprets_comparison() {
        // Left, right, result, comparator.
        let cases = vec!(vec!["true", "true", "true", "=="],
                         vec!["true", "false", "false", "=="],
                         vec!["true", "null", "false", "=="],
                         vec!["null", "null", "true", "=="],
                         vec!["10", "20", "false", ">"],
                         vec!["10", "20", "true", "<"]);
        for test_case in cases {
            let cmp = match test_case[3] {
                "==" => Comparator::Eq,
                ">" => Comparator::Gt,
                _ => Comparator::Lt,
            };
            let ast = Ast::Comparison(
                cmp,
                Box::new(Ast::Literal(Json::from_str(test_case[0]).unwrap())),
                Box::new(Ast::Literal(Json::from_str(test_case[1]).unwrap())));
            let result = Json::from_str(test_case[2]).unwrap();
            assert_eq!(result, interpret(&Json::Null, &ast).unwrap());
        }
    }
}
