//! Extracts JSON data by interpreting a JMESPath AST

extern crate rustc_serialize;

use self::rustc_serialize::json::Json;

use ast::{Ast, Comparator, KeyValuePair};

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
                    let actual_index = if *i > 0 {
                        *i as usize
                    } else {
                        negative_offset(a, i)
                    };
                    match a.get(actual_index) {
                        Some(result) => Ok(result.clone()),
                        None => Ok(Json::Null)
                    }
                }
            }
        },
        &Ast::Or(ref lhs, ref rhs) => {
            let left = try!(interpret(data, lhs));
            if is_truthy(&left) {
                Ok(left)
            } else {
                interpret(data, rhs)
            }
        },
        // Returns the resut of RHS if cond yields truthy value.
        &Ast::Condition(ref cond, ref cond_rhs) => {
            let cond_result = try!(interpret(data, cond));
            if is_truthy(&cond_result) {
                interpret(data, cond_rhs)
            } else {
                Ok(Json::Null)
            }
        },
        // Converts an object into a JSON array of its values.
        &Ast::ObjectValues(ref predicate) => {
            let result = try!(interpret(data, predicate));
            Ok(object_to_array(&result))
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
                            &Json::Array(ref values) => {
                                for value in values {
                                    collected.push(value.clone());
                                }
                            },
                            _ => collected.push(element.clone())
                        }
                    }
                    Ok(Json::Array(collected))
                }
            }
        },
        ref node @ _ => panic!(format!("not implemented yet: {:?}", node))
    }
}

fn object_to_array(data: &Json) -> Json {
    match data.as_object() {
        Some(obj) => Json::Array(obj.values().cloned().collect()),
        None => Json::Null
    }
}

fn negative_offset(data: &Vec<Json>, i: &i32) -> usize {
    let len = data.len();
    len.checked_sub(1 + (i.abs() as usize)).unwrap_or(len + 1)
}

fn is_truthy(data: &Json) -> bool {
    match data {
        &Json::Boolean(ref b) if *b == true => true,
        &Json::String(ref s) if s.len() > 0 => true,
        &Json::Array(ref a) if a.len() > 0 => true,
        &Json::Object(ref o) if o.len() > 0 => true,
        _ => false
    }
}

fn jp_type(data: &Json) -> &str {
    match data {
        &Json::Boolean(_) => "boolean",
        &Json::String(_) => "string",
        &Json::I64(_) | &Json::U64(_) | &Json::F64(_) => "number",
        &Json::Array(_) => "array",
        &Json::Object(_) => "object",
        &Json::Null => "null"
    }
}
