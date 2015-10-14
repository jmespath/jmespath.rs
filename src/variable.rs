extern crate rustc_serialize;

use std::cmp::{max, Ordering};
use std::i64;
use std::rc::Rc;
use std::collections::BTreeMap;
use std::iter::Iterator;
use self::rustc_serialize::json::Json;

use ast::{Ast, Comparator};

/// JMESPath variable.
///
/// Note: this enum and implementation is based on rustc-serialize:
/// https://github.com/rust-lang-nursery/rustc-serialize
#[derive(Clone, PartialEq, PartialOrd, Debug)]
pub enum Variable {
    Null,
    String(String),
    Boolean(bool),
    I64(i64),
    U64(u64),
    F64(f64),
    Array(Vec<Rc<Variable>>),
    Object(BTreeMap<String, Rc<Variable>>),
    Expref(Ast)
}

impl Eq for Variable {}

impl Ord for Variable {
    fn cmp(&self, other: &Self) -> Ordering {
        let var_type = self.get_type();
        // Variables of different types are considered equal.
        if var_type != other.get_type() {
            Ordering::Equal
        } else {
            match var_type {
                "string" => self.as_string().unwrap().cmp(other.as_string().unwrap()),
                "number" => self.as_f64().unwrap()
                    .partial_cmp(&other.as_f64().unwrap())
                    .unwrap_or(Ordering::Less),
                _ => Ordering::Equal
            }
        }
    }
}

impl Variable {
    /// Create a new JMESPath variable from a JSON value.
    pub fn from_json(value: &Json) -> Self {
        match value {
            &Json::Null => Variable::Null,
            &Json::Boolean(value) => Variable::Boolean(value),
            &Json::String(ref s) => Variable::String(s.to_string()),
            &Json::I64(i) => Variable::I64(i),
            &Json::F64(f) => Variable::F64(f),
            &Json::U64(u) => Variable::U64(u),
            &Json::Array(ref array) => {
                let mut result: Vec<Rc<Variable>> = vec![];
                for value in array.iter() {
                    result.push(Rc::new(Variable::from_json(value)));
                }
                Variable::Array(result)
            },
            &Json::Object(ref map) => {
                let mut result: BTreeMap<String, Rc<Variable>> = BTreeMap::new();
                for (key, value) in map.iter() {
                    result.insert(key.clone(), Rc::new(Variable::from_json(value)));
                }
                Variable::Object(result)
            }
        }
    }

    /// Create a JMESPath Variable from a JSON encoded string.
    pub fn from_str(s: &str) -> Result<Self, String> {
        Json::from_str(s)
            .map(|value| Self::from_json(&value))
            .or_else(|err| Err(format!("{:?}", err).to_string()))
    }

    /// Converts the Variable value to a JSON value.
    /// If any value in the Variable is an Expref, None is returned.
    pub fn to_json(&self) -> Option<Json> {
        match self {
            &Variable::Null => Some(Json::Null),
            &Variable::Boolean(value) => Some(Json::Boolean(value)),
            &Variable::String(ref s) => Some(Json::String(s.to_string())),
            &Variable::I64(i) => Some(Json::I64(i)),
            &Variable::F64(f) => Some(Json::F64(f)),
            &Variable::U64(u) => Some(Json::U64(u)),
            &Variable::Array(ref array) => {
                let mut result: Vec<Json> = vec![];
                for value in array.iter() {
                    let json_value = Variable::to_json(value);
                    if json_value.is_none() { return None };
                    result.push(json_value.unwrap());
                }
                Some(Json::Array(result))
            },
            &Variable::Object(ref map) => {
                let mut result: BTreeMap<String, Json> = BTreeMap::new();
                for (key, value) in map.iter() {
                    let json_value = Variable::to_json(value);
                    if json_value.is_none() { return None };
                    result.insert(key.clone(), json_value.unwrap());
                }
                Some(Json::Object(result))
            },
            &Variable::Expref(_) => None
        }
    }

    /// Converts the Variable value to a JSON encoded string value.
    /// If any value in the Variable is an Expref, None is returned.
    pub fn to_string(&self) -> Option<String> {
        self.to_json().map(|v| v.to_string())
    }

    /// Returns true if the Variable is an Array. Returns false otherwise.
    pub fn is_array<'a>(&'a self) -> bool {
        self.as_array().is_some()
    }

    /// If the Variable value is an Array, returns the associated vector.
    /// Returns None otherwise.
    pub fn as_array<'a>(&'a self) -> Option<&'a Vec<Rc<Variable>>> {
        match self {
            &Variable::Array(ref array) => Some(&*array),
            _ => None
        }
    }

    /// Returns true if the value is an Object.
    pub fn is_object<'a>(&'a self) -> bool {
        self.as_object().is_some()
    }

    /// If the value is an Object, returns the associated BTreeMap.
    /// Returns None otherwise.
    pub fn as_object<'a>(&'a self) -> Option<&'a BTreeMap<String, Rc<Variable>>> {
        match self {
            &Variable::Object(ref map) => Some(&*map),
            _ => None
        }
    }

    /// Returns true if the value is a String. Returns false otherwise.
    pub fn is_string(&self) -> bool {
        self.as_string().is_some()
    }

    /// If the value is a String, returns the associated str.
    /// Returns None otherwise.
    pub fn as_string(&self) -> Option<&String> {
        match *self {
            Variable::String(ref s) => Some(s),
            _ => None
        }
    }

    /// Returns true if the value is a Number. Returns false otherwise.
    pub fn is_number(&self) -> bool {
        match *self {
            Variable::I64(_) | Variable::U64(_) | Variable::F64(_) => true,
            _ => false,
        }
    }

    /// Returns true if the value is a i64. Returns false otherwise.
    pub fn is_i64(&self) -> bool {
        match *self {
            Variable::I64(_) => true,
            _ => false,
        }
    }

    /// Returns true if the value is a u64. Returns false otherwise.
    pub fn is_u64(&self) -> bool {
        match *self {
            Variable::U64(_) => true,
            _ => false,
        }
    }

    /// Returns true if the value is a f64. Returns false otherwise.
    pub fn is_f64(&self) -> bool {
        match *self {
            Variable::F64(_) => true,
            _ => false,
        }
    }

    /// If the value is a number, return or cast it to a i64.
    /// Returns None otherwise.
    pub fn as_i64(&self) -> Option<i64> {
        match *self {
            Variable::I64(n) => Some(n),
            Variable::U64(n) if n >= i64::MAX as u64 => None,
            Variable::U64(n) => Some(n as i64),
            _ => None
        }
    }

    /// If the value is a number, return or cast it to a u64.
    /// Returns None otherwise.
    pub fn as_u64(&self) -> Option<u64> {
        match *self {
            Variable::I64(n) if n >= 0 => Some(n as u64),
            Variable::U64(n) => Some(n),
            _ => None
        }
    }

    /// If the value is a number, return or cast it to a f64.
    /// Returns None otherwise.
    pub fn as_f64(&self) -> Option<f64> {
        match *self {
            Variable::I64(n) => Some(n as f64),
            Variable::U64(n) => Some(n as f64),
            Variable::F64(n) => Some(n),
            _ => None
        }
    }

    /// Returns true if the value is a Boolean. Returns false otherwise.
    pub fn is_boolean(&self) -> bool {
        self.as_boolean().is_some()
    }

    /// If the value is a Boolean, returns the associated bool.
    /// Returns None otherwise.
    pub fn as_boolean(&self) -> Option<bool> {
        match self {
            &Variable::Boolean(b) => Some(b),
            _ => None
        }
    }

    /// Returns true if the value is a Null. Returns false otherwise.
    pub fn is_null(&self) -> bool {
        self.as_null().is_some()
    }

    /// If the value is a Null, returns ().
    /// Returns None otherwise.
    pub fn as_null(&self) -> Option<()> {
        match self {
            &Variable::Null => Some(()),
            _ => None
        }
    }

    /// Returns true if the value is an expression reference.
    /// Returns false otherwise.
    pub fn is_expref(&self) -> bool {
        self.as_expref().is_some()
    }

    /// If the value is an expression reference, returns the associated Ast node.
    /// Returns None otherwise.
    pub fn as_expref(&self) -> Option<&Ast> {
        match self {
            &Variable::Expref(ref ast) => Some(ast),
            _ => None
        }
    }

    /// Retrieves an index from the Variable if the Variable is an array.
    /// Returns None if not an array or if the index is not present.
    pub fn get_index(&self, index: usize) -> Option<Rc<Variable>> {
        self.as_array()
            .and_then(|array| array.get(index))
            .map(|value| value.clone().clone())
    }

    /// Retrieves an index from the end of a Variable if the Variable is an array.
    /// Returns None if not an array or if the index is not present.
    /// The formula for determining the index position is length - index (i.e., an
    /// index of 0 or 1 is treated as the end of the array).
    pub fn get_negative_index(&self, index: usize) -> Option<Rc<Variable>> {
        self.as_array()
            .and_then(|array| {
                let adjusted_index = max(index, 1);
                if array.len() < adjusted_index {
                    None
                } else {
                    array.get(array.len() - adjusted_index)
                }
            })
            .map(|value| value.clone().clone())
    }

    /// Retrieves a key value from a Variable if the Variable is an object.
    /// Returns None if the Variable is not an object or if the field is not present.
    pub fn get_value(&self, key: &str) -> Option<Rc<Variable>> {
        self.as_object()
            .and_then(|map| map.get(key))
            .map(|value| value.clone().clone())
    }

    /// Converts a Variable::Object to a Variable::Array containing object values.
    /// None is returned if the Variable is not an object.
    pub fn object_values_to_array(&self) -> Option<Variable> {
        self.as_object().map(|map| Variable::Array(map.values().cloned().collect()))
    }

    /// Converts a Variable::Object to a Variable::Array containing object keys.
    /// None is returned if the Variable is not an object.
    pub fn object_keys_to_array(&self) -> Option<Variable> {
        self.as_object()
            .map(|map| Variable::Array(map.keys()
                .map(|key| Rc::new(Variable::String(key.to_string()))).collect()))
    }

    /// Returns true or false based on if the Variable value is considered truthy.
    pub fn is_truthy(&self) -> bool {
        match self {
            &Variable::Boolean(true) => true,
            &Variable::String(ref s) if s.len() > 0 => true,
            &Variable::Array(ref a) if a.len() > 0 => true,
            &Variable::Object(ref o) if o.len() > 0 => true,
            &Variable::I64(_) | &Variable::U64(_) | &Variable::F64(_) => true,
            _ => false
        }
    }

    /// Returns the JMESPath type name of a Variable value.
    pub fn get_type(&self) -> &str {
        match self {
            &Variable::Boolean(_) => "boolean",
            &Variable::String(_) => "string",
            &Variable::I64(_) | &Variable::U64(_) | &Variable::F64(_) => "number",
            &Variable::Array(_) => "array",
            &Variable::Object(_) => "object",
            &Variable::Null => "null",
            &Variable::Expref(_) => "expref"
        }
    }

    /// Compares two Variable values using a comparator.
    pub fn compare(&self, cmp: &Comparator, value: &Variable) -> Option<bool> {
        match cmp {
            &Comparator::Eq => Some(*self == *value),
            &Comparator::Ne => Some(*self != *value),
            &Comparator::Lt if self.is_number() && value.is_number() => Some(*self < *value),
            &Comparator::Lte if self.is_number() && value.is_number() => Some(*self <= *value),
            &Comparator::Gt if self.is_number() && value.is_number() => Some(*self > *value),
            &Comparator::Gte if self.is_number() && value.is_number() => Some(*self >= *value),
            _ => None
        }
    }
}


#[cfg(test)]
mod tests {
    extern crate rustc_serialize;

    use std::rc::Rc;

    use self::rustc_serialize::json::Json;

    use super::*;
    use ast::{Ast, Comparator};

    #[test]
    fn creates_variable_from_json() {
        assert_eq!(Variable::String("Foo".to_string()),
                   Variable::from_json(&Json::String("Foo".to_string())));
        assert_eq!(Variable::Null, Variable::from_json(&Json::Null));
        assert_eq!(Variable::Boolean(false), Variable::from_json(&Json::Boolean(false)));
        assert_eq!(Variable::I64(1), Variable::from_json(&Json::I64(1)));
        assert_eq!(Variable::U64(1), Variable::from_json(&Json::U64(1)));
        assert_eq!(Variable::F64(1.0), Variable::from_json(&Json::F64(1.0)));
        assert_eq!(Variable::U64(1), Variable::from_json(&Json::U64(1)));
        assert_eq!(Variable::F64(1.0), Variable::from_json(&Json::F64(1.0)));
        let array = Variable::from_json(&Json::from_str("[1, [true]]").unwrap());
        assert!(array.is_array());
        assert_eq!(Some(Rc::new(Variable::U64(1))), array.get_index(0));
        let map = Variable::from_json(&Json::from_str("{\"a\": {\"b\": 1}}").unwrap());
        assert!(map.is_object());
        assert_eq!(Some(Rc::new(Variable::U64(1))), map.get_value("a").unwrap().get_value("b"));
    }

    #[test]
    fn creates_variable_from_str() {
        assert_eq!(Ok(Variable::Boolean(true)), Variable::from_str("true"));
        assert_eq!(Err("SyntaxError(\"invalid syntax\", 1, 1)".to_string()),
                   Variable::from_str("abc"));
    }

    #[test]
    fn test_determines_types() {
        assert_eq!("object", Variable::from_str(&"{\"foo\": \"bar\"}").unwrap().get_type());
        assert_eq!("array", Variable::from_str(&"[\"foo\"]").unwrap().get_type());
        assert_eq!("null", Variable::Null.get_type());
        assert_eq!("boolean", Variable::Boolean(true).get_type());
        assert_eq!("string", Variable::String("foo".to_string()).get_type());
        assert_eq!("number", Variable::U64(10).get_type());
    }

    #[test]
    fn test_is_truthy() {
        assert_eq!(true, Variable::from_str(&"{\"foo\": \"bar\"}").unwrap().is_truthy());
        assert_eq!(false, Variable::from_str(&"{}").unwrap().is_truthy());
        assert_eq!(true, Variable::from_str(&"[\"foo\"]").unwrap().is_truthy());
        assert_eq!(false, Variable::from_str(&"[]").unwrap().is_truthy());
        assert_eq!(false, Variable::Null.is_truthy());
        assert_eq!(true, Variable::Boolean(true).is_truthy());
        assert_eq!(false, Variable::Boolean(false).is_truthy());
        assert_eq!(true, Variable::String("foo".to_string()).is_truthy());
        assert_eq!(false, Variable::String("".to_string()).is_truthy());
        assert_eq!(true, Variable::U64(10).is_truthy());
        assert_eq!(true, Variable::U64(0).is_truthy());
    }

    #[test]
    fn test_object_values_to_array() {
        let good = Variable::from_str(&"{\"foo\": \"bar\"}").unwrap();
        assert_eq!(good.object_values_to_array(), Some(Variable::from_str(&"[\"bar\"]").unwrap()));
        let bad = Variable::from_str(&"[\"foo\", \"bar\", \"baz\", \"bam\"]").unwrap();
        assert_eq!(None, bad.object_values_to_array());
    }

    #[test]
    fn test_object_keys_to_array() {
        let good = Variable::from_str(&"{\"foo\": \"bar\"}").unwrap();
        assert_eq!(good.object_keys_to_array(), Some(Variable::from_str(&"[\"foo\"]").unwrap()));
        let bad = Variable::from_str(&"[\"foo\", \"bar\", \"baz\", \"bam\"]").unwrap();
        assert_eq!(None, bad.object_keys_to_array());
    }

    #[test]
    fn test_eq_ne_compare() {
        let l = Variable::String("foo".to_string());
        let r = Variable::String("foo".to_string());
        assert_eq!(Some(true), l.compare(&Comparator::Eq, &r));
        assert_eq!(Some(false), l.compare(&Comparator::Ne, &r));
    }

    #[test]
    fn test_compare() {
        let invalid = Variable::String("foo".to_string());
        let l = Variable::U64(10);
        let r = Variable::U64(20);
        assert_eq!(None, invalid.compare(&Comparator::Gt, &r));
        assert_eq!(Some(false), l.compare(&Comparator::Gt, &r));
        assert_eq!(Some(false), l.compare(&Comparator::Gte, &r));
        assert_eq!(Some(true), r.compare(&Comparator::Gt, &l));
        assert_eq!(Some(true), r.compare(&Comparator::Gte, &l));
        assert_eq!(Some(true), l.compare(&Comparator::Lt, &r));
        assert_eq!(Some(true), l.compare(&Comparator::Lte, &r));
        assert_eq!(Some(false), r.compare(&Comparator::Lt, &l));
        assert_eq!(Some(false), r.compare(&Comparator::Lte, &l));
    }

    #[test]
    fn gets_value_from_object() {
        let var = Variable::from_str("{\"foo\":1}").unwrap();
        assert_eq!(Some(Rc::new(Variable::U64(1))), var.get_value("foo"));
    }

    #[test]
    fn getting_value_from_non_object_is_none() {
        assert_eq!(None, Variable::Boolean(false).get_value("foo"));
    }

    #[test]
    fn getting_index_from_non_array_is_none() {
        assert_eq!(None, Variable::Boolean(false).get_index(2));
    }

    #[test]
    fn gets_index_from_array() {
        let var = Variable::from_str("[1, 2, 3]").unwrap();
        assert_eq!(Some(Rc::new(Variable::U64(1))), var.get_index(0));
        assert_eq!(Some(Rc::new(Variable::U64(2))), var.get_index(1));
        assert_eq!(Some(Rc::new(Variable::U64(3))), var.get_index(2));
        assert_eq!(None, var.get_index(3));
    }

    #[test]
    fn getting_negative_index_from_non_array_is_none() {
        assert_eq!(None, Variable::Boolean(false).get_negative_index(2));
    }

    #[test]
    fn gets_negative_index_from_array() {
        let var = Variable::from_str("[1, 2, 3]").unwrap();
        assert_eq!(Some(Rc::new(Variable::U64(3))), var.get_negative_index(0));
        assert_eq!(Some(Rc::new(Variable::U64(3))), var.get_negative_index(1));
        assert_eq!(Some(Rc::new(Variable::U64(2))), var.get_negative_index(2));
        assert_eq!(Some(Rc::new(Variable::U64(1))), var.get_negative_index(3));
        assert_eq!(None, var.get_negative_index(4));
    }

    #[test]
    fn determines_if_null() {
        assert_eq!(false, Variable::Boolean(true).is_null());
        assert_eq!(true, Variable::Null.is_null());
    }

    #[test]
    fn option_of_null() {
        assert_eq!(Some(()), Variable::Null.as_null());
        assert_eq!(None, Variable::Boolean(true).as_null());
    }

    #[test]
    fn determines_if_boolean() {
        assert_eq!(true, Variable::Boolean(true).is_boolean());
        assert_eq!(false, Variable::Null.is_boolean());
    }

    #[test]
    fn option_of_boolean() {
        assert_eq!(Some(true), Variable::Boolean(true).as_boolean());
        assert_eq!(None, Variable::Null.as_boolean());
    }

    #[test]
    fn determines_if_string() {
        assert_eq!(false, Variable::Boolean(true).is_string());
        assert_eq!(true, Variable::String("foo".to_string()).is_string());
    }

    #[test]
    fn option_of_string() {
        assert_eq!(Some(&"foo".to_string()), Variable::String("foo".to_string()).as_string());
        assert_eq!(None, Variable::Null.as_string());
    }

    #[test]
    fn test_is_number() {
        let value = Variable::from_str("12").unwrap();
        assert!(value.is_number());
    }

    #[test]
    fn test_is_i64() {
        let value = Variable::from_str("-12").unwrap();
        assert!(value.is_i64());

        let value = Variable::from_str("12").unwrap();
        assert!(!value.is_i64());

        let value = Variable::from_str("12.0").unwrap();
        assert!(!value.is_i64());
    }

    #[test]
    fn test_is_u64() {
        let value = Variable::from_str("12").unwrap();
        assert!(value.is_u64());

        let value = Variable::from_str("-12").unwrap();
        assert!(!value.is_u64());

        let value = Variable::from_str("12.0").unwrap();
        assert!(!value.is_u64());
    }

    #[test]
    fn test_is_f64() {
        let value = Variable::from_str("12").unwrap();
        assert!(!value.is_f64());

        let value = Variable::from_str("-12").unwrap();
        assert!(!value.is_f64());

        let value = Variable::from_str("12.0").unwrap();
        assert!(value.is_f64());

        let value = Variable::from_str("-12.0").unwrap();
        assert!(value.is_f64());
    }

    #[test]
    fn test_as_i64() {
        let value = Variable::from_str("-12").unwrap();
        assert_eq!(value.as_i64(), Some(-12));
    }

    #[test]
    fn test_as_u64() {
        let value = Variable::from_str("12").unwrap();
        assert_eq!(value.as_u64(), Some(12));
    }

    #[test]
    fn test_as_f64() {
        let value = Variable::from_str("12.0").unwrap();
        assert_eq!(value.as_f64(), Some(12f64));
    }

    #[test]
    fn test_is_object() {
        let value = Variable::from_str("{}").unwrap();
        assert!(value.is_object());
    }

    #[test]
    fn test_as_object() {
        let value = Variable::from_str("{}").unwrap();
        assert!(value.as_object().is_some());
    }

    #[test]
    fn test_is_array() {
        let value = Variable::from_str("[1, 2, 3]").unwrap();
        assert!(value.is_array());
    }

    #[test]
    fn test_as_array() {
        let value = Variable::from_str("[1, 2, 3]").unwrap();
        let array = value.as_array();
        let expected_length = 3;
        assert!(array.is_some() && array.unwrap().len() == expected_length);
    }

    #[test]
    fn test_converts_to_json() {
        let test_cases = vec![
            "true", "false", "{}", "[]", "0", "null",
            "[1,2,3]", "{\"foo\":[true,false,10,1.1,-5],\"bar\":null}"];
        for case in test_cases {
            let var = Variable::from_str(case).unwrap();
            assert_eq!(Json::from_str(case).unwrap(), var.to_json().unwrap());
        }
    }

    #[test]
    fn test_converting_to_json_with_expref_returns_none() {
        let var = Variable::Expref(Ast::CurrentNode);
        assert!(var.to_json().is_none());
    }

    #[test]
    fn test_converts_to_string() {
        assert_eq!("true", Variable::Boolean(true).to_string().unwrap());
    }

    #[test]
    fn test_is_expref() {
        assert_eq!(true, Variable::Expref(Ast::CurrentNode).is_expref());
        assert_eq!(&Ast::CurrentNode, Variable::Expref(Ast::CurrentNode).as_expref().unwrap());
    }
}
