//! Module for JMESPath runtime variables

extern crate serde;
extern crate serde_json;

use std::collections::BTreeMap;
use std::cmp::Ordering;
use std::fmt;
use std::iter::Iterator;
use std::rc::Rc;
use std::string::ToString;

use self::serde::de;
use self::serde::ser;
use self::serde::Serialize;
use self::serde_json::error::Error;

use super::RcVar;
use super::ast::{Ast, Comparator};

/// JMESPath variable.
///
/// Note: this enum and implementation is based on rustc-serialize:
/// https://github.com/rust-lang-nursery/rustc-serialize
#[derive(Clone, PartialEq, PartialOrd, Debug)]
pub enum Variable {
    Null,
    String(String),
    Bool(bool),
    I64(i64),
    U64(u64),
    F64(f64),
    Array(Vec<RcVar>),
    Object(BTreeMap<String, RcVar>),
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

/// Write the JSON representation of a value, converting expref to a JSON
/// string containing the debug dump of the expref variable.
impl fmt::Display for Variable {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(fmt, "{}", serde_json::to_string(self).unwrap())
    }
}

impl Variable {
    /// Create a JMESPath Variable from a JSON encoded string.
    pub fn from_json(s: &str) -> Result<Self, String> {
        serde_json::from_str::<Variable>(s).map_err(|e| e.to_string())
    }

    /// Create a JMESPath `Variable` from a `serde::se::Serialize` type.
    pub fn from_serialize<T: ser::Serialize>(value: &T) -> Variable {
        let mut ser = Serializer::new();
        value.serialize(&mut ser).ok().unwrap();
        ser.unwrap()
    }

    /// Converts a JMESPath `Variable` to a `serde::de::Deserialize` type.
    pub fn to_deserialize<T: de::Deserialize>(&self) -> Result<T, Error> {
        serde_json::from_value(serde_json::to_value(&self))
    }

    /// Returns true if the Variable is an Array. Returns false otherwise.
    pub fn is_array(&self) -> bool {
        self.as_array().is_some()
    }

    /// If the Variable value is an Array, returns the associated vector.
    /// Returns None otherwise.
    pub fn as_array(&self) -> Option<&Vec<RcVar>> {
        match *self {
            Variable::Array(ref array) => Some(array),
            _ => None
        }
    }

    /// Returns true if the value is an Object.
    pub fn is_object(&self) -> bool {
        self.as_object().is_some()
    }

    /// If the value is an Object, returns the associated BTreeMap.
    /// Returns None otherwise.
    pub fn as_object(&self) -> Option<&BTreeMap<String, RcVar>> {
        match *self {
            Variable::Object(ref map) => Some(map),
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
            Variable::F64(_) | Variable::I64(_) | Variable::U64(_) => true,
            _ => false,
        }
    }

    /// If the value is a number, return or cast it to a f64.
    /// Returns None otherwise.
    pub fn as_f64(&self) -> Option<f64> {
        match *self {
            Variable::F64(n) => Some(n),
            Variable::U64(n) => Some(n as f64),
            Variable::I64(n) => Some(n as f64),
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
        match *self {
            Variable::Bool(b) => Some(b),
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
        match *self {
            Variable::Null => Some(()),
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
        match *self {
            Variable::Expref(ref ast) => Some(ast),
            _ => None
        }
    }

    /// If the `Value` is an Object, returns the value associated with the provided key.
    /// Otherwise, returns None.
    pub fn find(&self, key: &str) -> Option<RcVar> {
        self.as_object().and_then(|map| map.get(key)).cloned()
    }

    /// Returns true or false based on if the Variable value is considered truthy.
    pub fn is_truthy(&self) -> bool {
        match *self {
            Variable::Bool(true) => true,
            Variable::String(ref s) if !s.is_empty() => true,
            Variable::Array(ref a) if !a.is_empty() => true,
            Variable::Object(ref o) if !o.is_empty() => true,
            Variable::F64(_) => true,
            Variable::I64(_) => true,
            Variable::U64(_) => true,
            _ => false
        }
    }

    /// Returns the JMESPath type name of a Variable value.
    pub fn get_type(&self) -> &str {
        match *self {
            Variable::Bool(_) => "boolean",
            Variable::String(_) => "string",
            Variable::F64(_) | Variable::U64(_) | Variable::I64(_)=> "number",
            Variable::Array(_) => "array",
            Variable::Object(_) => "object",
            Variable::Null => "null",
            Variable::Expref(_) => "expref"
        }
    }

    /// Compares two Variable values using a comparator.
    pub fn compare(&self, cmp: &Comparator, value: &Variable) -> Option<bool> {
        match *cmp {
            Comparator::Eq => Some(*self == *value),
            Comparator::Ne => Some(*self != *value),
            Comparator::Lt if self.is_number() && value.is_number() => Some(*self < *value),
            Comparator::Lte if self.is_number() && value.is_number() => Some(*self <= *value),
            Comparator::Gt if self.is_number() && value.is_number() => Some(*self > *value),
            Comparator::Gte if self.is_number() && value.is_number() => Some(*self >= *value),
            _ => None
        }
    }
}

/// Serde deserialization for Variable
impl de::Deserialize for Variable {
    #[inline]
    fn deserialize<D>(deserializer: &mut D) -> Result<Variable, D::Error>
        where D: de::Deserializer,
    {
        struct VariableVisitor;

        impl de::Visitor for VariableVisitor {
            type Value = Variable;

            #[inline]
            fn visit_bool<E>(&mut self, value: bool) -> Result<Variable, E> {
                Ok(Variable::Bool(value))
            }

            #[inline]
            fn visit_i64<E>(&mut self, value: i64) -> Result<Variable, E> {
                if value < 0 {
                    Ok(Variable::I64(value))
                } else {
                    Ok(Variable::U64(value as u64))
                }
            }

            #[inline]
            fn visit_u64<E>(&mut self, value: u64) -> Result<Variable, E> {
                Ok(Variable::U64(value))
            }

            #[inline]
            fn visit_f64<E>(&mut self, value: f64) -> Result<Variable, E> {
                Ok(Variable::F64(value))
            }

            #[inline]
            fn visit_str<E>(&mut self, value: &str) -> Result<Variable, E>
                where E: de::Error,
            {
                self.visit_string(String::from(value))
            }

            #[inline]
            fn visit_string<E>(&mut self, value: String) -> Result<Variable, E> {
                Ok(Variable::String(value))
            }

            #[inline]
            fn visit_none<E>(&mut self) -> Result<Variable, E> {
                Ok(Variable::Null)
            }

            #[inline]
            fn visit_some<D>(&mut self, deserializer: &mut D) -> Result<Variable, D::Error>
                where D: de::Deserializer,
            {
                de::Deserialize::deserialize(deserializer)
            }

            #[inline]
            fn visit_unit<E>(&mut self) -> Result<Variable, E> {
                Ok(Variable::Null)
            }

            #[inline]
            fn visit_seq<V>(&mut self, visitor: V) -> Result<Variable, V::Error>
                where V: de::SeqVisitor,
            {
                let values = try!(de::impls::VecVisitor::new().visit_seq(visitor));
                Ok(Variable::Array(values))
            }

            #[inline]
            fn visit_map<V>(&mut self, visitor: V) -> Result<Variable, V::Error>
                where V: de::MapVisitor,
            {
                let values = try!(de::impls::BTreeMapVisitor::new().visit_map(visitor));
                Ok(Variable::Object(values))
            }
        }

        deserializer.visit(VariableVisitor)
    }
}

/// Serde serialization for Variable
impl ser::Serialize for Variable {
    #[inline]
    fn serialize<S>(&self, serializer: &mut S) -> Result<(), S::Error>
        where S: ser::Serializer
    {
        match *self {
            Variable::Null => serializer.visit_unit(),
            Variable::Bool(v) => serializer.visit_bool(v),
            Variable::I64(v) => serializer.visit_i64(v),
            Variable::U64(v) => serializer.visit_u64(v),
            Variable::F64(v) => serializer.visit_f64(v),
            Variable::String(ref v) => serializer.visit_str(&v),
            Variable::Array(ref v) => v.serialize(serializer),
            Variable::Object(ref v) => v.serialize(serializer),
            Variable::Expref(ref e) => serializer.visit_str(&format!("<Expref({:?})>", e)),
        }
    }
}

#[derive(Debug)]
enum State {
    Value(Variable),
    Array(Vec<RcVar>),
    Object(BTreeMap<String, RcVar>),
}

/// Create a `serde::Serializer` that serializes a `Serialize`e into a `Variable`.
/// Note that this is based on the Serializer for serde's JSON Value.
/// The Serializer is used to serialize JMESPath variables directly without needing
/// any intermediate types.
pub struct Serializer {
    state: Vec<State>,
}

impl Serializer {
    /// Construct a new `Serializer`.
    pub fn new() -> Serializer {
        Serializer {
            state: Vec::with_capacity(4),
        }
    }

    /// Unwrap the `Serializer` and return the `Value`.
    pub fn unwrap(mut self) -> Variable {
        match self.state.pop().unwrap() {
            State::Value(value) => value,
            state => panic!("expected value, found {:?}", state),
        }
    }
}

impl ser::Serializer for Serializer {
    type Error = ();

    #[inline]
    fn visit_some<V>(&mut self, value: V) -> Result<(), ()> where V: ser::Serialize {
        value.serialize(self)
    }

    #[inline]
    fn visit_bool(&mut self, value: bool) -> Result<(), ()> {
        self.state.push(State::Value(Variable::Bool(value)));
        Ok(())
    }

    #[inline]
    fn visit_i64(&mut self, value: i64) -> Result<(), ()> {
        if value < 0 {
            self.state.push(State::Value(Variable::I64(value)));
        } else {
            self.state.push(State::Value(Variable::U64(value as u64)));
        }
        Ok(())
    }

    #[inline]
    fn visit_u64(&mut self, value: u64) -> Result<(), ()> {
        self.state.push(State::Value(Variable::U64(value)));
        Ok(())
    }

    #[inline]
    fn visit_f64(&mut self, value: f64) -> Result<(), ()> {
        self.state.push(State::Value(Variable::F64(value as f64)));
        Ok(())
    }

    #[inline]
    fn visit_char(&mut self, value: char) -> Result<(), ()> {
        let s = value.to_string();
        self.visit_str(&s)
    }

    #[inline]
    fn visit_str(&mut self, value: &str) -> Result<(), ()> {
        self.state.push(State::Value(Variable::String(String::from(value))));
        Ok(())
    }

    #[inline]
    fn visit_none(&mut self) -> Result<(), ()> {
        self.visit_unit()
    }

    #[inline]
    fn visit_unit(&mut self) -> Result<(), ()> {
        self.state.push(State::Value(Variable::Null));
        Ok(())
    }

    #[inline]
    fn visit_unit_variant(&mut self,
                          _name: &str,
                          _variant_index: usize,
                          variant: &str) -> Result<(), ()> {
        let mut values = BTreeMap::new();
        values.insert(String::from(variant), Rc::new(Variable::Array(vec![])));
        self.state.push(State::Value(Variable::Object(values)));
        Ok(())
    }

    #[inline]
    fn visit_newtype_variant<T>(&mut self,
                                _name: &str,
                                _variant_index: usize,
                                variant: &str,
                                value: T) -> Result<(), ()>
                                where T: ser::Serialize {
        let mut values = BTreeMap::new();
        values.insert(String::from(variant), Rc::new(Variable::from_serialize(&value)));
        self.state.push(State::Value(Variable::Object(values)));
        Ok(())
    }

    #[inline]
    fn visit_seq<V>(&mut self, mut visitor: V) -> Result<(), ()> where V: ser::SeqVisitor {
        let len = visitor.len().unwrap_or(0);
        let values = Vec::with_capacity(len);
        self.state.push(State::Array(values));
        while let Some(()) = try!(visitor.visit(self)) { }
        let values = match self.state.pop().unwrap() {
            State::Array(values) => values,
            state => panic!("Expected array, found {:?}", state),
        };
        self.state.push(State::Value(Variable::Array(values)));
        Ok(())
    }

    #[inline]
    fn visit_tuple_variant<V>(&mut self,
                              _name: &str,
                              _variant_index: usize,
                              variant: &str,
                              visitor: V) -> Result<(), ()>
                              where V: ser::SeqVisitor {
        try!(self.visit_seq(visitor));
        let value = match self.state.pop().unwrap() {
            State::Value(value) => value,
            state => panic!("expected value, found {:?}", state),
        };
        let mut object = BTreeMap::new();
        object.insert(String::from(variant), Rc::new(value));
        self.state.push(State::Value(Variable::Object(object)));
        Ok(())
    }

    #[inline]
    fn visit_seq_elt<T>(&mut self, value: T) -> Result<(), ()> where T: ser::Serialize {
        try!(value.serialize(self));
        let value = match self.state.pop().unwrap() {
            State::Value(value) => value,
            state => panic!("expected value, found {:?}", state),
        };
        match *self.state.last_mut().unwrap() {
            State::Array(ref mut values) => { values.push(Rc::new(value)); }
            ref state => panic!("expected array, found {:?}", state),
        }
        Ok(())
    }

    #[inline]
    fn visit_map<V>(&mut self, mut visitor: V) -> Result<(), ()> where V: ser::MapVisitor {
        let values = BTreeMap::new();

        self.state.push(State::Object(values));

        while let Some(()) = try!(visitor.visit(self)) { }

        let values = match self.state.pop().unwrap() {
            State::Object(values) => values,
            state => panic!("expected object, found {:?}", state),
        };

        self.state.push(State::Value(Variable::Object(values)));

        Ok(())
    }

    #[inline]
    fn visit_struct_variant<V>(&mut self,
                               _name: &str,
                               _variant_index: usize,
                               variant: &str,
                               visitor: V) -> Result<(), ()>
                               where V: ser::MapVisitor {
        try!(self.visit_map(visitor));
        let value = match self.state.pop().unwrap() {
            State::Value(value) => value,
            state => panic!("expected value, found {:?}", state),
        };

        let mut object = BTreeMap::new();
        object.insert(String::from(variant), Rc::new(value));
        self.state.push(State::Value(Variable::Object(object)));
        Ok(())
    }

    #[inline]
    fn visit_map_elt<K, V>(&mut self,
                           key: K,
                           value: V) -> Result<(), ()>
                           where K: ser::Serialize,
                           V: ser::Serialize {
        try!(key.serialize(self));
        let key = match self.state.pop().unwrap() {
            State::Value(Variable::String(value)) => value,
            state => panic!("expected key, found {:?}", state),
        };

        try!(value.serialize(self));
        let value = match self.state.pop().unwrap() {
            State::Value(value) => value,
            state => panic!("expected value, found {:?}", state),
        };

        match *self.state.last_mut().unwrap() {
            State::Object(ref mut values) => { values.insert(key, Rc::new(value)); },
            ref state => panic!("expected object, found {:?}", state),
        }
        Ok(())
    }

    #[inline]
    fn format() -> &'static str {
        "jmespath"
    }
}

#[cfg(test)]
mod tests {
    use std::rc::Rc;
    use std::collections::BTreeMap;
    use super::serde_json::{self, Value};
    use super::Variable;
    use ast::{Ast, Comparator};

    #[test]
    fn creates_variable_from_str() {
        assert_eq!(Ok(Variable::Bool(true)), Variable::from_json("true"));
        assert_eq!(Err("\"expected value\" at line 1 column 1".to_string()),
                   Variable::from_json("abc"));
    }

    #[test]
    fn test_determines_types() {
         assert_eq!("object", Variable::from_json(&"{\"foo\": \"bar\"}").unwrap().get_type());
         assert_eq!("array", Variable::from_json(&"[\"foo\"]").unwrap().get_type());
         assert_eq!("null", Variable::Null.get_type());
         assert_eq!("boolean", Variable::Bool(true).get_type());
         assert_eq!("string", Variable::String("foo".to_string()).get_type());
         assert_eq!("number", Variable::F64(1.0).get_type());
         assert_eq!("number", Variable::I64(1 as i64).get_type());
         assert_eq!("number", Variable::U64(1).get_type());
    }

    #[test]
    fn test_is_truthy() {
        assert_eq!(true, Variable::from_json(&"{\"foo\": \"bar\"}").unwrap().is_truthy());
        assert_eq!(false, Variable::from_json(&"{}").unwrap().is_truthy());
        assert_eq!(true, Variable::from_json(&"[\"foo\"]").unwrap().is_truthy());
        assert_eq!(false, Variable::from_json(&"[]").unwrap().is_truthy());
        assert_eq!(false, Variable::Null.is_truthy());
        assert_eq!(true, Variable::Bool(true).is_truthy());
        assert_eq!(false, Variable::Bool(false).is_truthy());
        assert_eq!(true, Variable::String("foo".to_string()).is_truthy());
        assert_eq!(false, Variable::String("".to_string()).is_truthy());
        assert_eq!(true, Variable::F64(10.0).is_truthy());
        assert_eq!(true, Variable::U64(0).is_truthy());
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
        let l = Variable::F64(10.0);
        let r = Variable::F64(20.0);
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
        let var = Variable::from_json("{\"foo\":1}").unwrap();
        assert_eq!(Some(Rc::new(Variable::U64(1))), var.find("foo"));
    }

    #[test]
    fn getting_value_from_non_object_is_none() {
        assert_eq!(None, Variable::Bool(false).find("foo"));
    }

    #[test]
    fn determines_if_null() {
        assert_eq!(false, Variable::Bool(true).is_null());
        assert_eq!(true, Variable::Null.is_null());
    }

    #[test]
    fn option_of_null() {
        assert_eq!(Some(()), Variable::Null.as_null());
        assert_eq!(None, Variable::Bool(true).as_null());
    }

    #[test]
    fn determines_if_boolean() {
        assert_eq!(true, Variable::Bool(true).is_boolean());
        assert_eq!(false, Variable::Null.is_boolean());
    }

    #[test]
    fn option_of_boolean() {
        assert_eq!(Some(true), Variable::Bool(true).as_boolean());
        assert_eq!(None, Variable::Null.as_boolean());
    }

    #[test]
    fn determines_if_string() {
        assert_eq!(false, Variable::Bool(true).is_string());
        assert_eq!(true, Variable::String("foo".to_string()).is_string());
    }

    #[test]
    fn option_of_string() {
        assert_eq!(Some(&"foo".to_string()), Variable::String("foo".to_string()).as_string());
        assert_eq!(None, Variable::Null.as_string());
    }

    #[test]
    fn test_is_number() {
        let value = Variable::from_json("12").unwrap();
        assert!(value.is_number());
    }

    #[test]
    fn test_as_f64() {
        let value = Variable::from_json("12.0").unwrap();
        assert_eq!(value.as_f64(), Some(12f64));
    }

    #[test]
    fn test_is_object() {
        let value = Variable::from_json("{}").unwrap();
        assert!(value.is_object());
    }

    #[test]
    fn test_as_object() {
        let value = Variable::from_json("{}").unwrap();
        assert!(value.as_object().is_some());
    }

    #[test]
    fn test_is_array() {
        let value = Variable::from_json("[1, 2, 3]").unwrap();
        assert!(value.is_array());
    }

    #[test]
    fn test_as_array() {
        let value = Variable::from_json("[1, 2, 3]").unwrap();
        let array = value.as_array();
        let expected_length = 3;
        assert!(array.is_some() && array.unwrap().len() == expected_length);
    }

    #[test]
    fn test_is_expref() {
        assert_eq!(true, Variable::Expref(Ast::Identity {offset: 0}).is_expref());
        assert_eq!(&Ast::Identity {offset: 0},
            Variable::Expref(Ast::Identity {offset: 0}).as_expref().unwrap());
    }

    #[test]
    fn test_parses_json_scalar() {
        assert_eq!(Variable::Null, Variable::from_json("null").unwrap());
        assert_eq!(Variable::Bool(true), Variable::from_json("true").unwrap());
        assert_eq!(Variable::Bool(false), Variable::from_json("false").unwrap());
        assert_eq!(Variable::U64(1), Variable::from_json("1").unwrap());
        assert_eq!(Variable::I64(-1), Variable::from_json("-1").unwrap());
        assert_eq!(Variable::F64(1.5), Variable::from_json("1.5").unwrap());
        assert_eq!(Variable::String("abc".to_string()), Variable::from_json("\"abc\"").unwrap());
    }

    #[test]
    fn test_parses_json_array() {
        let var = Variable::from_json("[null, true, [\"a\"]]").unwrap();
        assert_eq!(var, Variable::Array(vec![
            Rc::new(Variable::Null),
            Rc::new(Variable::Bool(true)),
            Rc::new(Variable::Array(vec![
                Rc::new(Variable::String("a".to_string()))
            ]))
        ]))
    }

    #[test]
    fn test_parses_json_object() {
        let var = Variable::from_json("{\"a\": 1, \"b\": {\"c\": true}}").unwrap();
        let mut expected = BTreeMap::new();
        let mut sub_obj = BTreeMap::new();
        expected.insert("a".to_string(), Rc::new(Variable::U64(1)));
        sub_obj.insert("c".to_string(), Rc::new(Variable::Bool(true)));
        expected.insert("b".to_string(), Rc::new(Variable::Object(sub_obj)));
        assert_eq!(var, Variable::Object(expected));
    }

    #[test]
    fn test_converts_to_json() {
        let var = Variable::from_json("true").unwrap();
        let val = serde_json::to_value(&var);
        assert_eq!(Value::Bool(true), val);
        let round_trip = serde_json::from_value::<Variable>(val).unwrap();
        assert_eq!(Variable::Bool(true), round_trip);
        // Try a more complex shape
        let var = Variable::from_json("[\"a\"]").unwrap();
        let val = serde_json::to_value(&var);
        assert_eq!(Value::Array(vec![Value::String("a".to_string())]), val);
        let round_trip = serde_json::from_value::<Variable>(val).unwrap();
        assert_eq!(Variable::Array(vec![Rc::new(Variable::String("a".to_string()))]), round_trip);
    }

    /// Converting an expression variable to a string is a special case.
    #[test]
    fn test_converts_to_string() {
        assert_eq!("true", Variable::Bool(true).to_string());
        assert_eq!("[true]", Variable::from_json("[true]").unwrap().to_string());
        let v = Variable::Expref(Ast::Identity { offset: 0 });
        assert_eq!("\"<Expref(Identity { offset: 0 })>\"", v.to_string());
    }

    /// Tests that the Serde serialization directly to Variable works correctly.
    #[test]
    fn test_creates_variable_from_scalar_serialization() {
        assert_eq!("\"foo\"", Variable::from_serialize(&"foo").to_string());
        assert_eq!("\"foo\"", Variable::from_serialize(&"foo".to_string()).to_string());
        assert_eq!("\"f\"", Variable::from_serialize(&'f').to_string());
        assert_eq!("1", Variable::from_serialize(&1).to_string());
        assert_eq!("1", Variable::from_serialize(&(1 as i64)).to_string());
        assert_eq!("-1", Variable::from_serialize(&-1).to_string());
        assert_eq!("1.5", Variable::from_serialize(&1.5).to_string());
        assert_eq!("true", Variable::from_serialize(&true).to_string());
        assert_eq!("false", Variable::from_serialize(&false).to_string());
        assert_eq!("null", Variable::from_serialize(&()).to_string());
        let null_val: Option<bool> = None;
        assert_eq!("null", Variable::from_serialize(&null_val).to_string());
    }

    #[test]
    fn test_creates_variable_from_vec_serialization() {
        let empty_vec: Vec<String> = Vec::new();
        assert_eq!("[]", Variable::from_serialize(&empty_vec).to_string());
        assert_eq!("[\"abc\"]", Variable::from_serialize(&vec!["abc"]).to_string());
        let s_vec: Vec<Vec<&'static str>> = vec![vec!["foo", "baz"], vec!["bar"]];
        assert_eq!("[[\"foo\",\"baz\"],[\"bar\"]]", Variable::from_serialize(&s_vec).to_string());
    }

    #[test]
    fn test_creates_variable_from_map_serialization() {
        let empty_map: BTreeMap<String, String> = BTreeMap::new();
        assert_eq!("{}", Variable::from_serialize(&empty_map).to_string());
        let mut b_map: BTreeMap<&'static str, bool> = BTreeMap::new();
        b_map.insert("foo", true);
        assert_eq!("{\"foo\":true}", Variable::from_serialize(&b_map).to_string());
    }

    #[test]
    fn test_creates_variable_from_tuple_serialization() {
        let t = (true, false);
        assert_eq!("[true,false]", Variable::from_serialize(&t).to_string());
    }

    #[test]
    fn test_can_round_trip_to_and_from_value() {
        let value1 = Value::Array(vec![Value::Bool(true), Value::Bool(false)]);
        let variable = Variable::from_serialize(&value1);
        assert_eq!("[true,false]", variable.to_string());
        let value2: Value = variable.to_deserialize().unwrap();
        assert_eq!(value1, value2);
        assert_eq!("[true,false]", serde_json::to_string(&value2).unwrap());
    }
}
