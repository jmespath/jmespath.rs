//! Module for JMESPath runtime variables
//!
//! Note: currently requires the nightly compiler for specialization.

extern crate serde;
extern crate serde_json;

use serde::{de, ser};
use serde_json::value::Value;
use serde_json::error::Error;
use std::collections::BTreeMap;
use std::cmp::{max, Ordering};
use std::fmt;
use std::iter::Iterator;
use std::string::ToString;

use IntoJmespath;
use RcVar;
use ast::{Ast, Comparator};

/// JMESPath types.
#[derive(Debug, PartialEq, PartialOrd, Eq, Ord)]
pub enum JmespathType {
    Null,
    String,
    Number,
    Boolean,
    Array,
    Object,
    Expref,
}

impl fmt::Display for JmespathType {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(fmt, "{}", match *self {
            JmespathType::Null => "null",
            JmespathType::String => "string",
            JmespathType::Number => "number",
            JmespathType::Boolean => "boolean",
            JmespathType::Array => "array",
            JmespathType::Object => "object",
            JmespathType::Expref => "expref",
        })
    }
}

/// JMESPath variable.
#[derive(Clone, Debug)]
pub enum Variable {
    Null,
    String(String),
    Bool(bool),
    Number(f64),
    Array(Vec<RcVar>),
    Object(BTreeMap<String, RcVar>),
    Expref(Ast),
}

impl Eq for Variable {}

/// Compares two floats for equality.
///
/// Allows for equivalence of floating point numbers like
/// 0.7100000000000002 and 0.71.
///
/// Based on http://stackoverflow.com/a/4915891
fn float_eq(a: f64, b: f64) -> bool {
    use std::f64;
    let abs_a = a.abs();
    let abs_b = b.abs();
    let diff = (a - b).abs();
    if a == b {
        true
    } else if !a.is_normal() || !b.is_normal() {
        // a or b is zero or both are extremely close to it
        // relative error is less meaningful here.
        diff < (f64::EPSILON * f64::MIN_POSITIVE)
    } else {
        // use relative error.
        diff / (abs_a + abs_b) < f64::EPSILON
    }
}

/// Implement PartialEq for looser floating point comparisons.
impl PartialEq for Variable {
    fn eq(&self, other: &Variable) -> bool {
        if self.get_type() != other.get_type() {
            false
        } else {
            match *self {
                Variable::Number(a) => float_eq(a, other.as_number().unwrap()),
                Variable::String(ref s) => s == other.as_string().unwrap(),
                Variable::Bool(b) => b == other.as_boolean().unwrap(),
                Variable::Array(ref a) => a == other.as_array().unwrap(),
                Variable::Object(ref o) => o == other.as_object().unwrap(),
                Variable::Expref(ref e) => e == other.as_expref().unwrap(),
                Variable::Null => true,
            }
        }
    }
}

/// Implement PartialOrd so that Ast can be in the PartialOrd of Variable.
impl PartialOrd<Variable> for Variable {
    fn partial_cmp(&self, other: &Variable) -> Option<Ordering> {
        Some(self.cmp(other))
    }

    fn lt(&self, other: &Variable) -> bool {
        self.cmp(other) == Ordering::Less
    }

    fn le(&self, other: &Variable) -> bool {
        let ordering = self.cmp(other);
        ordering == Ordering::Equal || ordering == Ordering::Less
    }

    fn gt(&self, other: &Variable) -> bool {
        self.cmp(other) == Ordering::Greater
    }

    fn ge(&self, other: &Variable) -> bool {
        let ordering = self.cmp(other);
        ordering == Ordering::Equal || ordering == Ordering::Greater
    }
}

impl Ord for Variable {
    fn cmp(&self, other: &Self) -> Ordering {
        let var_type = self.get_type();
        // Variables of different types are considered equal.
        if var_type != other.get_type() {
            Ordering::Equal
        } else {
            match var_type {
                JmespathType::String => self.as_string().unwrap().cmp(other.as_string().unwrap()),
                JmespathType::Number => {
                    self.as_number().unwrap()
                        .partial_cmp(&other.as_number().unwrap())
                        .unwrap_or(Ordering::Less)
                },
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

/// Generic way of converting a Map in a Value to a Variable.
fn convert_map<'a, T>(value: T) -> Variable where T: Iterator<Item=(&'a String, &'a Value)> {
    let mut map: BTreeMap<String, RcVar> = BTreeMap::new();
    for kvp in value {
        map.insert(kvp.0.to_owned(), kvp.1.into_jmespath());
    }
    Variable::Object(map)
}

/// Convert a borrowed Value to a Variable.
impl<'a> From<&'a Value> for Variable {
    fn from(value: &'a Value) -> Variable {
        match *value {
            Value::String(ref s) => Variable::String(s.to_owned()),
            Value::Null => Variable::Null,
            Value::Bool(b) => Variable::Bool(b),
            Value::U64(n) => Variable::Number(n as f64),
            Value::F64(n) => Variable::Number(n),
            Value::I64(n) => Variable::Number(n as f64),
            Value::Object(ref values) => convert_map(values.iter()),
            Value::Array(ref values) => {
                Variable::Array(values.iter().map(|v| v.into_jmespath()).collect())
            },
        }
    }
}

/// Slightly optimized method for converting from an owned Value.
impl From<Value> for Variable {
    fn from(value: Value) -> Variable {
        match value {
            Value::String(s) => Variable::String(s),
            Value::Null => Variable::Null,
            Value::Bool(b) => Variable::Bool(b),
            Value::U64(n) => Variable::Number(n as f64),
            Value::F64(n) => Variable::Number(n),
            Value::I64(n) => Variable::Number(n as f64),
            Value::Object(ref values) => convert_map(values.iter()),
            Value::Array(mut values) => {
                Variable::Array(values.drain(..).map(|v| v.into_jmespath()).collect())
            },
        }
    }
}

impl Variable {
    /// Create a JMESPath Variable from a JSON encoded string.
    pub fn from_json(s: &str) -> Result<Self, String> {
        serde_json::from_str::<Variable>(s).map_err(|e| e.to_string())
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
            Variable::Number(_) => true,
            _ => false,
        }
    }

    /// If the value is a number, return or cast it to a f64.
    /// Returns None otherwise.
    pub fn as_number(&self) -> Option<f64> {
        match *self {
            Variable::Number(f) => Some(f),
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

    /// If the value is an object, returns the value associated with the provided key.
    /// Otherwise, returns Null.
    pub fn get_field(&self, key: &str) -> RcVar {
        if let Variable::Object(ref map) = *self {
            if let Some(result) = map.get(key) {
                return result.clone();
            }
        }
        RcVar::new(Variable::Null)
    }

    /// If the value is an array, then gets an array value by index. Otherwise returns Null.
    pub fn get_index(&self, index: usize) -> RcVar {
        if let Variable::Array(ref array) = *self {
            if let Some(result) = array.get(index) {
                return result.clone();
            }
        }
        RcVar::new(Variable::Null)
    }

    /// Retrieves an index from the end of an array.
    ///
    /// Returns Null if not an array or if the index is not present.
    /// The formula for determining the index position is length - index (i.e., an
    /// index of 0 or 1 is treated as the end of the array).
    pub fn get_negative_index(&self, index: usize) -> RcVar {
        if let Variable::Array(ref array) = *self {
            let adjusted_index = max(index, 1);
            if array.len() >= adjusted_index {
                return array[array.len() - adjusted_index].clone();
            }
        }
        RcVar::new(Variable::Null)
    }

    /// Returns true or false based on if the Variable value is considered truthy.
    pub fn is_truthy(&self) -> bool {
        match *self {
            Variable::Bool(true) => true,
            Variable::String(ref s) if !s.is_empty() => true,
            Variable::Array(ref a) if !a.is_empty() => true,
            Variable::Object(ref o) if !o.is_empty() => true,
            Variable::Number(_) => true,
            _ => false
        }
    }

    /// Returns the JMESPath type name of a Variable value.
    pub fn get_type(&self) -> JmespathType {
        match *self {
            Variable::Bool(_) => JmespathType::Boolean,
            Variable::String(_) => JmespathType::String,
            Variable::Number(_) => JmespathType::Number,
            Variable::Array(_) => JmespathType::Array,
            Variable::Object(_) => JmespathType::Object,
            Variable::Null => JmespathType::Null,
            Variable::Expref(_) => JmespathType::Expref,
        }
    }

    /// Compares two Variable values using a comparator.
    pub fn compare(&self, cmp: &Comparator, value: &Variable) -> Option<bool> {
        // Ordering requires numeric values.
        if !(*cmp == Comparator::Equal || *cmp == Comparator::NotEqual) {
            if !self.is_number() || !value.is_number() {
                return None;
            }
        }
        match *cmp {
            Comparator::Equal => Some(*self == *value),
            Comparator::NotEqual => Some(*self != *value),
            Comparator::LessThan => Some(*self < *value),
            Comparator::LessThanEqual => Some(*self <= *value),
            Comparator::GreaterThan => Some(*self > *value),
            Comparator::GreaterThanEqual => Some(*self >= *value),
        }
    }

    /// Returns a slice of the variable if the variable is an array.
    pub fn slice(&self, start: &Option<i32>, stop: &Option<i32>, step: i32)
        -> Option<Vec<RcVar>>
    {
        self.as_array().map(|a| slice(a, start, stop, step))
    }
}

/* ------------------------------------------
 * Variable slicing implementation
 * ------------------------------------------ */

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

/* ------------------------------------------
 * Serde Variable deserialization
 * ------------------------------------------ */

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
                Ok(Variable::Number(value as f64))
            }

            #[inline]
            fn visit_u64<E>(&mut self, value: u64) -> Result<Variable, E> {
                Ok(Variable::Number(value as f64))
            }

            #[inline]
            fn visit_f64<E>(&mut self, value: f64) -> Result<Variable, E> {
                Ok(Variable::Number(value))
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

        deserializer.deserialize(VariableVisitor)
    }
}

/* ------------------------------------------
 * Serde Variable serialization
 * ------------------------------------------ */

/// Serde serialization for Variable
impl ser::Serialize for Variable {
    #[inline]
    fn serialize<S>(&self, serializer: &mut S) -> Result<(), S::Error>
        where S: ser::Serializer
    {
        match *self {
            Variable::Null => serializer.serialize_unit(),
            Variable::Bool(v) => serializer.serialize_bool(v),
            Variable::Number(v) => serializer.serialize_f64(v),
            Variable::String(ref v) => serializer.serialize_str(&v),
            Variable::Array(ref v) => v.serialize(serializer),
            Variable::Object(ref v) => v.serialize(serializer),
            Variable::Expref(ref e) => serializer.serialize_str(&format!("__Expref__{:?}", e)),
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
    type Error = Error;

    #[inline]
    fn serialize_bool(&mut self, value: bool) -> Result<(), Error> {
        self.state.push(State::Value(Variable::Bool(value)));
        Ok(())
    }

    #[inline]
    fn serialize_i64(&mut self, value: i64) -> Result<(), Error> {
        self.state.push(State::Value(Variable::Number(value as f64)));
        Ok(())
    }

    #[inline]
    fn serialize_u64(&mut self, value: u64) -> Result<(), Error> {
        self.state.push(State::Value(Variable::Number(value as f64)));
        Ok(())
    }

    #[inline]
    fn serialize_f64(&mut self, value: f64) -> Result<(), Error> {
        self.state.push(State::Value(Variable::Number(value)));
        Ok(())
    }

    #[inline]
    fn serialize_char(&mut self, value: char) -> Result<(), Error> {
        let s = value.to_string();
        self.serialize_str(&s)
    }

    #[inline]
    fn serialize_str(&mut self, value: &str) -> Result<(), Error> {
        self.state.push(State::Value(Variable::String(String::from(value))));
        Ok(())
    }

    #[inline]
    fn serialize_none(&mut self) -> Result<(), Error> {
        self.serialize_unit()
    }

    #[inline]
    fn serialize_some<V>(&mut self, value: V) -> Result<(), Error> where V: ser::Serialize {
        value.serialize(self)
    }

    #[inline]
    fn serialize_unit(&mut self) -> Result<(), Error> {
        self.state.push(State::Value(Variable::Null));
        Ok(())
    }

    #[inline]
    fn serialize_unit_variant(&mut self,
                              _name: &str,
                              _variant_index: usize,
                              variant: &str) -> Result<(), Error> {
        let mut values = BTreeMap::new();
        values.insert(String::from(variant), RcVar::new(Variable::Array(vec![])));
        self.state.push(State::Value(Variable::Object(values)));
        Ok(())
    }

    #[inline]
    fn serialize_newtype_variant<T>(&mut self,
                                    _name: &str,
                                    _variant_index: usize,
                                    variant: &str,
                                    value: T) -> Result<(), Error>
                                    where T: ser::Serialize {
        let mut values = BTreeMap::new();
        values.insert(String::from(variant), value.into_jmespath());
        self.state.push(State::Value(Variable::Object(values)));
        Ok(())
    }

    #[inline]
    fn serialize_seq<V>(&mut self, mut visitor: V)
        -> Result<(), Error> where V: ser::SeqVisitor
    {
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
    fn serialize_tuple_variant<V>(&mut self,
                                  _name: &str,
                                  _variant_index: usize,
                                  variant: &str,
                                  visitor: V) -> Result<(), Error>
                                  where V: ser::SeqVisitor {
        try!(self.serialize_seq(visitor));
        let value = match self.state.pop().unwrap() {
            State::Value(value) => value,
            state => panic!("expected value, found {:?}", state),
        };
        let mut object = BTreeMap::new();
        object.insert(String::from(variant), RcVar::new(value));
        self.state.push(State::Value(Variable::Object(object)));
        Ok(())
    }

    #[inline]
    fn serialize_seq_elt<T>(&mut self, value: T)
        -> Result<(), Error> where T: ser::Serialize
    {
        try!(value.serialize(self));
        let value = match self.state.pop().unwrap() {
            State::Value(value) => value,
            state => panic!("expected value, found {:?}", state),
        };
        match *self.state.last_mut().unwrap() {
            State::Array(ref mut values) => { values.push(RcVar::new(value)); }
            ref state => panic!("expected array, found {:?}", state),
        }
        Ok(())
    }

    #[inline]
    fn serialize_map<V>(&mut self, mut visitor: V)
        -> Result<(), Error> where V: ser::MapVisitor
    {
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
    fn serialize_struct_variant<V>(&mut self,
                                   _name: &str,
                                   _variant_index: usize,
                                   variant: &str,
                                   visitor: V) -> Result<(), Error>
                                   where V: ser::MapVisitor {
        try!(self.serialize_map(visitor));
        let value = match self.state.pop().unwrap() {
            State::Value(value) => value,
            state => panic!("expected value, found {:?}", state),
        };

        let mut object = BTreeMap::new();
        object.insert(String::from(variant), RcVar::new(value));
        self.state.push(State::Value(Variable::Object(object)));
        Ok(())
    }

    #[inline]
    fn serialize_map_elt<K, V>(&mut self,
                               key: K,
                               value: V) -> Result<(), Error>
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
            State::Object(ref mut values) => { values.insert(key, RcVar::new(value)); },
            ref state => panic!("expected object, found {:?}", state),
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::RcVar;
    use std::collections::BTreeMap;
    use super::serde_json::{self, Value};
    use super::{Variable, JmespathType};
    use ast::{Ast, Comparator};

    #[test]
    fn creates_variable_from_str() {
        assert_eq!(Ok(Variable::Bool(true)), Variable::from_json("true"));
        assert_eq!(Err("\"expected value\" at line 1 column 1".to_string()),
                   Variable::from_json("abc"));
    }

    #[test]
    fn test_determines_types() {
         assert_eq!(JmespathType::Object,
                Variable::from_json(&"{\"foo\": \"bar\"}").unwrap().get_type());
         assert_eq!(JmespathType::Array, Variable::from_json(&"[\"foo\"]").unwrap().get_type());
         assert_eq!(JmespathType::Null, Variable::Null.get_type());
         assert_eq!(JmespathType::Boolean, Variable::Bool(true).get_type());
         assert_eq!(JmespathType::String, Variable::String("foo".to_string()).get_type());
         assert_eq!(JmespathType::Number, Variable::Number(1.0).get_type());
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
        assert_eq!(true, Variable::Number(10.0).is_truthy());
        assert_eq!(true, Variable::Number(0.0).is_truthy());
    }

    #[test]
    fn test_eq_ne_compare() {
        let l = Variable::String("foo".to_string());
        let r = Variable::String("foo".to_string());
        assert_eq!(Some(true), l.compare(&Comparator::Equal, &r));
        assert_eq!(Some(false), l.compare(&Comparator::NotEqual, &r));
    }

    #[test]
    fn test_compare() {
        let invalid = Variable::String("foo".to_string());
        let l = Variable::Number(10.0);
        let r = Variable::Number(20.0);
        assert_eq!(None, invalid.compare(&Comparator::GreaterThan, &r));
        assert_eq!(Some(false), l.compare(&Comparator::GreaterThan, &r));
        assert_eq!(Some(false), l.compare(&Comparator::GreaterThanEqual, &r));
        assert_eq!(Some(true), r.compare(&Comparator::GreaterThan, &l));
        assert_eq!(Some(true), r.compare(&Comparator::GreaterThanEqual, &l));
        assert_eq!(Some(true), l.compare(&Comparator::LessThan, &r));
        assert_eq!(Some(true), l.compare(&Comparator::LessThanEqual, &r));
        assert_eq!(Some(false), r.compare(&Comparator::LessThan, &l));
        assert_eq!(Some(false), r.compare(&Comparator::LessThanEqual, &l));
    }

    #[test]
    fn gets_value_from_object() {
        let var = Variable::from_json("{\"foo\":1}").unwrap();
        assert_eq!(RcVar::new(Variable::Number(1.0)), var.get_field("foo"));
    }

    #[test]
    fn getting_value_from_non_object_is_null() {
        assert_eq!(RcVar::new(Variable::Null), Variable::Bool(false).get_field("foo"));
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
    fn test_as_number() {
        let value = Variable::from_json("12.0").unwrap();
        assert_eq!(value.as_number(), Some(12f64));
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
        assert_eq!(Variable::Number(1.0), Variable::from_json("1").unwrap());
        assert_eq!(Variable::Number(-1.0), Variable::from_json("-1").unwrap());
        assert_eq!(Variable::Number(1.5), Variable::from_json("1.5").unwrap());
        assert_eq!(Variable::String("abc".to_string()), Variable::from_json("\"abc\"").unwrap());
    }

    #[test]
    fn test_parses_json_array() {
        let var = Variable::from_json("[null, true, [\"a\"]]").unwrap();
        assert_eq!(var, Variable::Array(vec![
            RcVar::new(Variable::Null),
            RcVar::new(Variable::Bool(true)),
            RcVar::new(Variable::Array(vec![
                RcVar::new(Variable::String("a".to_string()))
            ]))
        ]))
    }

    #[test]
    fn test_parses_json_object() {
        let var = Variable::from_json("{\"a\": 1, \"b\": {\"c\": true}}").unwrap();
        let mut expected = BTreeMap::new();
        let mut sub_obj = BTreeMap::new();
        expected.insert("a".to_string(), RcVar::new(Variable::Number(1.0)));
        sub_obj.insert("c".to_string(), RcVar::new(Variable::Bool(true)));
        expected.insert("b".to_string(), RcVar::new(Variable::Object(sub_obj)));
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
        assert_eq!(Variable::Array(vec![RcVar::new(Variable::String("a".to_string()))]), round_trip);
    }

    /// Converting an expression variable to a string is a special case.
    #[test]
    fn test_converts_to_string() {
        assert_eq!("true", Variable::Bool(true).to_string());
        assert_eq!("[true]", Variable::from_json("[true]").unwrap().to_string());
        let v = Variable::Expref(Ast::Identity { offset: 0 });
        assert_eq!("\"__Expref__Identity { offset: 0 }\"", v.to_string());
    }

    #[test]
    fn test_compares_float_equality() {
        assert!(Variable::Number(1.0) == Variable::Number(1.0));
        assert!(Variable::Number(0.0) == Variable::Number(0.0));
        assert!(Variable::Number(0.00001) != Variable::Number(0.0));
        assert!(Variable::Number(999.999) == Variable::Number(999.999));
        assert!(Variable::Number(1.000000000001) == Variable::Number(1.000000000001));
        assert!(Variable::Number(0.7100000000000002) == Variable::Number(0.71));
        assert!(Variable::Number(0.0000000000000002) == Variable::Number(0.0000000000000002));
        assert!(Variable::Number(0.0000000000000002) != Variable::Number(0.0000000000000003));
    }
}
