//! Module for JMESPath runtime variables.

extern crate serde;
extern crate serde_json;

use std::vec;
use serde::{de, ser};
use serde_json::error::{Error, ErrorCode};
use serde_json::value::{Value, Map, MapIntoIter};
use std::collections::BTreeMap;
use std::cmp::{max, Ordering};
use std::fmt;
use std::iter::Iterator;
use std::string::ToString;

use ToJmespath;
use Rcvar;
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
        write!(fmt,
               "{}",
               match *self {
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
    Array(Vec<Rcvar>),
    Object(BTreeMap<String, Rcvar>),
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
                    self.as_number()
                        .unwrap()
                        .partial_cmp(&other.as_number().unwrap())
                        .unwrap_or(Ordering::Less)
                }
                _ => Ordering::Equal,
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
fn convert_map<'a, T>(value: T) -> Variable
    where T: Iterator<Item = (&'a String, &'a Value)>
{
    let mut map: BTreeMap<String, Rcvar> = BTreeMap::new();
    for kvp in value {
        map.insert(kvp.0.to_owned(), kvp.1.to_jmespath());
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
                Variable::Array(values.iter().map(|v| v.to_jmespath()).collect())
            }
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
                Variable::Array(values.drain(..).map(|v| v.to_jmespath()).collect())
            }
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
    pub fn as_array(&self) -> Option<&Vec<Rcvar>> {
        match *self {
            Variable::Array(ref array) => Some(array),
            _ => None,
        }
    }

    /// Returns true if the value is an Object.
    pub fn is_object(&self) -> bool {
        self.as_object().is_some()
    }

    /// If the value is an Object, returns the associated BTreeMap.
    /// Returns None otherwise.
    pub fn as_object(&self) -> Option<&BTreeMap<String, Rcvar>> {
        match *self {
            Variable::Object(ref map) => Some(map),
            _ => None,
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
            _ => None,
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
            _ => None,
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
            _ => None,
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
            _ => None,
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
            _ => None,
        }
    }

    /// If the value is an object, returns the value associated with the provided key.
    /// Otherwise, returns Null.
    #[inline]
    pub fn get_field(&self, key: &str) -> Rcvar {
        if let Variable::Object(ref map) = *self {
            if let Some(result) = map.get(key) {
                return result.clone();
            }
        }
        Rcvar::new(Variable::Null)
    }

    /// If the value is an array, then gets an array value by index. Otherwise returns Null.
    #[inline]
    pub fn get_index(&self, index: usize) -> Rcvar {
        if let Variable::Array(ref array) = *self {
            if let Some(result) = array.get(index) {
                return result.clone();
            }
        }
        Rcvar::new(Variable::Null)
    }

    /// Retrieves an index from the end of an array.
    ///
    /// Returns Null if not an array or if the index is not present.
    /// The formula for determining the index position is length - index (i.e., an
    /// index of 0 or 1 is treated as the end of the array).
    pub fn get_negative_index(&self, index: usize) -> Rcvar {
        if let Variable::Array(ref array) = *self {
            let adjusted_index = max(index, 1);
            if array.len() >= adjusted_index {
                return array[array.len() - adjusted_index].clone();
            }
        }
        Rcvar::new(Variable::Null)
    }

    /// Returns true or false based on if the Variable value is considered truthy.
    pub fn is_truthy(&self) -> bool {
        match *self {
            Variable::Bool(b) => b,
            Variable::String(ref s) => !s.is_empty(),
            Variable::Array(ref a) => !a.is_empty(),
            Variable::Object(ref o) => !o.is_empty(),
            Variable::Number(_) => true,
            _ => false,
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
    pub fn slice(&self, start: &Option<i32>, stop: &Option<i32>, step: i32) -> Option<Vec<Rcvar>> {
        self.as_array().map(|a| slice(a, start, stop, step))
    }
}

// ------------------------------------------
// Variable slicing implementation
// ------------------------------------------

fn slice(array: &[Rcvar], start: &Option<i32>, stop: &Option<i32>, step: i32) -> Vec<Rcvar> {
    let mut result = vec![];
    let len = array.len() as i32;
    if len == 0 {
        return result;
    }
    let a: i32 = match *start {
        Some(starting_index) => adjust_slice_endpoint(len, starting_index, step),
        _ if step < 0 => len - 1,
        _ => 0,
    };
    let b: i32 = match *stop {
        Some(ending_index) => adjust_slice_endpoint(len, ending_index, step),
        _ if step < 0 => -1,
        _ => len,
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

// Serde Variable deserialization
// ------------------------------------------
// Below begins the amazingly complicated code needed to implement
// serde serialization and deserialization for Variable. This code
// is ported from the serde_json::Value implementation and adapted
// for Variable and Rcvar. There are a few instances of
// `(*self).clone` that I don't like, but I'm not sure how to work
// around it.

/// Shortcut function to encode a `T` into a JMESPath `Variable`
fn to_variable<T>(value: T) -> Variable
    where T: ser::Serialize,
{
    let mut ser = Serializer::new();
    value.serialize(&mut ser).expect("failed to serialize");
    ser.unwrap()
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
            fn visit_some<D>(
                &mut self,
                deserializer: &mut D
            ) -> Result<Variable, D::Error>
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

/// Creates a `serde::Deserializer` from a `Variable` object.
pub struct Deserializer {
    value: Option<Variable>,
}

impl Deserializer {
    /// Creates a new deserializer instance for deserializing the specified Variable value.
    pub fn new(value: Variable) -> Deserializer {
        Deserializer {
            value: Some(value),
        }
    }
}

impl de::Deserializer for Deserializer {
    type Error = Error;

    #[inline]
    fn deserialize<V>(&mut self, mut visitor: V) -> Result<V::Value, Error>
        where V: de::Visitor,
    {
        let value = match self.value.take() {
            Some(value) => value,
            None => {
                return Err(de::Error::end_of_stream());
            }
        };

        match value {
            Variable::Null => visitor.visit_unit(),
            Variable::Bool(v) => visitor.visit_bool(v),
            Variable::Number(v) => visitor.visit_f64(v),
            Variable::String(v) => visitor.visit_string(v),
            Variable::Array(v) => {
                let len = v.len();
                visitor.visit_seq(SeqDeserializer {
                    de: self,
                    iter: v.into_iter(),
                    len: len,
                })
            }
            Variable::Object(v) => {
                let len = v.len();
                visitor.visit_map(MapDeserializer {
                    de: self,
                    iter: v.into_iter(),
                    value: None,
                    len: len,
                })
            },
            Variable::Expref(v) => visitor.visit_string(format!("<expression: {:?}>", v)),
        }
    }

    #[inline]
    fn deserialize_option<V>(
        &mut self,
        mut visitor: V
    ) -> Result<V::Value, Error>
        where V: de::Visitor,
    {
        match self.value {
            Some(Variable::Null) => visitor.visit_none(),
            Some(_) => visitor.visit_some(self),
            None => Err(de::Error::end_of_stream()),
        }
    }

    #[inline]
    fn deserialize_enum<V>(
        &mut self,
        _name: &str,
        _variants: &'static [&'static str],
        mut visitor: V
    ) -> Result<V::Value, Error>
        where V: de::EnumVisitor,
    {
        let (variant, value) = match self.value.take() {
            Some(Variable::Object(value)) => {
                let mut iter = value.into_iter();
                let (variant, value) = match iter.next() {
                    Some(v) => v,
                    None => {
                        return Err(de::Error::invalid_type(de::Type::VariantName));
                    }
                };
                // enums are encoded in json as maps with a single key:value pair
                if iter.next().is_some() {
                    return Err(de::Error::invalid_type(de::Type::Map));
                }
                (variant, Some((*value).clone()))
            }
            Some(Variable::String(variant)) => (variant, None),
            Some(_) => {
                return Err(de::Error::invalid_type(de::Type::Enum));
            }
            None => {
                return Err(de::Error::end_of_stream());
            }
        };

        visitor.visit(VariantDeserializer {
            de: self,
            val: value,
            variant: Some(Variable::String(variant)),
        })
    }

    #[inline]
    fn deserialize_newtype_struct<V>(
        &mut self,
        _name: &'static str,
        mut visitor: V
    ) -> Result<V::Value, Self::Error>
        where V: de::Visitor,
    {
        visitor.visit_newtype_struct(self)
    }

    forward_to_deserialize! {
        bool usize u8 u16 u32 u64 isize i8 i16 i32 i64 f32 f64 char str string
        unit seq seq_fixed_size bytes map unit_struct tuple_struct struct
        struct_field tuple ignored_any
    }
}

struct VariantDeserializer<'a> {
    de: &'a mut Deserializer,
    val: Option<Variable>,
    variant: Option<Variable>,
}

impl<'a> de::VariantVisitor for VariantDeserializer<'a> {
    type Error = Error;

    fn visit_variant<V>(&mut self) -> Result<V, Error>
        where V: de::Deserialize,
    {
        let variant = self.variant.take().expect("variant is missing");
        de::Deserialize::deserialize(&mut Deserializer::new(variant))
    }

    fn visit_unit(&mut self) -> Result<(), Error> {
        match self.val.take() {
            Some(val) => {
                de::Deserialize::deserialize(&mut Deserializer::new(val))
            }
            None => Ok(()),
        }
    }

    fn visit_newtype<T>(&mut self) -> Result<T, Error>
        where T: de::Deserialize,
    {
        let val = self.val.take().expect("val is missing");
        de::Deserialize::deserialize(&mut Deserializer::new(val))
    }

    fn visit_tuple<V>(
        &mut self,
        _len: usize,
        visitor: V
    ) -> Result<V::Value, Error>
        where V: de::Visitor,
    {
        let val = self.val.take().expect("val is missing");
        if let Variable::Array(fields) = val {
            de::Deserializer::deserialize(&mut SeqDeserializer {
                                              de: self.de,
                                              len: fields.len(),
                                              iter: fields.into_iter(),
                                          },
                                          visitor)
        } else {
            Err(de::Error::invalid_type(de::Type::Tuple))
        }
    }

    fn visit_struct<V>(
        &mut self,
        _fields: &'static [&'static str],
        visitor: V
    ) -> Result<V::Value, Error>
        where V: de::Visitor,
    {
        let val = self.val.take().expect("val is missing");
        if let Variable::Object(fields) = val {
            de::Deserializer::deserialize(&mut MapDeserializer {
                                              de: self.de,
                                              len: fields.len(),
                                              iter: fields.into_iter(),
                                              value: None,
                                          },
                                          visitor)
        } else {
            Err(de::Error::invalid_type(de::Type::Struct))
        }
    }
}

struct SeqDeserializer<'a> {
    de: &'a mut Deserializer,
    iter: vec::IntoIter<Rcvar>,
    len: usize,
}

impl<'a> de::Deserializer for SeqDeserializer<'a> {
    type Error = Error;

    #[inline]
    fn deserialize<V>(&mut self, mut visitor: V) -> Result<V::Value, Error>
        where V: de::Visitor,
    {
        if self.len == 0 {
            visitor.visit_unit()
        } else {
            visitor.visit_seq(self)
        }
    }

    forward_to_deserialize! {
        bool usize u8 u16 u32 u64 isize i8 i16 i32 i64 f32 f64 char str string
        unit option seq seq_fixed_size bytes map unit_struct newtype_struct
        tuple_struct struct struct_field tuple enum ignored_any
    }
}

impl<'a> de::SeqVisitor for SeqDeserializer<'a> {
    type Error = Error;

    fn visit<T>(&mut self) -> Result<Option<T>, Error>
        where T: de::Deserialize,
    {
        match self.iter.next() {
            Some(value) => {
                self.len -= 1;
                self.de.value = Some((*value).clone());
                Ok(Some(try!(de::Deserialize::deserialize(self.de))))
            }
            None => Ok(None),
        }
    }

    fn end(&mut self) -> Result<(), Error> {
        if self.len == 0 {
            Ok(())
        } else {
            Err(de::Error::invalid_length(self.len))
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len, Some(self.len))
    }
}

struct MapDeserializer<'a> {
    de: &'a mut Deserializer,
    iter: MapIntoIter<String, Rcvar>,
    value: Option<Variable>,
    len: usize,
}

impl<'a> de::MapVisitor for MapDeserializer<'a> {
    type Error = Error;

    fn visit_key<T>(&mut self) -> Result<Option<T>, Error>
        where T: de::Deserialize,
    {
        match self.iter.next() {
            Some((key, value)) => {
                self.len -= 1;
                self.value = Some((*value).clone());
                self.de.value = Some(Variable::String(key));
                Ok(Some(try!(de::Deserialize::deserialize(self.de))))
            }
            None => Ok(None),
        }
    }

    fn visit_value<T>(&mut self) -> Result<T, Error>
        where T: de::Deserialize,
    {
        let value = self.value.take().expect("value is missing");
        self.de.value = Some(value);
        Ok(try!(de::Deserialize::deserialize(self.de)))
    }

    fn end(&mut self) -> Result<(), Error> {
        if self.len == 0 {
            Ok(())
        } else {
            Err(de::Error::invalid_length(self.len))
        }
    }

    fn missing_field<V>(&mut self, field: &'static str) -> Result<V, Error>
        where V: de::Deserialize,
    {
        struct MissingFieldDeserializer(&'static str);

        impl de::Deserializer for MissingFieldDeserializer {
            type Error = de::value::Error;

            fn deserialize<V>(
                &mut self,
                _visitor: V
            ) -> Result<V::Value, Self::Error>
                where V: de::Visitor,
            {
                let &mut MissingFieldDeserializer(field) = self;
                Err(de::value::Error::MissingField(field))
            }

            fn deserialize_option<V>(
                &mut self,
                mut visitor: V
            ) -> Result<V::Value, Self::Error>
                where V: de::Visitor,
            {
                visitor.visit_none()
            }

            forward_to_deserialize! {
                bool usize u8 u16 u32 u64 isize i8 i16 i32 i64 f32 f64 char str
                string unit seq seq_fixed_size bytes map unit_struct
                newtype_struct tuple_struct struct struct_field tuple enum
                ignored_any
            }
        }

        let mut de = MissingFieldDeserializer(field);
        Ok(try!(de::Deserialize::deserialize(&mut de)))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len, Some(self.len))
    }
}

impl<'a> de::Deserializer for MapDeserializer<'a> {
    type Error = Error;

    #[inline]
    fn deserialize<V>(&mut self, mut visitor: V) -> Result<V::Value, Error>
        where V: de::Visitor,
    {
        visitor.visit_map(self)
    }

    forward_to_deserialize! {
        bool usize u8 u16 u32 u64 isize i8 i16 i32 i64 f32 f64 char str string
        unit option seq seq_fixed_size bytes map unit_struct newtype_struct
        tuple_struct struct struct_field tuple enum ignored_any
    }
}

// Serde Variable serialization
impl ser::Serialize for Variable {
    #[inline]
    fn serialize<S>(&self, serializer: &mut S) -> Result<(), S::Error>
        where S: ser::Serializer,
    {
        match *self {
            Variable::Null => serializer.serialize_unit(),
            Variable::Bool(v) => serializer.serialize_bool(v),
            Variable::Number(v) => {
                // Serializes as an integer when the decimal is 0 (i.e., 0.0).
                if v.floor() == v {
                    serializer.serialize_i64(v as i64)
                } else {
                    serializer.serialize_f64(v)
                }
            },
            Variable::String(ref v) => serializer.serialize_str(v),
            Variable::Array(ref v) => v.serialize(serializer),
            Variable::Object(ref v) => v.serialize(serializer),
            Variable::Expref(ref e) => serializer.serialize_str(&format!("<expression: {:?}>", e)),
        }
    }
}

/// Create a `serde::Serializer` that serializes a `Serialize`e into a `Variable`.
pub struct Serializer {
    value: Variable,
}

impl Serializer {
    /// Construct a new `Serializer`.
    pub fn new() -> Serializer {
        Serializer {
            value: Variable::Null,
        }
    }

    /// Unwrap the `Serializer` and return the `Variable`.
    pub fn unwrap(self) -> Variable {
        self.value
    }
}

impl Default for Serializer {
    fn default() -> Self {
        Serializer::new()
    }
}

#[doc(hidden)]
pub struct TupleVariantState {
    name: String,
    vec: Vec<Rcvar>,
}

#[doc(hidden)]
pub struct StructVariantState {
    name: String,
    map: Map<String, Rcvar>,
}

#[doc(hidden)]
pub struct MapState {
    map: Map<String, Rcvar>,
    next_key: Option<String>,
}

impl ser::Serializer for Serializer {
    type Error = Error;

    type SeqState = Vec<Rcvar>;
    type TupleState = Vec<Rcvar>;
    type TupleStructState = Vec<Rcvar>;
    type TupleVariantState = TupleVariantState;
    type MapState = MapState;
    type StructState = MapState;
    type StructVariantState = StructVariantState;

    #[inline]
    fn serialize_bool(&mut self, value: bool) -> Result<(), Error> {
        self.value = Variable::Bool(value);
        Ok(())
    }

    #[inline]
    fn serialize_isize(&mut self, value: isize) -> Result<(), Error> {
        self.serialize_f64(value as f64)
    }

    #[inline]
    fn serialize_i8(&mut self, value: i8) -> Result<(), Error> {
        self.serialize_f64(value as f64)
    }

    #[inline]
    fn serialize_i16(&mut self, value: i16) -> Result<(), Error> {
        self.serialize_f64(value as f64)
    }

    #[inline]
    fn serialize_i32(&mut self, value: i32) -> Result<(), Error> {
        self.serialize_f64(value as f64)
    }

    fn serialize_i64(&mut self, value: i64) -> Result<(), Error> {
        self.serialize_f64(value as f64)
    }

    #[inline]
    fn serialize_usize(&mut self, value: usize) -> Result<(), Error> {
        self.serialize_f64(value as f64)
    }

    #[inline]
    fn serialize_u8(&mut self, value: u8) -> Result<(), Error> {
        self.serialize_f64(value as f64)
    }

    #[inline]
    fn serialize_u16(&mut self, value: u16) -> Result<(), Error> {
        self.serialize_f64(value as f64)
    }

    #[inline]
    fn serialize_u32(&mut self, value: u32) -> Result<(), Error> {
        self.serialize_f64(value as f64)
    }

    #[inline]
    fn serialize_u64(&mut self, value: u64) -> Result<(), Error> {
        self.serialize_f64(value as f64)
    }

    #[inline]
    fn serialize_f32(&mut self, value: f32) -> Result<(), Error> {
        self.serialize_f64(value as f64)
    }

    #[inline]
    fn serialize_f64(&mut self, value: f64) -> Result<(), Error> {
        self.value = if value.is_finite() {
            Variable::Number(value)
        } else {
            Variable::Null
        };
        Ok(())
    }

    #[inline]
    fn serialize_char(&mut self, value: char) -> Result<(), Error> {
        let mut s = String::new();
        s.push(value);
        self.serialize_str(&s)
    }

    #[inline]
    fn serialize_str(&mut self, value: &str) -> Result<(), Error> {
        self.value = Variable::String(String::from(value));
        Ok(())
    }

    fn serialize_bytes(&mut self, value: &[u8]) -> Result<(), Error> {
        let mut state = try!(self.serialize_seq(Some(value.len())));
        for byte in value {
            try!(self.serialize_seq_elt(&mut state, byte));
        }
        self.serialize_seq_end(state)
    }

    #[inline]
    fn serialize_unit(&mut self) -> Result<(), Error> {
        Ok(())
    }

    #[inline]
    fn serialize_unit_struct(
        &mut self,
        _name: &'static str
    ) -> Result<(), Error> {
        self.serialize_unit()
    }

    #[inline]
    fn serialize_unit_variant(
        &mut self,
        _name: &'static str,
        _variant_index: usize,
        variant: &'static str
    ) -> Result<(), Error> {
        self.serialize_str(variant)
    }

    #[inline]
    fn serialize_newtype_struct<T>(
        &mut self,
        _name: &'static str,
        value: T
    ) -> Result<(), Error>
        where T: ser::Serialize,
    {
        value.serialize(self)
    }

    fn serialize_newtype_variant<T>(
        &mut self,
        _name: &'static str,
        _variant_index: usize,
        variant: &'static str,
        value: T
    ) -> Result<(), Error>
        where T: ser::Serialize,
    {
        let mut values = Map::new();
        values.insert(String::from(variant), Rcvar::new(to_variable(&value)));
        self.value = Variable::Object(values);
        Ok(())
    }

    #[inline]
    fn serialize_none(&mut self) -> Result<(), Error> {
        self.serialize_unit()
    }

    #[inline]
    fn serialize_some<V>(&mut self, value: V) -> Result<(), Error>
        where V: ser::Serialize,
    {
        value.serialize(self)
    }

    fn serialize_seq(
        &mut self,
        len: Option<usize>
    ) -> Result<Vec<Rcvar>, Error> {
        Ok(Vec::with_capacity(len.unwrap_or(0)))
    }

    fn serialize_seq_elt<T: ser::Serialize>(
        &mut self,
        state: &mut Vec<Rcvar>,
        value: T
    ) -> Result<(), Error>
        where T: ser::Serialize,
    {
        state.push(Rcvar::new(to_variable(&value)));
        Ok(())
    }

    fn serialize_seq_end(&mut self, state: Vec<Rcvar>) -> Result<(), Error> {
        self.value = Variable::Array(state);
        Ok(())
    }

    fn serialize_seq_fixed_size(
        &mut self,
        size: usize
    ) -> Result<Vec<Rcvar>, Error> {
        self.serialize_seq(Some(size))
    }

    fn serialize_tuple(&mut self, len: usize) -> Result<Vec<Rcvar>, Error> {
        self.serialize_seq(Some(len))
    }

    fn serialize_tuple_elt<T: ser::Serialize>(
        &mut self,
        state: &mut Vec<Rcvar>,
        value: T
    ) -> Result<(), Error> {
        self.serialize_seq_elt(state, value)
    }

    fn serialize_tuple_end(&mut self, state: Vec<Rcvar>) -> Result<(), Error> {
        self.serialize_seq_end(state)
    }

    fn serialize_tuple_struct(
        &mut self,
        _name: &'static str,
        len: usize
    ) -> Result<Vec<Rcvar>, Error> {
        self.serialize_seq(Some(len))
    }

    fn serialize_tuple_struct_elt<T: ser::Serialize>(
        &mut self,
        state: &mut Vec<Rcvar>,
        value: T
    ) -> Result<(), Error> {
        self.serialize_seq_elt(state, value)
    }

    fn serialize_tuple_struct_end(&mut self, state: Vec<Rcvar>) -> Result<(), Error> {
        self.serialize_seq_end(state)
    }

    fn serialize_tuple_variant(
        &mut self,
        _name: &'static str,
        _variant_index: usize,
        variant: &'static str,
        len: usize
    ) -> Result<TupleVariantState, Error> {
        Ok(TupleVariantState {
            name: String::from(variant),
            vec: Vec::with_capacity(len),
        })
    }

    fn serialize_tuple_variant_elt<T: ser::Serialize>(
        &mut self,
        state: &mut TupleVariantState,
        value: T
    ) -> Result<(), Error> {
        state.vec.push(Rcvar::new(to_variable(&value)));
        Ok(())
    }

    fn serialize_tuple_variant_end(&mut self, state: TupleVariantState) -> Result<(), Error> {
        let mut object = Map::new();
        object.insert(state.name, Rcvar::new(Variable::Array(state.vec)));
        self.value = Variable::Object(object);
        Ok(())
    }

    fn serialize_map(&mut self, _len: Option<usize>) -> Result<MapState, Error> {
        Ok(MapState {
            map: Map::new(),
            next_key: None,
        })
    }

    fn serialize_map_key<T: ser::Serialize>(
        &mut self,
        state: &mut MapState,
        key: T,
    ) -> Result<(), Error> {
        match to_variable(&key) {
            Variable::String(s) => state.next_key = Some(s),
            _ => return Err(Error::Syntax(ErrorCode::KeyMustBeAString, 0, 0)),
        };
        Ok(())
    }

    fn serialize_map_value<T: ser::Serialize>(
        &mut self,
        state: &mut MapState,
        value: T,
    ) -> Result<(), Error> {
        match state.next_key.take() {
            Some(key) => state.map.insert(key, Rcvar::new(to_variable(&value))),
            None => {
                let code = ErrorCode::Custom("serialize_map_value without \
                                              matching serialize_map_key".to_owned());
                return Err(Error::Syntax(code, 0, 0));
            }
        };
        Ok(())
    }

    fn serialize_map_end(&mut self, state: MapState) -> Result<(), Error> {
        self.value = Variable::Object(state.map);
        Ok(())
    }

    fn serialize_struct(
        &mut self,
        _name: &'static str,
        len: usize
    ) -> Result<MapState, Error> {
        self.serialize_map(Some(len))
    }

    fn serialize_struct_elt<V: ser::Serialize>(
        &mut self,
        state: &mut MapState,
        key: &'static str,
        value: V
    ) -> Result<(), Error> {
        try!(self.serialize_map_key(state, key));
        self.serialize_map_value(state, value)
    }

    fn serialize_struct_end(&mut self, state: MapState) -> Result<(), Error> {
        self.serialize_map_end(state)
    }

    fn serialize_struct_variant(
        &mut self,
        _name: &'static str,
        _variant_index: usize,
        variant: &'static str,
        _len: usize
    ) -> Result<StructVariantState, Error> {
        Ok(StructVariantState {
            name: String::from(variant),
            map: Map::new(),
        })
    }

    fn serialize_struct_variant_elt<V: ser::Serialize>(
        &mut self,
        state: &mut StructVariantState,
        key: &'static str,
        value: V
    ) -> Result<(), Error> {
        state.map.insert(String::from(key), Rcvar::new(to_variable(&value)));
        Ok(())
    }

    fn serialize_struct_variant_end(&mut self, state: StructVariantState) -> Result<(), Error> {
        let mut object = Map::new();
        object.insert(state.name, Rcvar::new(Variable::Object(state.map)));
        self.value = Variable::Object(object);
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use ::Rcvar;
    use std::collections::BTreeMap;
    use super::serde_json::{self, Value};
    use super::{Variable, JmespathType};
    use ast::{Ast, Comparator};

    #[test]
    fn creates_variable_from_str() {
        assert_eq!(Ok(Variable::Bool(true)), Variable::from_json("true"));
        assert_eq!(Err("expected value at line 1 column 1".to_string()),
                   Variable::from_json("abc"));
    }

    #[test]
    fn test_determines_types() {
        assert_eq!(JmespathType::Object,
                   Variable::from_json(&"{\"foo\": \"bar\"}").unwrap().get_type());
        assert_eq!(JmespathType::Array,
                   Variable::from_json(&"[\"foo\"]").unwrap().get_type());
        assert_eq!(JmespathType::Null, Variable::Null.get_type());
        assert_eq!(JmespathType::Boolean, Variable::Bool(true).get_type());
        assert_eq!(JmespathType::String,
                   Variable::String("foo".to_string()).get_type());
        assert_eq!(JmespathType::Number, Variable::Number(1.0).get_type());
    }

    #[test]
    fn test_is_truthy() {
        assert_eq!(true,
                   Variable::from_json(&"{\"foo\": \"bar\"}").unwrap().is_truthy());
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
        assert_eq!(Rcvar::new(Variable::Number(1.0)), var.get_field("foo"));
    }

    #[test]
    fn getting_value_from_non_object_is_null() {
        assert_eq!(Rcvar::new(Variable::Null),
                   Variable::Bool(false).get_field("foo"));
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
        assert_eq!(Some(&"foo".to_string()),
                   Variable::String("foo".to_string()).as_string());
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
        assert_eq!(true,
                   Variable::Expref(Ast::Identity { offset: 0 }).is_expref());
        assert_eq!(&Ast::Identity { offset: 0 },
                   Variable::Expref(Ast::Identity { offset: 0 }).as_expref().unwrap());
    }

    #[test]
    fn test_parses_json_scalar() {
        assert_eq!(Variable::Null, Variable::from_json("null").unwrap());
        assert_eq!(Variable::Bool(true), Variable::from_json("true").unwrap());
        assert_eq!(Variable::Bool(false), Variable::from_json("false").unwrap());
        assert_eq!(Variable::Number(1.0), Variable::from_json("1").unwrap());
        assert_eq!(Variable::Number(-1.0), Variable::from_json("-1").unwrap());
        assert_eq!(Variable::Number(1.5), Variable::from_json("1.5").unwrap());
        assert_eq!(Variable::String("abc".to_string()),
                   Variable::from_json("\"abc\"").unwrap());
    }

    #[test]
    fn test_parses_and_encodes_complex() {
        let js = "[null,true,1,[\"a\"],{\"b\":{\"c\":[[9.9],false]}},-1,1.0000001]";
        let var = Variable::from_json(js).unwrap();
        assert_eq!(js, var.to_string());
    }

    #[test]
    fn test_parses_json_object() {
        let var = Variable::from_json("{\"a\": 1, \"b\": {\"c\": true}}").unwrap();
        let mut expected = BTreeMap::new();
        let mut sub_obj = BTreeMap::new();
        expected.insert("a".to_string(), Rcvar::new(Variable::Number(1.0)));
        sub_obj.insert("c".to_string(), Rcvar::new(Variable::Bool(true)));
        expected.insert("b".to_string(), Rcvar::new(Variable::Object(sub_obj)));
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
        assert_eq!(Variable::Array(vec![Rcvar::new(Variable::String("a".to_string()))]),
                   round_trip);
    }

    /// Converting an expression variable to a string is a special case.
    #[test]
    fn test_converts_to_string() {
        assert_eq!("true", Variable::Bool(true).to_string());
        assert_eq!("[true]", Variable::from_json("[true]").unwrap().to_string());
        let v = Variable::Expref(Ast::Identity { offset: 0 });
        assert_eq!("\"<expression: Identity { offset: 0 }>\"", v.to_string());
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
