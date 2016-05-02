use std::rc::Rc;
use std::collections::{BTreeMap, VecDeque};
use std::fmt;

use serde_json::Value;

use jmespath::{Variable, RcVar};
use Listener;
use ListenResult;
use Signal;
use Event;
use StreamValue;
use StreamError;
use Emitter;

/* ------------------------------------------
 * BufferedListener
 * ------------------------------------------ */

/// A BufferedListener buffers each received event in a VecDeque.
#[derive(Debug)]
pub struct BufferedListener {
    /// Queue of buffered events.
    pub events: VecDeque<Event>,
}

impl BufferedListener {
    /// Creates a new buffered listener.
    #[inline]
    pub fn new() -> BufferedListener {
        BufferedListener {
            events: VecDeque::new()
        }
    }

    /// Checks if the buffer is empty.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.events.is_empty()
    }

    /// Reset the contents of the buffer.
    pub fn reset(&mut self) {
        self.events.clear();
    }

    /// Returns if the buffer is known to be truthy in JMESPath terms.
    pub fn is_truthy(&self) -> bool {
        let len = self.events.len();
        if len == 0 {
            false
        } else if len == 1 {
            match *self.events.front().unwrap() {
                Event::Value(StreamValue::Null) => false,
                Event::Value(StreamValue::Bool(false)) => false,
                Event::Value(StreamValue::String(ref s)) if s.len() == 0 => false,
                _ => true
            }
        } else if len == 2 && self.events[0] == Event::StartArray {
            // If the buffer is only "[" and "]", then it is falsey.
            self.events[1] != Event::EndArray
        } else if len == 2 && self.events[0] == Event::StartObject {
            // If the buffer is only "{" and "}", then it is falsey.
            self.events[1] != Event::EndObject
        } else {
            true
        }
    }

    /// Returns true if the events in the buffer are falsey.
    ///
    /// Note that this method will return true even if there are no
    /// events in the buffer. As such, it's better to check if not
    /// empty or change the logic in question to instead rely on the
    /// is_truthy method.
    pub fn is_falsey(&self) -> bool {
        !self.is_truthy()
    }
}

impl Listener for BufferedListener {
    /// Pushes the event onto the buffer.
    #[inline]
    fn push(&mut self, event: &Event) -> ListenResult {
        self.events.push_back(event.clone());
        Ok(Signal::More)
    }
}

impl Emitter for BufferedListener {
    fn emit(&self, listener: &mut Listener) -> ListenResult {
        for event in self.events.iter() {
            if let Signal::Done = try!(listener.push(event)) {
                return Ok(Signal::Done);
            }
        }
        Ok(Signal::More)
    }
}

/* ------------------------------------------
 * JsonWriters and implementations
 * ------------------------------------------ */

/// Writes JSON text to a destination.
trait JsonWriter {
    /// Write a char to the writer.
    fn write_char(&mut self, c: char) -> ListenResult;

    /// Write a &str to the writer.
    fn write_str(&mut self, s: &str) -> ListenResult;
}

 /// Writes JSON events to an in-memory JSON string.
 struct JsonStringWriter {
     pub buffer: String,
 }

impl JsonStringWriter {
    /// Creates a new JSON string writer.
    #[inline]
    pub fn new() -> JsonStringWriter {
        JsonStringWriter {
            buffer: String::new(),
        }
    }
}

impl JsonWriter for JsonStringWriter {
    #[inline]
    fn write_char(&mut self, c: char) -> ListenResult {
        self.buffer.push(c);
        Ok(Signal::More)
    }

    #[inline]
    fn write_str(&mut self, s: &str) -> ListenResult {
        self.buffer.push_str(s);
        Ok(Signal::More)
    }
}

/// Represents a placeholder of what type is currently open.
#[derive(Debug)]
enum StringContextType {
    Array,
    Object,
}

/// Holds the context type and whether or not it is the first value in
/// a larger context (to account for when a "," is inserted).
#[derive(Debug)]
struct StringContextValue {
    context_type: StringContextType,
    is_first: bool,
}

impl StringContextValue {
    /// Create a new object context value
    #[inline]
    pub fn new_object() -> StringContextValue {
        StringContextValue {
            context_type: StringContextType::Object,
            is_first: true,
        }
    }

    /// Create a new array context value
    #[inline]
    pub fn new_array() -> StringContextValue {
        StringContextValue {
            context_type: StringContextType::Array,
            is_first: true,
        }
    }
}

/// Writes JSON events to a JsonWriter, handling context and commas.
struct JsonStringSerializer<T: JsonWriter> {
    /// Writes JSON events.
    pub writer: T,
    /// Tracks context to know when to use commas.
    context: Vec<StringContextValue>,
}

impl<T> JsonStringSerializer<T> where T: JsonWriter {
    /// Creates a new JsonStringSerializer.
    #[inline]
    fn new(writer: T) -> JsonStringSerializer<T> {
        JsonStringSerializer {
            writer: writer,
            context: Vec::new(),
        }
    }

    /// Checks if the value requires a preceding comma.
    #[inline]
    fn check_value(&mut self, for_field: bool) -> ListenResult {
        if let Some(v) = self.context.last_mut() {
            match (&v.context_type, for_field) {
                (&StringContextType::Array, _) | (&StringContextType::Object, true) => {
                    if v.is_first {
                        v.is_first = false;
                    } else {
                        return self.writer.write_char(',');
                    }
                },
                _ => {}
            }
        }
        Ok(Signal::More)
    }
}

impl<T> Listener for JsonStringSerializer<T> where T: JsonWriter {
    fn push(&mut self, event: &Event) -> ListenResult {
        match *event {
            Event::StartArray => {
                self.check_value(false).and_then(|_| {
                    self.context.push(StringContextValue::new_array());
                    self.writer.write_char('[')
                })
            },
            Event::StartObject => {
                self.check_value(false).and_then(|_| {
                    self.context.push(StringContextValue::new_object());
                    self.writer.write_char('{')
                })
            },
            Event::EndArray => {
                self.context.pop();
                self.writer.write_char(']')
            },
            Event::EndObject => {
                self.context.pop();
                self.writer.write_char('}')
            },
            Event::FieldName(ref s) => {
                self.check_value(true).and_then(|_| self.writer.write_str(&format!("{:?}:", s)))
            },
            Event::Value(ref v) => {
                self.check_value(false).and_then(|_| self.writer.write_str(&v.to_string()))
            },
            _ => Ok(Signal::More)
        }
    }
}

/* ------------------------------------------
 * StringListener
 * ------------------------------------------ */

/// Listens for JSON events and writes them to an in-memory buffer.
pub struct StringListener {
    serializer: JsonStringSerializer<JsonStringWriter>,
}

impl StringListener {
    /// Create a new StringListener.
    #[inline]
    pub fn new() -> StringListener {
        StringListener {
            serializer: JsonStringSerializer::new(JsonStringWriter::new())
        }
    }

    /// Clears the buffer
    pub fn clear(&mut self) {
        self.serializer.writer.buffer.clear();
    }

    /// Get a reference to the string buffer.
    pub fn as_str(&self) -> &str {
        &self.serializer.writer.buffer
    }

    /// Get the string buffer and take ownership.
    pub fn get_string(self) -> String {
        self.serializer.writer.buffer
    }
}

impl Listener for StringListener {
    #[inline]
    fn push(&mut self, event: &Event) -> ListenResult {
        self.serializer.push(event)
    }
}

impl fmt::Display for StringListener {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(fmt, "{}", self.as_str())
    }
}

/* ------------------------------------------
 * ValueListener
 * ------------------------------------------ */

/// Creates values when listeneing with a ValueListener.
pub trait ValueCreator<T> {
    /// Resets the state of the ValueCreator
    fn reset(&mut self) {
        // No-op
    }

    /// Creates an array value.
    fn array(&self, values: Vec<T>) -> T;

    /// Creates an array value.
    fn object(&self, key_value_pairs: BTreeMap<String, T>) -> T;

    /// Creates a boolean value.
    fn bool(&self, b: bool) -> T;

    /// Creates a string value.
    fn string(&self, s: String) -> T;

    /// Creates an I64 value.
    fn i64(&self, i: i64) -> T;

    /// Creates an I64 value.
    fn u64(&self, i: u64) -> T;

    /// Creates an F64 value.
    fn f64(&self, i: f64) -> T;

    /// Creates a null value.
    fn null(&self) -> T;
}

/// Creates Serde JSON Value enums.
#[derive(Debug)]
pub struct SerdeValueCreator;

impl ValueCreator<Value> for SerdeValueCreator {
    #[inline]
    fn array(&self, values: Vec<Value>) -> Value {
        Value::Array(values)
    }

    #[inline]
    fn object(&self, key_value_pairs: BTreeMap<String, Value>) -> Value {
        Value::Object(key_value_pairs)
    }

    #[inline]
    fn bool(&self, b: bool) -> Value {
        Value::Bool(b)
    }

    #[inline]
    fn string(&self, s: String) -> Value {
        Value::String(s)
    }

    #[inline]
    fn i64(&self, i: i64) -> Value {
        Value::I64(i)
    }

    #[inline]
    fn u64(&self, i: u64) -> Value {
        Value::U64(i)
    }

    #[inline]
    fn f64(&self, i: f64) -> Value {
        Value::F64(i)
    }

    #[inline]
    fn null(&self, ) -> Value {
        Value::Null
    }
}

/// Creates JMESPath Variable enums.
#[derive(Debug)]
pub struct JmesPathValueCreator;

impl ValueCreator<RcVar> for JmesPathValueCreator {
    #[inline]
    fn array(&self, values: Vec<RcVar>) -> RcVar {
        Rc::new(Variable::Array(values))
    }

    #[inline]
    fn object(&self, key_value_pairs: BTreeMap<String, RcVar>) -> RcVar {
        Rc::new(Variable::Object(key_value_pairs))
    }

    #[inline]
    fn bool(&self, b: bool) -> RcVar {
        Rc::new(Variable::Bool(b))
    }

    #[inline]
    fn string(&self, s: String) -> RcVar {
        Rc::new(Variable::String(s))
    }

    #[inline]
    fn i64(&self, i: i64) -> RcVar {
        Rc::new(Variable::I64(i))
    }

    #[inline]
    fn u64(&self, i: u64) -> RcVar {
        Rc::new(Variable::U64(i))
    }

    #[inline]
    fn f64(&self, i: f64) -> RcVar {
        Rc::new(Variable::F64(i))
    }

    #[inline]
    fn null(&self) -> RcVar {
        Rc::new(Variable::Null)
    }
}

#[derive(Debug)]
enum State<V> {
    Value(V),
    Array(Vec<V>),
    Object(BTreeMap<String, V>),
    Field(String),
}

impl<V> State<V> {
    pub fn to_object(self) -> Option<BTreeMap<String, V>> {
        match self {
            State::Object(map) => Some(map),
            _ => None
        }
    }
}

/// Listens to events, lazily building up a serde_json::Value.
pub struct ValueListener<T> {
    state: Vec<State<T>>,
    creator: Box<ValueCreator<T>>,
    is_done: bool,
}

impl<T> ValueListener<T> where T: fmt::Debug {
    /// Creates a new ValueListener.
    #[inline]
    pub fn new(value_creator: Box<ValueCreator<T>>) -> ValueListener<T> {
        ValueListener {
            state: Vec::new(),
            creator: value_creator,
            is_done: false,
        }
    }

    pub fn reset(&mut self) {
        self.state.clear();
        self.creator.reset();
        self.is_done = false;
    }

    /// Returns true/false if the variable is finished being created.
    pub fn is_complete(&self) -> bool {
        self.is_done
    }

    /// Attempts to take the value out of the listener.
    pub fn take_value(&mut self) -> Result<T, &'static str> {
        match self.state.pop() {
            None => Err("Attempted to take the value of an empty listener"),
            Some(State::Array(_)) => Err("Attempted to take the value of an unclosed array"),
            Some(State::Object(_)) => Err("Attempted to take the value of an unclosed object"),
            Some(State::Field(_)) => Err("Attempted to take the value of an unclosed field"),
            Some(State::Value(v)) => Ok(v),
        }
    }

    /// Pushes a value onto the listener or a parent state.
    #[inline]
    fn push_value(&mut self, value: T) -> ListenResult {
        match self.state.pop() {
            None => {
                self.state.push(State::Value(value));
                self.is_done = true;
                Ok(Signal::Done)
            },
            Some(State::Array(mut array)) => {
                array.push(value);
                self.state.push(State::Array(array));
                Ok(Signal::More)
            },
            Some(State::Field(name)) => {
                // It is safe to unwrap here because we ensure that a field
                // cannot be inserted out of order.
                let mut map = self.state.pop().unwrap().to_object().unwrap();
                map.insert(name, value);
                self.state.push(State::Object(map));
                Ok(Signal::More)
            },
            Some(State::Object(_)) => {
                Err(StreamError::JsonError(format!("Expected field, found value: {:?}", value)))
            },
            Some(State::Value(v)) => {
                Err(StreamError::JsonError(format!("Unexpected value: {:?}", v)))
            },
        }
    }

    /// Determines what value to push onto the listener.
    #[inline]
    fn on_value(&mut self, value: &StreamValue) -> ListenResult {
        let created_value = match *value {
            StreamValue::Bool(b) => self.creator.bool(b),
            StreamValue::Null => self.creator.null(),
            StreamValue::F64(n) => self.creator.f64(n),
            StreamValue::I64(n) => self.creator.i64(n),
            StreamValue::U64(n) => self.creator.u64(n),
            StreamValue::String(ref s) => self.creator.string((**s).to_owned()),
        };
        self.push_value(created_value)
    }
}

impl<T> Listener for ValueListener<T> where T: fmt::Debug {
    fn push(&mut self, event: &Event) -> ListenResult {
        match *event {
            Event::Value(ref value) => self.on_value(value),
            Event::StartObject => {
                self.state.push(State::Object(BTreeMap::new()));
                Ok(Signal::More)
            },
            Event::StartArray => {
                self.state.push(State::Array(Vec::new()));
                Ok(Signal::More)
            },
            Event::EndObject => {
                if let Some(State::Object(map)) = self.state.pop() {
                    let value = self.creator.object(map);
                    self.push_value(value)
                } else {
                    Err(StreamError::JsonError("Unexpected JSON token '}'".to_owned()))
                }
            },
            Event::EndArray => {
                if let Some(State::Array(values)) = self.state.pop() {
                    let value = self.creator.array(values);
                    self.push_value(value)
                } else {
                    Err(StreamError::JsonError("Unexpected JSON token ']'".to_owned()))
                }
            },
            Event::FieldName(ref name) => {
                if let Some(&State::Object(_)) = self.state.last() {
                    self.state.push(State::Field((**name).to_owned()));
                    Ok(Signal::More)
                } else {
                    Err(StreamError::JsonError(format!("Unexpected JSON field: {}", name)))
                }
            },
            Event::EndDocument => {
                self.is_done = true;
                Ok(Signal::Done)
            },
        }
    }
}

#[cfg(test)]
mod tests {
    use std::rc::Rc;
    use super::*;
    use jmespath::Variable;
    use serde_json::{Value, to_value};
    use super::super::{
        Signal,
        StreamValue,
        StreamError,
        Event,
        Listener,
        IdentityFilter,
        Emitter,
    };

    #[test]
    fn buffered_listener_receives_events() {
        let mut listener = BufferedListener::new();
        assert_eq!(Ok(Signal::More), listener.push(&Event::Value(StreamValue::U64(1))));
        assert_eq!(Ok(Signal::More), listener.push(&Event::Value(StreamValue::Null)));
        let mut events = listener.events;
        assert_eq!(Event::Value(StreamValue::U64(1)), events.pop_front().unwrap());
        assert_eq!(Event::Value(StreamValue::Null), events.pop_front().unwrap());
    }

    #[test]
    fn writes_to_string() {
        let value = Rc::new(Variable::from_json(
            "[\"a\",{\"foo\":{\"baz\":{\"bar\":\"Good!\"}}}]").unwrap());
        let mut listener = StringListener::new();
        let mut filter = IdentityFilter;
        value.emit_filter(&mut filter, &mut listener).ok();
        assert_eq!("[\"a\",{\"foo\":{\"baz\":{\"bar\":\"Good!\"}}}]", listener.as_str());
    }

    #[test]
    fn creates_serde_json_values_from_listener() {
        let value = Rc::new(Variable::from_json(
            "[\"a\",{\"foo\":{\"baz\":{\"bar\":\"Good!\",\"other\":2}}}]").unwrap());
        let serde_value = to_value(&value);
        let mut listener = ValueListener::new(Box::new(SerdeValueCreator));
        let mut filter = IdentityFilter;
        value.emit_filter(&mut filter, &mut listener).ok();
        assert_eq!(serde_value, listener.take_value().unwrap());
    }

    #[test]
    fn creates_jmespath_json_values_from_listener() {
        let value = Rc::new(Variable::from_json(
            "[\"a\",{\"foo\":{\"baz\":{\"bar\":\"Good!\",\"other\":2}}}]").unwrap());
        let mut listener = ValueListener::new(Box::new(JmesPathValueCreator));
        let mut filter = IdentityFilter;
        value.emit_filter(&mut filter, &mut listener).ok();
        assert_eq!(value, listener.take_value().unwrap());
    }

    #[test]
    fn pushes_a_single_json_value() {
        let mut listener = ValueListener::new(Box::new(SerdeValueCreator));
        assert_eq!(Ok(Signal::Done), listener.push(&Event::Value(StreamValue::Bool(true))));
        assert_eq!(Value::Bool(true), listener.take_value().unwrap());
    }

    #[test]
    fn fails_when_taking_from_empty_listener() {
        let mut listener = ValueListener::new(Box::new(SerdeValueCreator));
        assert_eq!(listener.take_value(),
                   Err("Attempted to take the value of an empty listener"));
    }

    #[test]
    fn fails_when_taking_from_unclosed_array() {
        let mut listener = ValueListener::new(Box::new(SerdeValueCreator));
        listener.push(&Event::StartArray).ok();
        assert_eq!(listener.take_value(),
                   Err("Attempted to take the value of an unclosed array"));
    }

    #[test]
    fn fails_when_taking_from_unclosed_object() {
        let mut listener = ValueListener::new(Box::new(SerdeValueCreator));
        listener.push(&Event::StartObject).ok();
        assert_eq!(listener.take_value(),
                   Err("Attempted to take the value of an unclosed object"));
    }

    #[test]
    fn fails_when_taking_from_unclosed_field() {
        let mut listener = ValueListener::new(Box::new(SerdeValueCreator));
        listener.push(&Event::StartObject).ok();
        listener.push(&Event::FieldName(Rc::new("foo".to_owned()))).ok();
        assert_eq!(listener.take_value(),
                   Err("Attempted to take the value of an unclosed field"));
    }

    #[test]
    fn fails_when_json_field_out_of_object() {
        let mut listener = ValueListener::new(Box::new(SerdeValueCreator));
        assert_eq!(listener.push(&Event::FieldName(Rc::new("foo".to_owned()))),
                   Err(StreamError::JsonError("Unexpected JSON field: foo".to_owned())));
    }

    #[test]
    fn fails_when_closing_array_out_of_order() {
        let mut listener = ValueListener::new(Box::new(SerdeValueCreator));
        assert_eq!(listener.push(&Event::EndArray),
                   Err(StreamError::JsonError("Unexpected JSON token ']'".to_owned())));
    }

    #[test]
    fn fails_when_closing_object_out_of_order() {
        let mut listener = ValueListener::new(Box::new(SerdeValueCreator));
        assert_eq!(listener.push(&Event::EndObject),
                   Err(StreamError::JsonError("Unexpected JSON token '}'".to_owned())));
    }

    #[test]
    fn fails_when_value_before_field() {
        let mut listener = ValueListener::new(Box::new(SerdeValueCreator));
        listener.push(&Event::StartObject).ok();
        assert_eq!(listener.push(&Event::Value(StreamValue::Null)),
                   Err(StreamError::JsonError("Expected field, found value: null".to_owned())));
    }

    #[test]
    fn fails_when_sending_two_values_in_a_row() {
        let mut listener = ValueListener::new(Box::new(SerdeValueCreator));
        listener.push(&Event::Value(StreamValue::Null)).ok();
        assert_eq!(listener.push(&Event::Value(StreamValue::Null)),
                   Err(StreamError::JsonError("Unexpected value: null".to_owned())));
    }
}
