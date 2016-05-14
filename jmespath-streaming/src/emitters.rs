///! JMESPath streaming event emitters.

use std::rc::Rc;

use serde_json::Value;

use jmespath::Variable;
use prelude::*;

/// Macro to emit an event and return early if the listener returns Done.
macro_rules! emit_event {
    ($listener:expr, $event:expr) => {
        if let Signal::Done = try!($listener.push($event)) {
            return Ok(Signal::Done);
        }
    };
}

impl<'a, T> Emitter for &'a T where T: Emitter {
    fn emit(&self, listener: &mut Listener) -> ListenResult {
        (**self).emit(listener)
    }
}

impl<T> Emitter for Rc<T> where T: Emitter {
    fn emit(&self, listener: &mut Listener) -> ListenResult {
        (**self).emit(listener)
    }
}

impl<T> Emitter for Box<T> where T: Emitter {
    fn emit(&self, listener: &mut Listener) -> ListenResult {
        (**self).emit(listener)
    }
}

/// Emits Events from a JMESPath Variable.
impl Emitter for Variable {
    fn emit(&self, listener: &mut Listener) -> ListenResult {
        match *self {
            Variable::Expref(_) => {
                Err(StreamError::JmesPathError("Cannot emit expref".to_owned()))
            },
            Variable::Null => listener.push(&Event::Value(StreamValue::Null)),
            Variable::I64(i) => listener.push(&Event::Value(StreamValue::I64(i))),
            Variable::F64(f) => listener.push(&Event::Value(StreamValue::F64(f))),
            Variable::U64(u) => listener.push(&Event::Value(StreamValue::U64(u))),
            Variable::Bool(b) => listener.push(&Event::Value(StreamValue::Bool(b))),
            Variable::String(ref s) => {
                listener.push(&Event::Value(StreamValue::String(Rc::new(s.to_owned()))))
            },
            Variable::Array(ref a) => {
                emit_event!(listener, &Event::StartArray);
                for v in a.iter() {
                    try!(v.emit(listener));
                }
                listener.push(&Event::EndArray)
            },
            Variable::Object(ref o) => {
                emit_event!(listener, &Event::StartObject);
                for (k, v) in o.iter() {
                    emit_event!(listener, &Event::FieldName(Rc::new(k.to_owned())));
                    try!(v.emit(listener));
                }
                listener.push(&Event::EndObject)
            }
        }
    }
}

/// Emits JMESPath events from a Serde Value.
impl Emitter for Value {
    fn emit(&self, listener: &mut Listener) -> ListenResult {
        match *self {
            Value::Null => listener.push(&Event::Value(StreamValue::Null)),
            Value::I64(i) => listener.push(&Event::Value(StreamValue::I64(i))),
            Value::F64(f) => listener.push(&Event::Value(StreamValue::F64(f))),
            Value::U64(u) => listener.push(&Event::Value(StreamValue::U64(u))),
            Value::Bool(b) => listener.push(&Event::Value(StreamValue::Bool(b))),
            Value::String(ref s) => {
                listener.push(&Event::Value(StreamValue::String(Rc::new(s.to_owned()))))
            },
            Value::Array(ref a) => {
                emit_event!(listener, &Event::StartArray);
                for v in a.iter() {
                    if let Signal::Done = try!(v.emit(listener)) {
                        return Ok(Signal::Done);
                    }
                }
                listener.push(&Event::EndArray)
            },
            Value::Object(ref o) => {
                emit_event!(listener, &Event::StartObject);
                for (k, v) in o.iter() {
                    emit_event!(listener, &Event::FieldName(Rc::new(k.to_owned())));
                    if let Signal::Done = try!(v.emit(listener)) {
                        return Ok(Signal::Done);
                    }
                }
                listener.push(&Event::EndObject)
            }
        }
    }
}
