//! Streaming JMESPath support implemented using state machine filters.

extern crate jmespath;
extern crate serde;
extern crate serde_json;

pub mod emitters;
pub mod filters;
pub mod listeners;
pub mod prelude;

use std::fmt;
use std::rc::Rc;

use jmespath::{Context, Error, ErrorReason, RuntimeError};
use jmespath::ast::{Ast, Comparator};
use jmespath::functions::FnRegistry;

use listeners::FilteredListener;

/// Result of emitting a stream Event.
pub type ListenResult = Result<Signal, StreamError>;

/// Synchronously Emits events to a Listener.
///
/// `Emitter`s should emit all of the JMESPath events necessary
/// to represent the `Emitter` state to a `Listener`. For each event, the
/// Emitter must check if the `Listener` wishes to continue by inspecting the
/// return `Signal`. A `Signal::Done` event tells the `Emitter` to stop
/// emitting events, while `Signal::More` tells the `Emitter` to continue.
pub trait Emitter {
    /// Emits values from the emitter into a listener.
    fn emit(&self, listener: &mut Listener) -> ListenResult;

    /// Emits filtered values from the emitter into a listener.
    fn emit_filter(&self, filter: &mut Filter, listener: &mut Listener) -> ListenResult {
        self.emit(&mut FilteredListener::new(filter, listener))
    }
}

/// Receives stream JSON events and signals whether or not to continue.
///
/// Listeners receive JSON events and returns a `Signal` to the signal to the
/// emitter (i.e., caller) whether or not the listener should receive
/// subsequent events.
///
/// When Signal::Done is returned, the emitter/caller should not continue
/// to send events to the listener, however, it is possible that that
/// emitters will continue to emit even after a Done signal.
pub trait Listener {
    fn push(&mut self, event: &Event) -> ListenResult;
}

/// Filters JSON events, passing events into a Listener.
///
/// `Filter`s receive Events and can choose to forward the event as-is to a
/// `Listener`, or they may choose to buffer events until some kind of state
/// transition can be determined. In addition to filtering events from an
/// emitter to a Listener, Filters can create entirely new events.
pub trait Filter {
    /// Given an `Event`, filter it and send zero or more event(s) to the `Listener`.
    fn filter(&mut self, event: &Event, listener: &mut Listener) -> ListenResult;

    /// Reset the state of the filter so that it can be reused.
    fn reset(&mut self) {}
}

/// Implements `Filter` for a Boxed `Filter`.
impl<T: ?Sized> Filter for Box<T> where T: Filter {
    fn filter(&mut self, event: &Event, listener: &mut Listener) -> ListenResult {
        (**self).filter(event, listener)
    }

    fn reset(&mut self) {
        (**self).reset()
    }
}

/// Sends null to the listener and returns Done signal.
fn send_null(target: &mut Listener) -> ListenResult {
    try!(target.push(&Event::Value(StreamValue::Null)));
    Ok(Signal::Done)
}

/// Signals to an emitter whether or not a `Listener` wants more `Events`.
#[derive(Debug, Clone, PartialEq)]
pub enum Signal {
    /// The `Listener` wants to receive more events.
    More,
    /// The `Listener` does not want to receive more events.
    Done
}

/// Represents an error occurred while listening or filtering events.
#[derive(Debug, Clone, PartialEq)]
pub enum StreamError {
    /// A JSON error occurred (e.g., invalid syntax, mangled ordering, etc.)
    JsonError(String),
    /// A JMESPath error occurred (e.g., an invalid type).
    JmesPathError(String),
}

/// JMESPath JSON event.
#[derive(Debug, Clone, PartialEq)]
pub enum Event {
    StartObject,
    EndObject,
    FieldName(Rc<String>),
    StartArray,
    EndArray,
    Value(StreamValue),
    EndDocument,
}

impl Event {
    pub fn as_number(&self) -> Option<f64> {
        match *self {
            Event::Value(ref v) => v.as_number(),
            _ => None
        }
    }
}

/// JSON Event scalar stream value.
#[derive(Debug, Clone, PartialEq)]
pub enum StreamValue {
    Null,
    String(Rc<String>),
    I64(i64),
    U64(u64),
    F64(f64),
    Bool(bool),
}

impl StreamValue {
    /// Attempts to represent the StreamValue as a number.
    pub fn as_number(&self) -> Option<f64> {
        match *self {
            StreamValue::F64(f) => Some(f),
            StreamValue::I64(i) => Some(i as f64),
            StreamValue::U64(u) => Some(u as f64),
            _ => None,
        }
    }
}

impl fmt::Display for StreamValue {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match *self {
            StreamValue::Bool(true) => write!(fmt, "true"),
            StreamValue::Bool(false) => write!(fmt, "false"),
            StreamValue::Null => write!(fmt, "null"),
            StreamValue::String(ref s) => write!(fmt, "{:?}", s),
            StreamValue::F64(ref n) => write!(fmt, "{}", n),
            StreamValue::I64(ref n) => write!(fmt, "{}", n),
            StreamValue::U64(ref n) => write!(fmt, "{}", n),
        }
    }
}

/* ------------------------------------------
 * Event stack
 * ------------------------------------------ */

/// Closing tokens that are pending.
#[derive(Debug, Clone, PartialEq)]
enum PendingToken {
    Object,
    Array
}

/// Validates the order of open and close events that flow through.
#[derive(Debug, Clone, PartialEq)]
pub struct EventStack {
    events: Vec<PendingToken>
}

impl EventStack {
    /// Create a new EventStack container.
    #[inline]
    pub fn new() -> EventStack {
        EventStack {
            events: Vec::new()
        }
    }

    /// Clears out any pending events.
    pub fn clear(&mut self) {
        self.events.clear();
    }

    /// Pushes a pending object event.
    #[inline]
    pub fn push_object(&mut self) {
        self.events.push(PendingToken::Object);
    }

    /// Pushes a pending array event.
    #[inline]
    pub fn push_array(&mut self) {
        self.events.push(PendingToken::Array);
    }

    /// Checks if there are no more pending events.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.events.is_empty()
    }

    /// Pops a pending event and ensures it is an array.
    pub fn pop_array(&mut self) -> Result<(), StreamError> {
        match self.events.pop() {
            Some(PendingToken::Array) => Ok(()),
            Some(PendingToken::Object) => {
                Err(StreamError::JsonError("Expected ']', but received '}'".to_owned()))
            },
            _ => Err(StreamError::JsonError("Unexpected token: ]".to_owned()))
        }
    }

    /// Pops a pending event and ensures it is an object.
    pub fn pop_object(&mut self) -> Result<(), StreamError> {
        match self.events.pop() {
            Some(PendingToken::Object) => Ok(()),
            Some(PendingToken::Array) => {
                Err(StreamError::JsonError("Expected '}', but received ']'".to_owned()))
            },
            _ => Err(StreamError::JsonError("Unexpected token: }".to_owned()))
        }
    }

    /// Ensures that the document is closed correctly.
    pub fn end_document(&mut self) -> ListenResult {
        if self.is_empty() {
            Ok(Signal::Done)
        } else {
            Err(StreamError::JsonError(format!("Unclosed elements: {:?}", self.events)))
        }
    }
}

/* ------------------------------------------
 * Event filter compiler
 * ------------------------------------------ */

/// Compiles a JMESPath AST into a stream filter.
///
/// If the expression cannot be compiled into a filter, then an Error is
/// returned. This can happen, for example, when a functiont that works in
/// an in-memory context cannot be executed from a streaming context.
pub fn compile_filter(ast: &Ast, ctx: &mut Context) -> Result<Box<Filter>, Error> {
    use filters::*;

    match *ast {
        Ast::Subexpr { ref lhs, ref rhs, .. } => {
            Ok(Box::new(PipedFilter::new(
                try!(compile_filter(lhs, ctx)),
                try!(compile_filter(rhs, ctx))
            )))
        },
        Ast::Field { ref name, .. } => Ok(Box::new(FieldFilter::new(name))),
        Ast::Index { idx, .. } => {
            if idx < 0 {
                Ok(Box::new(NegativeIndexFilter::new(idx.abs() as usize)))
            } else {
                Ok(Box::new(IndexFilter::new(idx as usize)))
            }
        },
        Ast::Or { ref lhs, ref rhs, .. } => {
            Ok(Box::new(AndOrFilter::new_or(
                try!(compile_filter(lhs, ctx)),
                try!(compile_filter(rhs, ctx))
            )))
        },
        Ast::And { ref lhs, ref rhs, .. } => {
            Ok(Box::new(AndOrFilter::new_and(
                try!(compile_filter(lhs, ctx)),
                try!(compile_filter(rhs, ctx))
            )))
        },
        Ast::Flatten { ref node, .. } => {
            Ok(new_flatten(try!(compile_filter(node, ctx))))
        },
        Ast::Identity { .. } => Ok(Box::new(IdentityFilter)),
        Ast::Projection { ref lhs, ref rhs, .. } => {
            Ok(new_projection(
                try!(compile_filter(lhs, ctx)),
                try!(compile_filter(rhs, ctx))
            ))
        },
        Ast::Literal { ref value, .. } => {
            Ok(Box::new(LiteralFilter::new(Box::new(value.clone()))))
        },
        Ast::ObjectValues { ref node, .. } => {
            Ok(Box::new(PipedFilter::new(
                try!(compile_filter(node, ctx)),
                Box::new(ObjectValuesFilter::new())
            )))
        },
        Ast::MultiList { ref elements, .. } => {
            let mut filters = Vec::with_capacity(elements.len());
            for ele in elements {
                filters.push(try!(compile_filter(ele, ctx)));
            }
            Ok(Box::new(MultiListFilter::new(filters)))
        },
        Ast::MultiHash { ref elements, .. } => {
            let mut filters = Vec::with_capacity(elements.len());
            for kvp in elements {
                let value = try!(compile_filter(&kvp.value, ctx));
                filters.push((Rc::new(kvp.key.clone()), value));
            }
            Ok(Box::new(MultiHashFilter::new(filters)))
        },
        Ast::Not { ref node, .. } => {
            Ok(Box::new(PipedFilter::new(
                try!(compile_filter(node, ctx)),
                Box::new(NotFilter::new())
            )))
        },
        Ast::Condition { ref predicate, ref then, .. } => {
            Ok(Box::new(ConditionFilter::new(
                try!(compile_filter(predicate, ctx)),
                try!(compile_filter(then, ctx))
            )))
        },
        Ast::Comparison { ref comparator, ref lhs, ref rhs, .. } => {
            let lhs = try!(compile_filter(lhs, ctx));
            let rhs = try!(compile_filter(rhs, ctx));
            Ok(match *comparator {
                Comparator::Eq(ref c) => Box::new(EqualityFilter::new(lhs, rhs, c.clone())),
                Comparator::Ord(ref c) => Box::new(OrderingFilter::new(lhs, rhs, c.clone())),
            })
        },
        Ast::Expref { ref ast, .. } => compile_filter(ast, ctx),
        Ast::Slice { ref start, ref stop, step, .. } => {
            if step > 0 {
                match (start, stop) {
                    (&None, &None) => return Ok(new_forward_slice(0, None, step as usize)),
                    (&None, &Some(b)) if b > 0 => {
                        return Ok(new_forward_slice(0, Some(b as usize), step as usize))
                    },
                    (&Some(a), &Some(b)) if a >= 0 && b >= 0 => {
                        return Ok(new_forward_slice(a as usize, Some(b as usize), step as usize))
                    },
                    (&Some(a), &None) if a >= 0 => {
                        return Ok(new_forward_slice(a as usize, None, step as usize))
                    },
                    _ => {}
                }
            }
            Ok(Box::new(ValueSliceFilter::new(start.clone(), stop.clone(), step)))
        },
        Ast::Function { ref name, ref args, offset } => compile_function(name, args, offset, ctx),
    }
}

/// Compiles a function stream filter.
fn compile_function(name: &str, args: &Vec<Ast>, offset: usize, ctx: &mut Context)
        -> Result<Box<Filter>, Error> {
    ctx.offset = offset;
    match ctx.fn_registry.get_signature(name) {
        None => {
            Err(Error::from_ctx(ctx, ErrorReason::Runtime(
                RuntimeError::UnknownFunction(name.to_owned())
            )))
        },
        Some(signature) => {
            try!(signature.validate_arity(ctx, args.len()));
            let mut compiled_args = Vec::with_capacity(args.len());
            for arg in args {
                compiled_args.push(try!(compile_filter(arg, ctx)));
            }
            // let args_filter = Box::new(MultiListFilter::new(compiled_args));
            panic!("Functions are not yet implemented");
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::rc::Rc;
    use jmespath::{Expression, Context, Variable};
    use jmespath::functions::BuiltinFnRegistry;
    use listeners::StringListener;

    pub fn run_test_cases(cases: Vec<(&str, &str, &str)>) {
        for (expr, json, result) in cases {
            println!("{:?}, {:?}, {:?}", expr, json, result);
            let expression = Expression::new(expr).unwrap();
            let registry = BuiltinFnRegistry::new();
            let mut ctx = Context::new(expr, &registry);
            let mut filter = compile_filter(expression.as_ast(), &mut ctx).unwrap();
            let mut listener = StringListener::new();
            let value = Variable::from_json(json).unwrap();
            value.emit_filter(&mut filter, &mut listener).ok();
            assert_eq!(result, listener.as_str());
        }
    }

    #[test]
    fn handles_subexpressions_using_recursion() {
        let value = Rc::new(Variable::from_json(
            "{\"foo\":{\"baz\":{\"bar\":\"Good!\"}}}").unwrap());
        let expr = "foo.baz.bar";
        let expression = Expression::new(expr).unwrap();
        let registry = BuiltinFnRegistry::new();
        let mut ctx = Context::new(expr, &registry);
        let mut filter = compile_filter(expression.as_ast(), &mut ctx).unwrap();
        let mut listener = StringListener::new();
        value.emit_filter(&mut filter, &mut listener).ok();
        assert_eq!("\"Good!\"", listener.as_str());
    }
}
