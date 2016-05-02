//! Streaming JMESPath support implemented using state machine filtes.

extern crate jmespath;
extern crate serde;
extern crate serde_json;

use self::comparison::{EqualityFilter, OrderingFilter};
use self::condition::ConditionFilter;
use self::field::FieldFilter;
use self::flatten::new_flatten;
use self::index::{IndexFilter, NegativeIndexFilter};
use self::literal::LiteralFilter;
use self::multi_list::MultiListFilter;
use self::multi_hash::MultiHashFilter;
use self::not::NotFilter;
use self::and_or::AndOrFilter;
use self::object_values::ObjectValuesFilter;
use self::projection::new_projection;
use self::slice::{ValueSliceFilter, new_forward_slice};

pub mod listener;

mod and_or;
mod comparison;
mod condition;
mod field;
mod flatten;
mod slice;
mod index;
mod literal;
mod multi_list;
mod multi_hash;
mod not;
mod object_values;
mod projection;

use std::fmt;
use std::rc::Rc;
use serde_json::Value;

use jmespath::{Variable, Context, Error, ErrorReason, RuntimeError};
use jmespath::ast::{Ast, Comparator};
use jmespath::functions::FnRegistry;

pub type ListenResult = Result<Signal, StreamError>;

/// Receives streamed JSON events and returns a signal to the emitter to know
/// if an error occurred and whether or not to stop parsing before the end of
/// the stream.
pub trait Listener {
    fn push(&mut self, event: &Event) -> ListenResult;
}

/// Filters JSON events, passing events into a Listener.
pub trait Filter {
    /// Given the event, filter it and send event(s) to the listener.
    fn filter(&mut self, event: &Event, listener: &mut Listener) -> ListenResult;

    /// Reset the state of the filter so that it can be reused.
    fn reset(&mut self) {
        // By default, does nothing.
    }
}

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

#[derive(Debug, Clone, PartialEq)]
pub enum Signal {
    More,
    Done
}

#[derive(Debug, Clone, PartialEq)]
pub enum StreamError {
    JsonError(String),
    JmesPathError(String),
}

/// Compiles an AST into a stream filter.
pub fn compile_filter(ast: &Ast, ctx: &mut Context) -> Result<Box<Filter>, Error> {
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
            Ok(Box::new(ValueSliceFilter::new(start.clone(), stop.clone(), step.clone())))
        },
        Ast::Function { ref name, ref args, offset } => {
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
        },
    }
}

/// Event listener that filters events before sending them to a listener.
pub struct FilteredListener<'a> {
    pub filter: &'a mut Filter,
    pub listener: &'a mut Listener,
}

impl<'a> FilteredListener<'a> {
    #[inline]
    pub fn new(filter: &'a mut Filter, listener: &'a mut Listener) -> FilteredListener<'a> {
        FilteredListener {
            filter: filter,
            listener: listener,
        }
    }
}

impl<'a> Listener for FilteredListener<'a> {
    #[inline]
    fn push(&mut self, event: &Event) -> ListenResult {
        self.filter.filter(event, self.listener)
    }
}

/// Filter that is used when a streaming function is not implemented.
pub struct NotImplementedFilter;

impl Filter for NotImplementedFilter {
    fn filter(&mut self, _event: &Event, _target: &mut Listener) -> ListenResult {
        Err(StreamError::JmesPathError(
            "Invoked a function that does not implement filter".to_owned()
        ))
    }
}

/// Filter that forwards all events to the Listener
pub struct IdentityFilter;

impl Filter for IdentityFilter {
    fn filter(&mut self, event: &Event, target: &mut Listener) -> ListenResult {
        target.push(event)
    }
}

/// Sends the result of filtering on LHS to RHS.
pub struct PipedFilter {
    a: Box<Filter>,
    b: Box<Filter>,
}

impl PipedFilter {
    #[inline]
    pub fn new(a: Box<Filter>, b: Box<Filter>) -> PipedFilter {
        PipedFilter {
            a: a,
            b: b,
        }
    }
}

impl Filter for PipedFilter {
    #[inline]
    fn filter(&mut self, event: &Event, listener: &mut Listener) -> ListenResult {
        let mut filtered_listener = FilteredListener::new(&mut *self.b, listener);
        self.a.filter(event, &mut filtered_listener)
    }

    #[inline]
    fn reset(&mut self) {
        self.a.reset();
        self.b.reset();
    }
}

/// Passes an entire value, ensuring it is not sent to the listener.
struct SkipValueFilter {
    pending: EventStack,
}

impl SkipValueFilter {
    #[inline]
    pub fn new() -> SkipValueFilter {
        SkipValueFilter {
            pending: EventStack::new(),
        }
    }
}

impl Filter for SkipValueFilter {
    #[inline]
    fn filter(&mut self, event: &Event, _listener: &mut Listener) -> ListenResult {
        match *event {
            Event::StartObject => {
                self.pending.push_object();
                return Ok(Signal::More);
            },
            Event::StartArray => {
                self.pending.push_array();
                return Ok(Signal::More);
            },
            Event::EndObject => try!(self.pending.pop_object()),
            Event::EndArray => try!(self.pending.pop_array()),
            Event::EndDocument => return self.pending.end_document(),
            _ => {}
        }
        if self.pending.is_empty() {
            Ok(Signal::Done)
        } else {
            Ok(Signal::More)
        }
    }

    fn reset(&mut self) {
        self.pending = EventStack::new();
    }
}

/// Sends an entire value to a listener
struct SendValueFilter {
    pending: EventStack,
    allow_early_termination: bool,
}

impl SendValueFilter {
    #[inline]
    pub fn new(allow_early_termination: bool) -> SendValueFilter {
        SendValueFilter {
            pending: EventStack::new(),
            allow_early_termination: allow_early_termination,
        }
    }
}

impl Filter for SendValueFilter {
    #[inline]
    fn filter(&mut self, event: &Event, listener: &mut Listener) -> ListenResult {
        let listener_result = match *event {
            Event::StartObject => {
                self.pending.push_object();
                return listener.push(event);
            },
            Event::StartArray => {
                self.pending.push_array();
                return listener.push(event);
            },
            Event::EndObject => {
                try!(self.pending.pop_object());
                try!(listener.push(event))
            },
            Event::EndArray => {
                try!(self.pending.pop_array());
                try!(listener.push(event))
            },
            Event::EndDocument => return self.pending.end_document(),
            _ => try!(listener.push(event))
        };
        if self.pending.is_empty() {
            Ok(Signal::Done)
        } else if self.allow_early_termination {
            Ok(listener_result)
        } else {
            Ok(Signal::More)
        }
    }

    fn reset(&mut self) {
        self.pending = EventStack::new();
    }
}

enum NotExpectState {
    Expecting,
    Forwarding,
    Rejecting,
}

/// Filter that expects anything other than a specific event.
struct NotExpectFilter {
    event: Event,
    state: NotExpectState,
}

impl NotExpectFilter {
    #[inline]
    pub fn new(event: Event) -> NotExpectFilter {
        NotExpectFilter {
            event: event,
            state: NotExpectState::Expecting,
        }
    }
}

impl Filter for NotExpectFilter {
    fn filter(&mut self, event: &Event, listener: &mut Listener) -> ListenResult {
        match self.state {
            NotExpectState::Expecting => {
                if *event != self.event {
                    self.state = NotExpectState::Forwarding;
                    listener.push(event)
                } else {
                    self.state = NotExpectState::Rejecting;
                    Ok(Signal::Done)
                }
            },
            NotExpectState::Forwarding => listener.push(event),
            NotExpectState::Rejecting => Ok(Signal::Done),
        }
    }

    fn reset(&mut self) {
        self.state = NotExpectState::Expecting;
    }
}

/* ------------------------------------------
 * Event stack
 * ------------------------------------------ */

/// Closing tokens that are pending.
#[derive(Debug, Clone, PartialEq)]
pub enum PendingToken {
    Object,
    Array
}

/// Handles account for pending closing tokens in a stack.
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
 * Emitters
 * ------------------------------------------ */

macro_rules! emit_event {
    ($listener:expr, $event:expr) => {
        if let Signal::Done = try!($listener.push($event)) {
            return Ok(Signal::Done);
        }
    };
}

/// Emits events to a Listener.
pub trait Emitter {
    /// Emits values from the emitter into a listener.
    fn emit(&self, listener: &mut Listener) -> ListenResult;

    /// Emits filtered values from the emitter into a listener.
    fn emit_filter(&self, filter: &mut Filter, listener: &mut Listener) -> ListenResult {
        self.emit(&mut FilteredListener::new(filter, listener))
    }
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

/* ------------------------------------------
 * Array filtering
 * ------------------------------------------ */

pub type ArrayFilterPredicateResult = Result<bool, StreamError>;

pub trait ArrayFilterPredicate : Filter {
    /// Signals to the predicate that a new value is about to be sent.
    /// The predicate can accept the value by returning Ok(true), reject
    /// it, skipping the value, by returning Ok(false), or cause an error
    // by returning an Err..
    fn accept(&mut self) -> ArrayFilterPredicateResult;
}

struct DefaultArrayFilterPredicate {
    filter: Box<Filter>,
}

impl DefaultArrayFilterPredicate {
    pub fn new(filter: Box<Filter>) -> DefaultArrayFilterPredicate {
        DefaultArrayFilterPredicate {
            filter: filter,
        }
    }
}

impl ArrayFilterPredicate for DefaultArrayFilterPredicate {
    fn accept(&mut self) -> ArrayFilterPredicateResult {
        self.filter.reset();
        Ok(true)
    }
}

impl Filter for DefaultArrayFilterPredicate {
    fn filter(&mut self, event: &Event, listener: &mut Listener) -> ListenResult {
        self.filter.filter(event, listener)
    }

    fn reset(&mut self) {
        self.filter.reset();
    }
}

#[derive(Debug)]
enum ArrayFilterState {
    ExpectArray,
    FilterValue,
    SendValue,
    SkipValue,
    Done,
}

/// Filters and maps events emitted from array values hrough a predicate.
///
/// If the first event is not an array, this filter emits null. Each value
/// emit is emitted through the predicate until the value has finished or
/// until the predicate returns Done. Once an entire value has been emitted
/// through the predicate, the predicate is reset so that it may receive the
/// next value, until finally, the EndArray event is emitted to close out.
pub struct ArrayValueFilter {
    state: ArrayFilterState,
    predicate: Box<ArrayFilterPredicate>,
    send_value_filter: SendValueFilter,
    skip_value_filter: SkipValueFilter,
}

impl ArrayValueFilter {
    /// Creates a new ArrayValueFilter.
    ///
    /// The `predicate` filter receives each event emitted from an array value
    /// and the listener that was intended to receive the event. The predicate
    /// is free to not emit events it receives (filtering) or to map and
    /// transform events before passing them on to the listener.
    #[inline]
    pub fn new(predicate: Box<ArrayFilterPredicate>) -> ArrayValueFilter {
        ArrayValueFilter {
            state: ArrayFilterState::ExpectArray,
            predicate: predicate,
            send_value_filter: SendValueFilter::new(false),
            skip_value_filter: SkipValueFilter::new(),
        }
    }

    #[inline]
    fn expect_array_state(&mut self, event: &Event, listener: &mut Listener) -> ListenResult {
        match *event {
            Event::StartArray => {
                match try!(listener.push(event)) {
                    Signal::Done => {
                        // The listener doesn't want an array, so stop.
                        self.state = ArrayFilterState::Done;
                        Ok(Signal::Done)
                    },
                    Signal::More => {
                        // The array was accepted, so transition to emitting
                        // events mapped through the predicate.
                        self.state = ArrayFilterState::FilterValue;
                        Ok(Signal::More)
                    }
                }
            },
            _ => {
                // Received something that was not an array so emit null.
                self.state = ArrayFilterState::Done;
                send_null(listener)
            }
        }
    }

    #[inline]
    fn filter_value_state(&mut self, event: &Event, listener: &mut Listener) -> ListenResult {
        match *event {
            Event::EndArray => {
                // When the outer array is closed, we need to emit the event
                // the listener and transition to the done state.
                self.state = ArrayFilterState::Done;
                try!(listener.push(event));
                Ok(Signal::Done)
            },
            _ => {
                // Another value was received, so ask the predicate to accept.
                // If accepted, begin emitting mapped events through the predicate
                // map/filter function.
                if !try!(self.predicate.accept()) {
                    self.state = ArrayFilterState::SkipValue;
                    self.filter(event, listener)
                } else {
                    self.state = ArrayFilterState::SendValue;
                    self.filter(event, listener)
                }
            }
        }
    }
}

impl Filter for ArrayValueFilter {
    fn filter(&mut self, event: &Event, listener: &mut Listener) -> ListenResult {
        match self.state {
            ArrayFilterState::ExpectArray => self.expect_array_state(event, listener),
            ArrayFilterState::FilterValue => self.filter_value_state(event, listener),
            ArrayFilterState::SendValue => {
                let result = {
                    let mut filtered = FilteredListener::new(&mut self.predicate, listener);
                    try!(self.send_value_filter.filter(event, &mut filtered))
                };
                if let Signal::Done = result {
                    self.state = ArrayFilterState::FilterValue;
                    self.send_value_filter.reset();
                }
                Ok(Signal::More)
            },
            ArrayFilterState::SkipValue => {
                if let Signal::Done = try!(self.skip_value_filter.filter(event, listener)) {
                    // Received the Done signal from the predicate, so begin
                    // filtering and emit the next value.
                    self.state = ArrayFilterState::FilterValue;
                    self.skip_value_filter.reset();
                }
                Ok(Signal::More)
            },
            ArrayFilterState::Done => Ok(Signal::Done),
        }
    }

    fn reset(&mut self) {
        self.predicate.reset();
        self.state = ArrayFilterState::ExpectArray;
    }
}

#[cfg(test)]
mod tests {
    use std::rc::Rc;
    use super::*;
    use jmespath::{Expression, Context, Variable};
    use jmespath::functions::BuiltinFnRegistry;
    use listener::StringListener;

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
