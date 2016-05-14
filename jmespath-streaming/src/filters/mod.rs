//! JMESPath streaming event filters.

mod and_or;
mod array_value_filter;
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

// Re-export all of the filters from listeners::*.
pub use self::and_or::AndOrFilter;
pub use self::array_value_filter::ArrayFilterPredicate;
pub use self::array_value_filter::ArrayFilterPredicateResult;
pub use self::array_value_filter::ArrayValueFilter;
pub use self::array_value_filter::DefaultArrayFilterPredicate;
pub use self::comparison::EqualityFilter;
pub use self::comparison::OrderingFilter;
pub use self::condition::ConditionFilter;
pub use self::field::FieldFilter;
pub use self::flatten::new_flatten;
pub use self::index::IndexFilter;
pub use self::index::NegativeIndexFilter;
pub use self::literal::LiteralFilter;
pub use self::multi_hash::MultiHashFilter;
pub use self::multi_list::MultiListFilter;
pub use self::not::NotFilter;
pub use self::object_values::ObjectValuesFilter;
pub use self::projection::new_projection;
pub use self::slice::ValueSliceFilter;
pub use self::slice::new_forward_slice;

use super::prelude::*;
use super::EventStack;
use super::listeners::FilteredListener;

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
