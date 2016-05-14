//! Performs array value filtering.

use prelude::*;
use send_null;
use listeners::FilteredListener;
use filters::{SkipValueFilter, SendValueFilter};

pub type ArrayFilterPredicateResult = Result<bool, StreamError>;

pub trait ArrayFilterPredicate : Filter {
    /// Signals to the predicate that a new value is about to be sent.
    /// The predicate can accept the value by returning Ok(true), reject
    /// it, skipping the value, by returning Ok(false), or cause an error
    // by returning an Err..
    fn accept(&mut self) -> ArrayFilterPredicateResult;
}

pub struct DefaultArrayFilterPredicate {
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
