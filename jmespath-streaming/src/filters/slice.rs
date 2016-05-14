//! Slice filter.

use jmespath::{RcVar, Variable};
use prelude::*;
use listeners::{ValueListener, JmesPathValueCreator};
use filters::{ArrayFilterPredicate, ArrayFilterPredicateResult, ArrayValueFilter};

/* ------------------------------------------
 * Forward slicing (e.g., [1:10:1])
 * ------------------------------------------ */

/// Creates a new forward slicing filter.
pub fn new_forward_slice(start: usize, stop: Option<usize>, step: usize) -> Box<Filter> {
    Box::new(ArrayValueFilter::new(
        Box::new(ForwardSlicePredicate::new(start, stop, step))
    ))
}

struct ForwardSlicePredicate {
    start: usize,
    stop: Option<usize>,
    step: usize,
    index: usize,
}

impl ForwardSlicePredicate {
    pub fn new(start: usize, stop: Option<usize>, step: usize) -> ForwardSlicePredicate {
        ForwardSlicePredicate {
            start: start,
            stop: stop,
            step: step,
            index: 0,
        }
    }
}

impl ArrayFilterPredicate for ForwardSlicePredicate {
    fn accept(&mut self) -> ArrayFilterPredicateResult {
        let result = self.index >= self.start
            && self.index % self.step == 0
            && (self.stop.is_none() || (self.index < self.stop.unwrap()));
        self.index += 1;
        Ok(result)
    }
}

impl Filter for ForwardSlicePredicate {
    fn filter(&mut self, event: &Event, listener: &mut Listener) -> ListenResult {
        listener.push(event)
    }

    fn reset(&mut self) {
        self.index = 0;
    }
}

/* ------------------------------------------
 * In-memory slicing for more complex slices
 * ------------------------------------------ */

pub struct ValueSliceFilter {
    is_done: bool,
    value: ValueListener<RcVar>,
    start: Option<i32>,
    stop: Option<i32>,
    step: i32,
}

impl ValueSliceFilter {
    /// Create a new ValueSliceFilter
    pub fn new(start: Option<i32>, stop: Option<i32>, step: i32) -> ValueSliceFilter {
        ValueSliceFilter {
            is_done: false,
            value: ValueListener::new(Box::new(JmesPathValueCreator)),
            start: start,
            stop: stop,
            step: step,
        }
    }

    fn send_values(&mut self, event: &Event, listener: &mut Listener) -> ListenResult {
        match try!(self.value.push(event)) {
            Signal::Done => {
                self.is_done = true;
                let value = self.value.take_value().expect("Expected completed value");
                match value.slice(&self.start, &self.stop, self.step) {
                    Some(results) => try!(Variable::Array(results).emit(listener)),
                    None => try!(listener.push(&Event::Value(StreamValue::Null))),
                };
                Ok(Signal::Done)
            },
            signal => Ok(signal),
        }
    }
}

impl Filter for ValueSliceFilter {
    fn filter(&mut self, event: &Event, listener: &mut Listener) -> ListenResult {
        if self.is_done {
            Ok(Signal::Done)
        } else {
            self.send_values(event, listener)
        }
    }

    fn reset(&mut self) {
        self.is_done = false;
        self.value.reset();
    }
}

#[cfg(test)]
mod tests {
    use tests::run_test_cases;

    #[test]
    fn filters_forward_slices() {
        let data = "[0,1,2,3,4,5,6,7,8,9]";
        run_test_cases(vec![
            ("[1:3]", "1", "null"),
            ("[1:3]", data, "[1,2]"),
            ("[1:8]", data, "[1,2,3,4,5,6,7]"),
            ("[2:8:2]", data, "[2,4,6]"),
            ("[2:3]", data, "[2]"),
            ("[2::2]", data, "[2,4,6,8]"),
            ("[::2]", data, "[0,2,4,6,8]"),
        ]);
    }

    #[test]
    fn filters_in_memory_negative_slices() {
        let data = "[0,1,2,3,4,5,6,7,8,9]";
        run_test_cases(vec![
            ("[1:3:-1]", "1", "null"),
            ("[-5::]", data, "[5,6,7,8,9]"),
        ]);
    }
}
