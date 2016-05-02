use jmespath::RcVar;
use jmespath::ast::{OrdComparator, EqComparator};
use listener::{BufferedListener, ValueListener, JmesPathValueCreator};
use Listener;
use ListenResult;
use Filter;
use Event;
use Signal;
use StreamValue;

/* ------------------------------------------
 * Equality comparisons
 * ------------------------------------------ */

/// Compares LHS and RHS equality, emitting true/false/null.
///
/// Note: equality comparisons require that the entire representation
/// of a value is buffered into memory. Avoid using equality comparisons
/// large data sets if possible.
pub struct EqualityFilter {
    lhs: Box<Filter>,
    rhs: Box<Filter>,
    is_done: bool,
    lhs_value: ValueListener<RcVar>,
    rhs_value: ValueListener<RcVar>,
    comparator: EqComparator,
}

impl EqualityFilter {
    /// Create a new EqualityFilter
    pub fn new(lhs: Box<Filter>, rhs: Box<Filter>, comparator: EqComparator) -> EqualityFilter {
        EqualityFilter {
            lhs: lhs,
            rhs: rhs,
            lhs_value: ValueListener::new(Box::new(JmesPathValueCreator)),
            rhs_value: ValueListener::new(Box::new(JmesPathValueCreator)),
            comparator: comparator,
            is_done: false,
        }
    }

    /// Transition the filter to the done state.
    fn transition_done(&mut self, event: Event, listener: &mut Listener) -> ListenResult {
        try!(listener.push(&event));
        self.reset();
        self.is_done = true;
        Ok(Signal::Done)
    }

    fn send_values(&mut self, event: &Event, listener: &mut Listener) -> ListenResult {
        let lhs_done = self.lhs_value.is_complete()
            || match try!(self.lhs.filter(event, &mut self.lhs_value)) {
                Signal::Done => true,
                Signal::More => false,
            };
        let rhs_done = self.rhs_value.is_complete()
            || match try!(self.rhs.filter(event, &mut self.rhs_value)) {
                Signal::Done => true,
                Signal::More => false,
            };

        if !lhs_done || !rhs_done {
            return Ok(Signal::More);
        }

        let lhs_value = self.lhs_value.take_value().unwrap();
        let rhs_value = self.rhs_value.take_value().unwrap();
        let emit_event = match lhs_value.compare_equality(&self.comparator, &rhs_value) {
            Some(result) => Event::Value(StreamValue::Bool(result)),
            None => Event::Value(StreamValue::Null),
        };
        self.transition_done(emit_event, listener)
    }
}

impl Filter for EqualityFilter {
    fn filter(&mut self, event: &Event, listener: &mut Listener) -> ListenResult {
        if self.is_done {
            Ok(Signal::Done)
        } else {
            self.send_values(event, listener)
        }
    }

    fn reset(&mut self) {
        self.is_done = false;
        self.lhs.reset();
        self.rhs.reset();
        self.lhs_value.reset();
        self.rhs_value.reset();
    }
}

/* ------------------------------------------
 * Ordering comparisons
 * ------------------------------------------ */

/// Compares LHS and RHS ordering, emitting true/false/null.
pub struct OrderingFilter {
    lhs: Box<Filter>,
    rhs: Box<Filter>,
    lhs_buffer: BufferedListener,
    rhs_buffer: BufferedListener,
    comparator: OrdComparator,
    is_done: bool,
}

impl OrderingFilter {
    /// Create a new OrderingFilter.
    pub fn new(lhs: Box<Filter>, rhs: Box<Filter>, comparator: OrdComparator) -> OrderingFilter {
        OrderingFilter {
            lhs: lhs,
            rhs: rhs,
            lhs_buffer: BufferedListener::new(),
            rhs_buffer: BufferedListener::new(),
            comparator: comparator,
            is_done: false,
        }
    }

    fn send_null(&mut self, listener: &mut Listener) -> ListenResult {
        try!(listener.push(&Event::Value(StreamValue::Null)));
        self.transition_done()
    }

    fn send_bool(&mut self, result: bool, listener: &mut Listener) -> ListenResult {
        try!(listener.push(&Event::Value(StreamValue::Bool(result))));
        self.transition_done()
    }

    fn transition_done(&mut self) -> ListenResult {
        self.reset();
        self.is_done = true;
        Ok(Signal::Done)
    }

    fn send_values(&mut self, event: &Event, listener: &mut Listener) -> ListenResult {
        try!(self.lhs.filter(event, &mut self.lhs_buffer));
        try!(self.rhs.filter(event, &mut self.rhs_buffer));

        // We only can compare numbers, which means a valid buffer will only
        // ever have a single value, and that value must be a number. After
        // the buffer has a single value, we can stop pushing to it and check.
        if self.lhs_buffer.is_empty() || self.rhs_buffer.is_empty() {
            return Ok(Signal::More);
        }

        let lval = match self.lhs_buffer.events[0].as_number() {
            Some(n) => n,
            None => return self.send_null(listener)
        };
        let rval = match self.rhs_buffer.events[0].as_number() {
            Some(n) => n,
            None => return self.send_null(listener)
        };

        match self.comparator {
            OrdComparator::LessThan => self.send_bool(lval < rval, listener),
            OrdComparator::LessThanEqual => self.send_bool(lval <= rval, listener),
            OrdComparator::GreaterThan => self.send_bool(lval > rval, listener),
            OrdComparator::GreaterThanEqual => self.send_bool(lval >= rval, listener),
        }
    }
}

impl Filter for OrderingFilter {
    fn filter(&mut self, event: &Event, listener: &mut Listener) -> ListenResult {
        if self.is_done {
            Ok(Signal::Done)
        } else {
            self.send_values(event, listener)
        }
    }

    fn reset(&mut self) {
        self.is_done = false;
        self.lhs.reset();
        self.rhs.reset();
        self.lhs_buffer.reset();
        self.rhs_buffer.reset();
    }
}

#[cfg(test)]
mod tests {
    use tests::run_test_cases;

    #[test]
    fn compares_equality_values() {
        run_test_cases(vec![
            // Boolean
            ("a == b", "{\"a\":true,\"b\":true}", "true"),
            ("a == b", "{\"a\":true,\"b\":false}", "false"),
            ("a == b", "{\"a\":true,\"b\":\"a\"}", "false"),
            // Number
            ("a == a", "{\"a\":0,\"b\":1}", "true"),
            ("a == b", "{\"a\":1,\"b\":1}", "true"),
            ("a == b", "{\"a\":1,\"b\":2}", "false"),
            ("a == b", "{\"a\":1,\"b\":false}", "false"),
            // String
            ("a == b", "{\"a\":\"1\",\"b\":\"1\"}", "true"),
            ("a == b", "{\"a\":\"1\",\"b\":\"2\"}", "false"),
            ("a == b", "{\"a\":\"1\",\"b\":false}", "false"),
            // Null
            ("a == b", "{\"a\":null,\"b\":null}", "true"),
            ("a == b", "{\"a\":null,\"b\":\"2\"}", "false"),
            // Array
            ("a == b", "{\"a\":[],\"b\":[]}", "true"),
            ("a == b", "{\"a\":[1],\"b\":[1]}", "true"),
            ("a == b", "{\"a\":[1,2],\"b\":[1,2]}", "true"),
            ("a == b", "{\"a\":[1,[2]],\"b\":[1,[2]]}", "true"),
            ("a == b", "{\"a\":[1,2],\"b\":[1,3]}", "false"),
            // Object
            ("a == b", "{\"a\":{},\"b\":{}}", "true"),
            ("a == b", "{\"a\":{\"v\":true},\"b\":{\"v\":true}}", "true"),
            ("a == b", "{\"a\":{\"v\":true,\"d\":true},\"b\":{\"v\":true, \"d\":true}}", "true"),
            ("a == b", "{\"a\":{\"v\":[true]},\"b\":{\"v\":[true,false]}}", "false"),
            ("a == b", "{\"a\":{\"v\":[true]},\"b\":{\"v\":[false]}}", "false"),
        ]);
    }

    #[test]
    fn compares_ordered_values() {
        run_test_cases(vec![
            ("a > b", "{\"a\":0,\"b\":1}", "false"),
            ("a > b", "{\"a\":2,\"b\":1}", "true"),
            ("a < b", "{\"a\":0,\"b\":1}", "true"),
            ("a > b", "{\"a\":\"0\",\"b\":\"1\"}", "null"),
            ("a >= b", "{\"a\":{},\"b\":{}}", "null"),
            ("a < b", "{\"a\":[],\"b\":{}}", "null"),
            ("a < b", "{\"a\":true,\"b\":false}", "null"),
        ]);
    }
}
