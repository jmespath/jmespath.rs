//! And filter and Or filter.

use std::collections::VecDeque;

use listeners::BufferedListener;
use prelude::*;
use send_null;

enum AndOrType {
    And,
    Or,
}

enum AndOrState {
    TryLeft,
    Left,
    Right,
    Done,
}

pub struct AndOrFilter {
    lhs: Box<Filter>,
    rhs: Box<Filter>,
    state: AndOrState,
    determination: AndOrType,
    in_queue: VecDeque<Event>,
    out_queue: BufferedListener,
}

impl AndOrFilter {
    /// Create a new And filter
    #[inline]
    pub fn new_and(lhs: Box<Filter>, rhs: Box<Filter>) -> AndOrFilter {
        Self::new(lhs, rhs, AndOrType::And)
    }

    /// Create a new Or filter
    #[inline]
    pub fn new_or(lhs: Box<Filter>, rhs: Box<Filter>) -> AndOrFilter {
        Self::new(lhs, rhs, AndOrType::Or)
    }

    #[inline]
    fn new(lhs: Box<Filter>, rhs: Box<Filter>, determination: AndOrType)
            -> AndOrFilter {
        AndOrFilter {
            lhs: lhs,
            rhs: rhs,
            state: AndOrState::TryLeft,
            determination: determination,
            in_queue: VecDeque::new(),
            out_queue: BufferedListener::new(),
        }
    }

    /// Sends events to LHS until a determination can be made as to
    /// whether or not to transition.
    #[inline]
    fn try_left_state(&mut self, event: &Event, listener: &mut Listener) -> ListenResult {
        self.in_queue.push_back(event.clone());
        let filter_result = try!(self.lhs.filter(event, &mut self.out_queue));
        match self.determination {
            AndOrType::Or if self.out_queue.is_truthy() => {
                self.transition_lhs(listener, filter_result)
            },
            AndOrType::And if self.out_queue.is_truthy() => {
                self.transition_rhs(listener)
            },
            _ if filter_result == Signal::More => Ok(filter_result),
            AndOrType::And if filter_result == Signal::Done => {
                self.state = AndOrState::Done;
                send_null(listener)
            },
            _ => self.transition_rhs(listener)
        }
    }

    /// Transitions to the LHS state.
    ///
    /// Sends all buffered events emitted from LHS to the listener.
    /// Subsequent events emitted to the filter will now go directly
    /// from LHS to listener.
    #[inline]
    fn transition_lhs(&mut self, listener: &mut Listener, result: Signal) -> ListenResult {
        self.state = AndOrState::Left;
        self.in_queue.clear();
        // Send each event in the output queue to the listener.
        while let Some(e) = self.out_queue.events.pop_front() {
            if let Signal::Done = try!(listener.push(&e)) {
                return Ok(Signal::Done);
            }
        }
        Ok(result)
    }

    /// Transitions to the RHS state.
    ///
    /// Sends all buffered events that first were sent to LHS to RHS.
    /// Subsequent events emitted to the filter will now go directly
    /// from RHS to listener.
    #[inline]
    fn transition_rhs(&mut self, listener: &mut Listener) -> ListenResult {
        self.state = AndOrState::Right;
        self.out_queue.reset();
        // Send each event in the input queue to the listener.
        while let Some(e) = self.in_queue.pop_front() {
            if let Signal::Done = try!(self.rhs.filter(&e, listener)) {
                return Ok(Signal::Done);
            }
        }
        Ok(Signal::More)
    }
}

impl Filter for AndOrFilter {
    fn filter(&mut self, event: &Event, listener: &mut Listener) -> ListenResult {
        match self.state {
            AndOrState::TryLeft => self.try_left_state(event, listener),
            AndOrState::Left => self.lhs.filter(event, listener),
            AndOrState::Right => self.rhs.filter(event, listener),
            AndOrState::Done => Ok(Signal::Done),
        }
    }

    fn reset(&mut self) {
        self.state = AndOrState::TryLeft;
        self.lhs.reset();
        self.rhs.reset();
        self.in_queue.clear();
        self.out_queue.reset();
    }
}

#[cfg(test)]
mod tests {
    use tests::run_test_cases;

    #[test]
    fn applies_multi_list_filter() {
        let data = "{\"foo\":{\"baz\":null},\"baz\":{\"hi\":\"Good!\"}}";
        run_test_cases(vec![
            ("foo || baz", data, "{\"baz\":null}"),
            ("missing || foo", data, "{\"baz\":null}"),
            ("baz || foo", data, "{\"hi\":\"Good!\"}"),
            ("missing || missing", data, "null"),
            ("foo && baz", data, "{\"hi\":\"Good!\"}"),
            ("missing && foo", data, "null"),
            ("baz && foo", data, "{\"baz\":null}"),
            ("baz && missing", data, "null"),
            ("missing && missing", data, "null"),
        ]);
    }
}
