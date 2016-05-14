///! Condition filter.

use std::collections::VecDeque;

use listeners::BufferedListener;
use prelude::*;
use send_null;

enum ConditionState {
    TryPredicate,
    Affirmative,
    Negative,
}

pub struct ConditionFilter {
    predicate: Box<Filter>,
    then: Box<Filter>,
    state: ConditionState,
    in_queue: VecDeque<Event>,
    out_queue: BufferedListener,
}

impl ConditionFilter {
    pub fn new(predicate: Box<Filter>, then: Box<Filter>) -> ConditionFilter {
        ConditionFilter {
            predicate: predicate,
            then: then,
            state: ConditionState::TryPredicate,
            in_queue: VecDeque::new(),
            out_queue: BufferedListener::new(),
        }
    }

    /// Sends events to the predicate filter until a determination can
    /// be made as to whether or not to transition to then.
    fn try_predicate_state(&mut self, event: &Event, listener: &mut Listener) -> ListenResult {
        self.in_queue.push_back(event.clone());
        let filter_result = try!(self.predicate.filter(event, &mut self.out_queue));
        if self.out_queue.is_truthy() {
            // Stop sending to the predicate once it yields truthy.
            self.state = ConditionState::Affirmative;
            self.out_queue.reset();
            // Send each buffered event to the then filter and listener.
            while let Some(e) = self.in_queue.pop_front() {
                if let Signal::Done = try!(self.then.filter(&e, listener)) {
                    self.in_queue.clear();
                    return Ok(Signal::Done);
                }
            }
            Ok(Signal::More)
        } else if filter_result == Signal::Done {
            // If the output_queue is still not true and the predicate
            // is Done, then transition to a negative state.
            self.state = ConditionState::Negative;
            self.in_queue.clear();
            self.out_queue.reset();
            send_null(listener)
        } else {
            Ok(filter_result)
        }
    }
}

impl Filter for ConditionFilter {
    fn filter(&mut self, event: &Event, listener: &mut Listener) -> ListenResult {
        match self.state {
            ConditionState::TryPredicate => self.try_predicate_state(event, listener),
            ConditionState::Affirmative => self.then.filter(event, listener),
            ConditionState::Negative => Ok(Signal::Done)
        }
    }

    fn reset(&mut self) {
        self.state = ConditionState::TryPredicate;
        self.predicate.reset();
        self.then.reset();
        self.in_queue.clear();
        self.out_queue.reset();
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::rc::Rc;
    use jmespath::Variable;

    use listeners::StringListener;
    use filters::IndexFilter;
    use Emitter;

    #[test]
    fn pushes_queue_to_then_when_predicate_is_true() {
        let value = Rc::new(Variable::from_json("[\"a\",\"b\"]").unwrap());
        let mut listener = StringListener::new();
        let mut filter = ConditionFilter::new(
            Box::new(IndexFilter::new(0)),
            Box::new(IndexFilter::new(1)),
        );
        value.emit_filter(&mut filter, &mut listener).ok();
        assert_eq!("\"b\"", listener.as_str());
    }

    #[test]
    fn pushes_null_when_predicate_is_falsey() {
        let value = Rc::new(Variable::from_json("[\"a\",\"b\"]").unwrap());
        let mut listener = StringListener::new();
        let mut filter = ConditionFilter::new(
            Box::new(IndexFilter::new(10)),
            Box::new(IndexFilter::new(1)),
        );
        value.emit_filter(&mut filter, &mut listener).ok();
        assert_eq!("null", listener.as_str());
    }
}
