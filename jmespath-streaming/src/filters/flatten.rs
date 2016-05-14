//! Array flatten filter.

use prelude::*;
use filters::{ArrayFilterPredicate, ArrayFilterPredicateResult, ArrayValueFilter, PipedFilter};

/// Creates a new flatten filter.
pub fn new_flatten(inner: Box<Filter>) -> Box<Filter> {
    Box::new(PipedFilter::new(
        inner,
        Box::new(ArrayValueFilter::new(Box::new(FlattenFilterPredicate::new())))
    ))
}

#[derive(Debug)]
enum FlattenPredicateState {
    CheckValue,
    FilterValue,
    SendValue,
}

/// Predicate used to flatten each array value.
///
/// Receives each array element and omits the opening and closing array
/// tokens of each value, essentially flattening the array. Note that
/// this filter does not need to track the validity of opening and
/// closing tokens. That is handled in the ArrayValueFilter. All that
/// this filter needs to do is ensure the opening and closing array
/// events are not forwarded to the listener.
struct FlattenFilterPredicate {
    state: FlattenPredicateState,
    pending_arrays: usize,
}

impl FlattenFilterPredicate {
    pub fn new() -> FlattenFilterPredicate {
        FlattenFilterPredicate {
            state: FlattenPredicateState::CheckValue,
            pending_arrays: 0,
        }
    }
}

impl ArrayFilterPredicate for FlattenFilterPredicate {
    fn accept(&mut self) -> ArrayFilterPredicateResult {
        self.reset();
        Ok(true)
    }
}

impl Filter for FlattenFilterPredicate {
    fn filter(&mut self, event: &Event, listener: &mut Listener) -> ListenResult {
        match self.state {
            FlattenPredicateState::SendValue => listener.push(event),
            FlattenPredicateState::CheckValue => {
                if *event == Event::StartArray {
                    // Skip a start array and begin sending the contents of the array.
                    self.state = FlattenPredicateState::FilterValue;
                    self.pending_arrays += 1;
                    Ok(Signal::More)
                } else {
                    // Pipe the event and any inner events.
                    self.state = FlattenPredicateState::SendValue;
                    self.filter(event, listener)
                }
            },
            FlattenPredicateState::FilterValue => {
                // When sending values through the predicate, we need to track
                // open and closing tokens to ensure that the last closing
                // array token is not sent to the listener.
                match *event {
                    Event::StartArray => {
                        self.pending_arrays += 1;
                        listener.push(event)
                    },
                    Event::EndArray => {
                        self.pending_arrays -= 1;
                        if self.pending_arrays == 0 {
                            // Skip the closing array and we are done.
                            Ok(Signal::Done)
                        } else {
                            listener.push(event)
                        }
                    },
                    // All other events are forwarded to the listener.
                    _ => listener.push(event)
                }
            }
        }
    }

    fn reset(&mut self) {
        self.state = FlattenPredicateState::CheckValue;
        self.pending_arrays = 0;
    }
}

#[cfg(test)]
mod tests {
    use tests::run_test_cases;

    #[test]
    fn applies_multi_list_filter() {
        let data = "[0,[1],2,[3, 4],[[5]]]";
        run_test_cases(vec![
            ("[]", data, "[0,1,2,3,4,[5]]"),
            ("[1][]", data, "[1]"),
            ("[4][]", data, "[5]"),
            ("[]", "true", "null"),
        ]);
    }
}
