use Listener;
use ListenResult;
use Filter;
use Event;
use Signal;
use StreamValue;
use StreamError;

enum NotState {
    Start,
    Done,
    ExpectingEndObject,
    ExpectingEndArray,
}

/// Filter that pushes true/false based on negation of a filter.
pub struct NotFilter {
    state: NotState,
}

impl NotFilter {
    pub fn new() -> NotFilter {
        NotFilter {
            state: NotState::Start,
        }
    }

    pub fn send_result(&mut self, result: bool, listener: &mut Listener) -> ListenResult {
        self.state = NotState::Done;
        try!(listener.push(&Event::Value(StreamValue::Bool(result))));
        Ok(Signal::Done)
    }
}

impl Filter for NotFilter {
    fn filter(&mut self, event: &Event, listener: &mut Listener) -> ListenResult {
        match self.state {
            NotState::Start => {
                match *event {
                    Event::StartArray => {
                        self.state = NotState::ExpectingEndArray;
                        Ok(Signal::More)
                    },
                    Event::StartObject => {
                        self.state = NotState::ExpectingEndObject;
                        Ok(Signal::More)
                    },
                    Event::Value(ref v) => {
                        let result = match *v {
                            StreamValue::I64(_) => false,
                            StreamValue::U64(_) => false,
                            StreamValue::F64(_) => false,
                            StreamValue::Bool(true) => false,
                            StreamValue::String(ref s) if s.len() > 0 => false,
                            _ => true
                        };
                        self.send_result(result, listener)
                    },
                    _ => {
                        Err(StreamError::JsonError(
                            format!("Expected value, {{, or [. Found {:?}", event)))
                    }
                }
            },
            NotState::ExpectingEndObject => {
                self.send_result(Event::EndObject == *event, listener)
            },
            NotState::ExpectingEndArray => {
                self.send_result(Event::EndArray == *event, listener)
            },
            NotState::Done => Ok(Signal::Done),
        }
    }

    fn reset(&mut self) {
        self.state = NotState::Start;
    }
}

#[cfg(test)]
mod tests {
    use tests::run_test_cases;

    #[test]
    fn not_filter() {
        run_test_cases(vec![
            ("!@", "1", "false"),
            ("!@", "0", "false"),
            ("!@", "false", "true"),
            ("!@", "true", "false"),
            ("!@", "[]", "true"),
            ("!@", "[1]", "false"),
            ("!@", "[1,2,3]", "false"),
            ("!@", "{}", "true"),
            ("!@", "{\"a\":true}", "false"),
        ]);
    }
}
