use Listener;
use ListenResult;
use Filter;
use Event;
use Signal;
use SkipValueFilter;
use SendValueFilter;
use send_null;

#[derive(Debug)]
enum FieldState {
    ExpectObject,
    ExpectField,
    SendValue,
    SkipValue,
    Done,
}

pub struct FieldFilter {
    name: String,
    state: FieldState,
    skip_value_filter: SkipValueFilter,
    send_value_filter: SendValueFilter,
}

impl FieldFilter {
    #[inline]
    pub fn new(name: &str) -> FieldFilter {
        FieldFilter {
            name: name.to_owned(),
            state: FieldState::ExpectObject,
            skip_value_filter: SkipValueFilter::new(),
            send_value_filter: SendValueFilter::new(true),
        }
    }
}

impl Filter for FieldFilter {
    #[inline]
    fn filter(&mut self, event: &Event, listener: &mut Listener) -> ListenResult {
        match self.state {
            FieldState::ExpectObject => {
                match *event {
                    Event::StartObject => {
                        self.state = FieldState::ExpectField;
                        Ok(Signal::More)
                    },
                    _ => {
                        self.state = FieldState::Done;
                        send_null(listener)
                    }
                }
            },
            FieldState::ExpectField => {
                match *event {
                    Event::FieldName(ref s) => {
                        self.state = if **s == self.name {
                            FieldState::SendValue
                        } else {
                            FieldState::SkipValue
                        };
                        Ok(Signal::More)
                    },
                    _ => {
                        self.state = FieldState::Done;
                        send_null(listener)
                    }
                }
            },
            FieldState::SendValue => {
                self.send_value_filter.filter(event, listener).map(|signal| {
                    if let Signal::Done = signal {
                        self.state = FieldState::Done;
                    }
                    signal
                })
            },
            FieldState::SkipValue => {
                match try!(self.skip_value_filter.filter(event, listener)) {
                    Signal::Done => {
                        self.state = FieldState::ExpectField;
                        Ok(Signal::More)
                    },
                    signal => Ok(signal)
                }
            },
            FieldState::Done => Ok(Signal::Done),
        }
    }

    fn reset(&mut self) {
        self.state = FieldState::ExpectObject;
        self.skip_value_filter.reset();
        self.send_value_filter.reset();
    }
}

#[cfg(test)]
mod tests {
    use tests::run_test_cases;

    #[test]
    fn applies_multi_list_filter() {
        let data = "{\"foo\":{\"baz\":null},\"baz\":{\"hi\":\"Good!\"}}";
        run_test_cases(vec![
            ("foo", data, "{\"baz\":null}"),
            ("foo.baz", data, "null"),
            ("baz.hi", data, "\"Good!\""),
            ("foo.not_there", data, "null"),
            ("baz", data, "{\"hi\":\"Good!\"}"),
            ("baz.not_object", data, "null"),
            ("foo", "[1, 2, 3]", "null"),
            ("not_there", data, "null"),
        ]);
    }
}
