use Listener;
use ListenResult;
use Filter;
use Event;
use SendValueFilter;
use Signal;
use StreamError;
use send_null;

enum ObjectValuesState {
    StartObject,
    Field,
    SendValue,
    Done,
}

pub struct ObjectValuesFilter {
    state: ObjectValuesState,
    send_value_filter: SendValueFilter,
}

impl ObjectValuesFilter {
    pub fn new() -> ObjectValuesFilter {
        ObjectValuesFilter {
            state: ObjectValuesState::StartObject,
            send_value_filter: SendValueFilter::new(false),
        }
    }
}

impl Filter for ObjectValuesFilter {
    fn filter(&mut self, event: &Event, listener: &mut Listener) -> ListenResult {
        match self.state {
            ObjectValuesState::StartObject => {
                match *event {
                    Event::StartObject => {
                        match try!(listener.push(&Event::StartArray)) {
                            Signal::Done => {
                                self.state = ObjectValuesState::Done;
                                Ok(Signal::Done)
                            },
                            Signal::More => {
                                self.state = ObjectValuesState::Field;
                                Ok(Signal::More)
                            }
                        }
                    },
                    _ => {
                        self.state = ObjectValuesState::Done;
                        send_null(listener)
                    }
                }
            },
            ObjectValuesState::Field => {
                match *event {
                    Event::FieldName(_) => {
                        self.state = ObjectValuesState::SendValue;
                        Ok(Signal::More)
                    },
                    Event::EndObject => {
                        self.state = ObjectValuesState::Done;
                        try!(listener.push(&Event::EndArray));
                        Ok(Signal::Done)
                    },
                    _ => Err(StreamError::JsonError(format!("Unexpected event: {:?}", event))),
                }
            },
            ObjectValuesState::SendValue => {
                match self.send_value_filter.filter(event, listener) {
                    Ok(Signal::Done) => {
                        self.state = ObjectValuesState::Field;
                        self.send_value_filter.reset();
                        Ok(Signal::More)
                    },
                    r => r
                }
            },
            ObjectValuesState::Done => Ok(Signal::Done)
        }
    }

    fn reset(&mut self) {
        self.send_value_filter.reset();
        self.state = ObjectValuesState::StartObject;
    }
}

#[cfg(test)]
mod tests {
    use std::rc::Rc;
    use super::*;
    use jmespath::Variable;
    use Emitter;
    use listener::StringListener;

    #[test]
    fn send_object_values_through_filter() {
        let mut filter = ObjectValuesFilter::new();
        let mut listener = StringListener::new();
        let value = Variable::from_json("{\"foo\":[1,2],\"bar\":3,\"baz\":4}").unwrap();
        value.emit_filter(&mut filter, &mut listener).ok();
        let parsed = Variable::from_json(listener.as_str()).unwrap();
        let arr = parsed.as_array().unwrap();
        assert!(arr.contains(&Rc::new(Variable::from_json("[1,2]").unwrap())));
        assert!(arr.contains(&Rc::new(Variable::U64(3))));
        assert!(arr.contains(&Rc::new(Variable::U64(4))));
    }

    #[test]
    fn sends_null_for_non_objects() {
        let mut filter = ObjectValuesFilter::new();
        let mut listener = StringListener::new();
        let value = Variable::from_json("[1,2]").unwrap();
        value.emit_filter(&mut filter, &mut listener).ok();
        assert_eq!("null", listener.as_str());
    }
}
