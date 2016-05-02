use std::rc::Rc;

use listener::BufferedListener;
use send_null;
use Listener;
use ListenResult;
use Filter;
use Event;
use Signal;
use StreamValue;
use Emitter;

enum MultiHashState {
    Init,
    Collect(usize),
    Done,
}

pub struct MultiHashFilter {
    filters: Vec<(Rc<String>, Box<Filter>)>,
    buffer: BufferedListener,
    state: MultiHashState,
}

impl MultiHashFilter {
    /// Creates a new MultiHashFilter.
    pub fn new(filters: Vec<(Rc<String>, Box<Filter>)>) -> MultiHashFilter {
        MultiHashFilter {
            filters: filters,
            buffer: BufferedListener::new(),
            state: MultiHashState::Init,
        }
    }

    fn init_state(&mut self, event: &Event, listener: &mut Listener) -> ListenResult {
        // Cannot multi-hash off of a null value.
        if event == &Event::Value(StreamValue::Null) {
            self.state = MultiHashState::Done;
            return send_null(listener);
        }
        match try!(listener.push(&Event::StartObject)) {
            // Stop if the listener did not want an object.
            Signal::Done => {
                self.state = MultiHashState::Done;
                Ok(Signal::Done)
            },
            // If there are no filters, then immediately finish.
            Signal::More if self.filters.len() == 0 => {
                self.transition_done(listener)
            },
            Signal::More => {
                self.state = MultiHashState::Collect(0);
                // Emit the first key and then proceed to emit the value.
                try!(listener.push(&Event::FieldName(self.filters[0].0.clone())));
                self.filter(event, listener)
            },
        }
    }

    fn collect_results_state(&mut self, index: usize, event: &Event, listener: &mut Listener)
        -> ListenResult
    {
        self.buffer.push(event).ok();
        match try!(self.filters[index].1.filter(event, listener)) {
            Signal::Done => {
                // The filter completed using the buffer, so emit to the next
                // filter using the previously buffered events.
                self.emit_buffer(index + 1, listener)
            },
            Signal::More => {
                // The filter did not complete using the buffer, then we need to
                // break so that the buffer can be filled with more events.
                self.state = MultiHashState::Collect(index);
                Ok(Signal::More)
            }
        }
    }

    /// Emit buffered events to each remaining filter.
    fn emit_buffer(&mut self, index: usize, listener: &mut Listener) -> ListenResult {
        for i in index..self.filters.len() {
            try!(listener.push(&Event::FieldName(self.filters[i].0.clone())));
            let result = try!(self.buffer.emit_filter(&mut self.filters[i].1, listener));
            // If the filter did not finish with the buffered events, then
            // stop and allow more events to later flow into the filter.
            if let Signal::More = result {
                self.state = MultiHashState::Collect(i);
                return Ok(Signal::More)
            }
        }
        self.transition_done(listener)
    }

    fn transition_done(&mut self, listener: &mut Listener) -> ListenResult {
        self.state = MultiHashState::Done;
        self.buffer.reset();
        try!(listener.push(&Event::EndObject));
        Ok(Signal::Done)
    }
}

impl Filter for MultiHashFilter {
    fn filter(&mut self, event: &Event, listener: &mut Listener) -> ListenResult {
        match self.state {
            MultiHashState::Init => self.init_state(event, listener),
            MultiHashState::Collect(index) => self.collect_results_state(index, event, listener),
            MultiHashState::Done => Ok(Signal::Done)
        }
    }

    fn reset(&mut self) {
        self.state = MultiHashState::Init;
        self.buffer.reset();
        for filter in self.filters.iter_mut() {
            filter.1.reset();
        }
    }
}

#[cfg(test)]
mod tests {
    use tests::run_test_cases;

    #[test]
    fn applies_multi_hash_filter() {
        let data = "{\"foo\":{\"bar\":true},\"baz\":[1,[2,3]]}";
        run_test_cases(vec![
            ("{foo: foo}", "null", "null"),
            ("{foo: foo}", "[1,2]", "{\"foo\":null}"),
            ("{foo: foo}", "1", "{\"foo\":null}"),
            ("{foo: foo}", data, "{\"foo\":{\"bar\":true}}"),
            ("{foo: foo.bar}", data, "{\"foo\":true}"),
            ("{foo: missing}", data, "{\"foo\":null}"),
            ("{foo: missing, baz: baz}", data, "{\"foo\":null,\"baz\":[1,[2,3]]}"),
            ("{foo: baz, baz: foo}", data, "{\"foo\":[1,[2,3]],\"baz\":{\"bar\":true}}"),
        ]);
    }
}
