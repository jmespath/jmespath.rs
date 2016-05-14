//! Multi-list value filter.

use listeners::BufferedListener;
use send_null;
use prelude::*;

enum MultiListState {
    Init,
    Collect(usize),
    Done,
}

/// Creates an array of results, filtering each element with a filter.
pub struct MultiListFilter {
    filters: Vec<Box<Filter>>,
    buffer: BufferedListener,
    state: MultiListState,
}

impl MultiListFilter {
    /// Creates a new MultiListFilter.
    pub fn new(filters: Vec<Box<Filter>>) -> MultiListFilter {
        MultiListFilter {
            filters: filters,
            buffer: BufferedListener::new(),
            state: MultiListState::Init,
        }
    }

    fn init_state(&mut self, event: &Event, listener: &mut Listener) -> ListenResult {
        // Cannot multi-list off of a null value.
        if event == &Event::Value(StreamValue::Null) {
            self.state = MultiListState::Done;
            return send_null(listener);
        }
        match try!(listener.push(&Event::StartArray)) {
            // Stop if the listener did not want an array.
            Signal::Done => {
                self.state = MultiListState::Done;
                Ok(Signal::Done)
            },
            // If there are no filters, then immediately finish.
            Signal::More if self.filters.len() == 0 => {
                self.transition_done(listener)
            },
            _ => {
                // Begin emitting events into the filters.
                self.state = MultiListState::Collect(0);
                self.filter(event, listener)
            },
        }
    }

    fn collect_results_state(&mut self, index: usize, event: &Event, listener: &mut Listener)
        -> ListenResult
    {
        self.buffer.push(event).ok();
        match try!(self.filters[index].filter(event, listener)) {
            Signal::Done => {
                // The filter completed using the buffer, so emit to the next
                // filter using the previously buffered events.
                self.emit_buffer(index + 1, listener)
            },
            Signal::More => {
                // The filter did not complete using the buffer, then we need to
                // break so that the buffer can be filled with more events.
                self.state = MultiListState::Collect(index);
                Ok(Signal::More)
            }
        }
    }

    /// Emit buffered events to each remaining filter.
    fn emit_buffer(&mut self, index: usize, listener: &mut Listener) -> ListenResult {
        for i in index..self.filters.len() {
            let result = try!(self.buffer.emit_filter(&mut self.filters[i], listener));
            if let Signal::More = result {
                self.state = MultiListState::Collect(i);
                return Ok(Signal::More)
            }
        }
        self.transition_done(listener)
    }

    fn transition_done(&mut self, listener: &mut Listener) -> ListenResult {
        self.state = MultiListState::Done;
        self.buffer.reset();
        try!(listener.push(&Event::EndArray));
        Ok(Signal::Done)
    }
}

impl Filter for MultiListFilter {
    fn filter(&mut self, event: &Event, listener: &mut Listener) -> ListenResult {
        match self.state {
            MultiListState::Init => self.init_state(event, listener),
            MultiListState::Collect(index) => self.collect_results_state(index, event, listener),
            MultiListState::Done => Ok(Signal::Done)
        }
    }

    fn reset(&mut self) {
        self.state = MultiListState::Init;
        self.buffer.reset();
        for filter in self.filters.iter_mut() {
            filter.reset();
        }
    }
}

#[cfg(test)]
mod tests {
    use tests::run_test_cases;

    #[test]
    fn applies_multi_list_filter() {
        run_test_cases(vec![
            ("[foo]", "null", "null"),
            ("[foo]", "[1,2,3,4]", "[null]"),
            ("[foo, foo.bar]", "{\"foo\":{\"bar\":true}}", "[{\"bar\":true},true]"),
            ("[foo]", "{\"foo\":{\"bar\":true}}", "[{\"bar\":true}]"),
            ("[foo]", "{\"baz\":true}", "[null]"),
            ("[foo, bar, baz]", "{\"baz\":true}", "[null,null,true]"),
            ("[foo]", "{}", "[null]"),
            ("[foo]", "true", "[null]"),
        ]);
    }
}
