use std::collections::VecDeque;

use listener::BufferedListener;
use Emitter;
use Listener;
use ListenResult;
use Filter;
use Event;
use Signal;
use SendValueFilter;
use SkipValueFilter;
use StreamValue;
use send_null;

/* ------------------------------------------
 * Positive indexing
 * ------------------------------------------ */

#[derive(Debug)]
enum IndexState {
    ExpectArray,
    ExpectValue,
    SendValue,
    SkipValue,
    Done,
}

pub struct IndexFilter {
    index: usize,
    current_index: usize,
    state: IndexState,
    skip_value_filter: SkipValueFilter,
    send_value_filter: SendValueFilter,
}

impl IndexFilter {
    pub fn new(index: usize) -> IndexFilter {
        IndexFilter {
            index: index,
            current_index: 0,
            state: IndexState::ExpectArray,
            skip_value_filter: SkipValueFilter::new(),
            send_value_filter: SendValueFilter::new(true),
        }
    }

    fn send_null(&mut self, listener: &mut Listener) -> ListenResult {
        self.state = IndexState::Done;
        send_null(listener)
    }
}

impl Filter for IndexFilter {
    fn filter(&mut self, event: &Event, listener: &mut Listener) -> ListenResult {
        match self.state {
            IndexState::ExpectArray => {
                match *event {
                    Event::StartArray => {
                        self.state = IndexState::ExpectValue;
                        Ok(Signal::More)
                    },
                    _ => self.send_null(listener)
                }
            },
            IndexState::ExpectValue => {
                if let &Event::EndArray = event {
                    self.send_null(listener)
                } else if self.current_index == self.index {
                    self.state = IndexState::SendValue;
                    self.filter(event, listener)
                } else {
                    self.current_index += 1;
                    self.state = IndexState::SkipValue;
                    self.filter(event, listener)
                }
            },
            IndexState::SendValue => {
                self.send_value_filter.filter(event, listener).map(|signal| {
                    if let Signal::Done = signal {
                        self.state = IndexState::Done;
                    }
                    signal
                })
            },
            IndexState::SkipValue => {
                self.skip_value_filter.filter(event, listener).map(|signal| {
                    if let Signal::Done = signal {
                        self.state = IndexState::ExpectValue;
                    }
                    signal
                })
            },
            IndexState::Done => Ok(Signal::Done),
        }
    }

    fn reset(&mut self) {
        self.state = IndexState::ExpectArray;
        self.skip_value_filter.reset();
        self.send_value_filter.reset();
    }
}

/* ------------------------------------------
 * Negative indexing
 * ------------------------------------------ */

/// SlidingBuffer keeps N number of buffers available to account for negative
/// indexing on an array of an unknown size.
struct SlidingBuffer {
    size: usize,
    buffers: VecDeque<BufferedListener>,
}

impl SlidingBuffer {
    pub fn new(size: usize) -> SlidingBuffer {
        SlidingBuffer {
            buffers: VecDeque::new(),
            size: size,
        }
    }

    pub fn expect_value(&mut self) {
        if self.buffers.len() == self.size {
            self.buffers.pop_front();
        }
        self.buffers.push_back(BufferedListener::new());
    }

    pub fn reset(&mut self) {
        self.buffers.clear();
    }
}

impl Listener for SlidingBuffer {
    fn push(&mut self, event: &Event) -> ListenResult {
        self.buffers.back_mut()
            .expect("SlidingBuffer::expect_value must be called before push()")
            .push(event)
    }
}

impl Emitter for SlidingBuffer {
    fn emit(&self, listener: &mut Listener) -> ListenResult {
        if self.buffers.len() < self.size {
            listener.push(&Event::Value(StreamValue::Null))
        } else {
            self.buffers.front().unwrap().emit(listener)
        }
    }
}

#[derive(Debug)]
enum NegativeIndexState {
    ExpectArray,
    ExpectValue,
    SendValue,
    Done,
}

pub struct NegativeIndexFilter {
    state: NegativeIndexState,
    buffer: SlidingBuffer,
    send_value_filter: SendValueFilter,
}

impl NegativeIndexFilter {
    pub fn new(index: usize) -> NegativeIndexFilter {
        NegativeIndexFilter {
            buffer: SlidingBuffer::new(index),
            state: NegativeIndexState::ExpectArray,
            send_value_filter: SendValueFilter::new(true),
        }
    }

    fn send_buffer(&mut self, listener: &mut Listener) -> ListenResult {
        self.state = NegativeIndexState::Done;
        try!(self.buffer.emit(listener));
        self.buffer.reset();
        Ok(Signal::Done)
    }
}

impl Filter for NegativeIndexFilter {
    fn filter(&mut self, event: &Event, listener: &mut Listener) -> ListenResult {
        match self.state {
            NegativeIndexState::ExpectArray => {
                match *event {
                    Event::StartArray => {
                        self.state = NegativeIndexState::ExpectValue;
                        Ok(Signal::More)
                    },
                    _ => {
                        self.state = NegativeIndexState::Done;
                        send_null(listener)
                    }
                }
            },
            NegativeIndexState::ExpectValue => {
                if let &Event::EndArray = event {
                    self.send_buffer(listener)
                } else {
                    self.state = NegativeIndexState::SendValue;
                    self.buffer.expect_value();
                    self.filter(event, listener)
                }
            },
            NegativeIndexState::SendValue => {
                let result = try!(self.send_value_filter.filter(event, &mut self.buffer));
                if let Signal::Done = result {
                    self.state = NegativeIndexState::ExpectValue;
                }
                Ok(Signal::More)
            },
            NegativeIndexState::Done => Ok(Signal::Done),
        }
    }

    fn reset(&mut self) {
        self.state = NegativeIndexState::ExpectArray;
        self.send_value_filter.reset();
        self.buffer.reset();
    }
}

#[cfg(test)]
mod tests {
    use tests::run_test_cases;

    #[test]
    fn filters_positive_index() {
        run_test_cases(vec![
            ("[0]", "[0, 1, 2]", "0"),
            ("[0]", "[]", "null"),
            ("[1]", "[0, 1, 2]", "1"),
            ("[2]", "[0, 1, 2]", "2"),
            ("[3]", "[0, 1, 2]", "null"),
            ("[0]", "1", "null"),
        ]);
    }

    #[test]
    fn filters_negative_index() {
        run_test_cases(vec![
            ("[-1]", "[]", "null"),
            ("[-1]", "1", "null"),
            ("[-2]", "[0]", "null"),
            ("[-1]", "[0]", "0"),
            ("[-1]", "[0, 1]", "1"),
            ("[-1]", "[0, 1, 2]", "2"),
            ("[-2]", "[0, 1, 2]", "1"),
            ("[-3]", "[0, 1, 2]", "0"),
            ("[-2]", "[0, 1, 2, 3, 4, 5, 6]", "5"),
            ("[-3]", "[0, 1, 2, 3, 4, 5, 6]", "4"),
        ]);
    }
}
