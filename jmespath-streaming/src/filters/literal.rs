//! Literal filter (simply emits events).

use prelude::*;

/// Sends a literal value to a listener, ignoring any provided event.
pub struct LiteralFilter<T: Emitter> {
    emitter: Box<T>,
}

impl<T> LiteralFilter<T> where T: Emitter {
    pub fn new(emitter: Box<T>) -> LiteralFilter<T> {
        LiteralFilter {
            emitter: emitter
        }
    }
}

impl<T> Filter for LiteralFilter<T> where T: Emitter {
    fn filter(&mut self, _event: &Event, listener: &mut Listener) -> ListenResult {
        try!(self.emitter.emit(listener));
        Ok(Signal::Done)
    }
}

#[cfg(test)]
mod tests {
    use tests::run_test_cases;

    #[test]
    fn applies_multi_list_filter() {
        run_test_cases(vec![
            ("`[1,true,null]`", "{}", "[1,true,null]"),
            ("`1`", "true", "1"),
            ("`null`", "[]", "null"),
        ]);
    }
}
