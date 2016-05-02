use Filter;
use Event;
use NotExpectFilter;
use PipedFilter;
use StreamValue;
use ArrayValueFilter;
use DefaultArrayFilterPredicate;

/// Creates a new projection filter.
pub fn new_projection(lhs: Box<Filter>, rhs: Box<Filter>) -> Box<Filter> {
    Box::new(PipedFilter::new(
        lhs,
        Box::new(ArrayValueFilter::new(
            Box::new(DefaultArrayFilterPredicate::new(
                Box::new(PipedFilter::new(
                    rhs,
                    Box::new(NotExpectFilter::new(Event::Value(StreamValue::Null))),
                ))
            ))
        ))
    ))
}

#[cfg(test)]
mod tests {
    use tests::run_test_cases;

    #[test]
    fn projects_values() {
        run_test_cases(vec![
            ("*", "1", "null"),
            ("foo[*]", "{\"foo\":1}", "null"),
            ("*", "{\"foo\":1}", "[1]"),
            ("foo[*][0]", "{\"foo\":[[1, 2], [3], [4, 5]]}", "[1,3,4]"),
        ]);
    }
}
