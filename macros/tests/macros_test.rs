#![feature(plugin)]

#![plugin(jmespath_macros)]
extern crate jmespath;

#[test]
fn expands_field_subexpr_macro() {
    assert_eq!(jmespath!("foo.bar"), jmespath::Expression::new("foo.bar").unwrap());
}

#[test]
fn expands_or() {
    assert_eq!(jmespath!("a || b"), jmespath::Expression::new("a || b").unwrap());
}

#[test]
fn expands_and() {
    assert_eq!(jmespath!("a && b"), jmespath::Expression::new("a && b").unwrap());
}

#[test]
fn expands_index() {
    assert_eq!(jmespath!("a[0]"), jmespath::Expression::new("a[0]").unwrap());
}

#[test]
fn expands_not() {
    assert_eq!(jmespath!("!a"), jmespath::Expression::new("!a").unwrap());
}

#[test]
fn expands_expref() {
    assert_eq!(jmespath!("&a"), jmespath::Expression::new("&a").unwrap());
}

#[test]
fn expands_value_projection() {
    assert_eq!(jmespath!("a.*.b"), jmespath::Expression::new("a.*.b").unwrap());
}

#[test]
fn expands_array_projection() {
    assert_eq!(jmespath!("a[*].b"), jmespath::Expression::new("a[*].b").unwrap());
}

#[test]
fn expands_flatten_projection() {
    assert_eq!(jmespath!("a[].b"), jmespath::Expression::new("a[].b").unwrap());
}

#[test]
fn expands_slices() {
    assert_eq!(jmespath!("[1::]"), jmespath::Expression::new("[1::]").unwrap());
    assert_eq!(jmespath!("[10:1:-1]"), jmespath::Expression::new("[10:1:-1]").unwrap());
}

#[test]
fn expands_multi_list() {
    assert_eq!(jmespath!("[a, b, c]"), jmespath::Expression::new("[a, b, c]").unwrap());
}

#[test]
fn expands_functions() {
    assert_eq!(jmespath!("foo(a, b, c)"), jmespath::Expression::new("foo(a, b, c)").unwrap());
}

#[test]
fn expands_comparisons() {
    assert_eq!(jmespath!("a > b"), jmespath::Expression::new("a > b").unwrap());
    assert_eq!(jmespath!("a >= b"), jmespath::Expression::new("a >= b").unwrap());
    assert_eq!(jmespath!("a < b"), jmespath::Expression::new("a < b").unwrap());
    assert_eq!(jmespath!("a <= b"), jmespath::Expression::new("a <= b").unwrap());
    assert_eq!(jmespath!("a == b"), jmespath::Expression::new("a == b").unwrap());
    assert_eq!(jmespath!("a != b"), jmespath::Expression::new("a != b").unwrap());
}

#[test]
fn expands_multi_hash() {
    assert_eq!(jmespath!("a.{b: c}"), jmespath::Expression::new("a.{b: c}").unwrap());
    assert_eq!(jmespath!("{b: c}"), jmespath::Expression::new("{b: c}").unwrap());
    assert_eq!(jmespath!("a.{b: foo.bar, c: d}"),
            jmespath::Expression::new("a.{b: foo.bar, c: d}").unwrap());
}

#[test]
fn expands_literal() {
    assert_eq!(jmespath!("`\"foo\"`"), jmespath::Expression::new("`\"foo\"`").unwrap());
    assert_eq!(jmespath!("`1`"), jmespath::Expression::new("`1`").unwrap());
    assert_eq!(jmespath!("`1.5`"), jmespath::Expression::new("`1.5`").unwrap());
    assert_eq!(jmespath!("`-1.5`"), jmespath::Expression::new("`-1.5`").unwrap());
    assert_eq!(jmespath!("`-1`"), jmespath::Expression::new("`-1`").unwrap());
    assert_eq!(jmespath!("`true`"), jmespath::Expression::new("`true`").unwrap());
    assert_eq!(jmespath!("`false`"), jmespath::Expression::new("`false`").unwrap());
    assert_eq!(jmespath!("`null`"), jmespath::Expression::new("`null`").unwrap());
    assert_eq!(jmespath!("`[1, 2, 3]`"), jmespath::Expression::new("`[1, 2, 3]`").unwrap());
    assert_eq!(jmespath!("`{\"a\":1, \"b\":\"c\"}`"),
            jmespath::Expression::new("`{\"a\":1, \"b\":\"c\"}`").unwrap());
}

#[test]
fn basic_usage() {
    use std::collections::BTreeMap;

    // Create our statically compiled expression. The build will fail
    // if the expression is invalid.
    let expr = jmespath!("foo.bar");

    // Build up and search over a BTreeMap directly.
    let mut outer = BTreeMap::new();
    let mut inner = BTreeMap::new();
    inner.insert("bar", true);
    outer.insert("foo", inner);

    // Perform the search.
    let result = expr.search(&outer).unwrap();

    // Convert to an actual bool and compare with what's expected.
    assert_eq!(true, result.as_boolean().unwrap());
}
