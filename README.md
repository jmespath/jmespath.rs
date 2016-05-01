# JMESPath for Rust

[![Build Status](https://travis-ci.org/mtdowling/jmespath.rs.svg?branch=master)](https://travis-ci.org/mtdowling/jmespath.rs)
[![Coverage Status](https://coveralls.io/repos/github/mtdowling/jmespath.rs/badge.svg?branch=master)](https://coveralls.io/github/mtdowling/jmespath.rs?branch=master)
[![Current Version](http://meritbadge.herokuapp.com/jmespath)](https://crates.io/crates/jmespath)
[![Gitter](https://badges.gitter.im/Join Chat.svg)](https://gitter.im/jmespath/chat)

Rust implementation of [JMESPath](http://jmespath.org), a query language for JSON.

[Documentation](http://mtdowling.com/jmespath.rs/jmespath/)

## Installing

This crate is [on crates.io](https://crates.io/crates/jmespath) and can be used
by adding `jmespath` to the dependencies in your project's `Cargo.toml`.

```toml
[dependencies]
jmespath = "0.0.1"
```

## Examples

```rust
extern crate jmespath;

let expr = jmespath::Expression::new("foo.bar | baz").unwrap();

// Parse some JSON data into a JMESPath variable
let json_str = "{\"foo\":{\"bar\":{\"baz\":true}}}";
let data = jmespath::Variable::from_json(json_str).unwrap();

// Search the data with the compiled expression
let result = expr.search(data).unwrap();
assert_eq!(true, result.as_boolean().unwrap());
```

## jmespath! compiler plugin

The `jmespath_macros` crate provides the `jmespath!` macro used to
statically compile JMESPath expressions.

By statically compiling JMESPath expressions, you pay the cost of
parsing and compiling JMESPath expressions at compile time rather
than at runtime, and you can be sure that the expression is valid
if your program compiles.

**Note:** This only works with a nightly compiler.

```rust
#![feature(plugin)]

#![plugin(jmespath_macros)]
extern crate jmespath;

fn main() {
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
```
