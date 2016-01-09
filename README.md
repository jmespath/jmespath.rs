# JMESPath.rs

Rust implementation of [JMESPath](http://jmespath.org), a query language for JSON.

[![Build Status](https://travis-ci.org/mtdowling/jmespath.rs.svg?branch=master)](https://travis-ci.org/mtdowling/jmespath.rs)

[Documentation](http://mtdowling.com/jmespath.rs/jmespath/)

This crate is [on crates.io](https://crates.io/crates/jmespath) and can be used
by adding `jmespath` to the dependencies in your project's `Cargo.toml`.

```toml
[dependencies]
jmespath = "0.0.1"
```

```rust
extern crate jmespath;

let expr = jmespath::Expression::new("foo.bar | baz").unwrap();

// Parse some JSON data into a JMESPath variable
let json_str = "{\"foo\":{\"bar\":{\"baz\":true}}}";
let data = jmespath::Variable::from_str(json_str).unwrap();

// Search the data with the compiled expression
let result = expr.search(data).unwrap();
assert_eq!(true, result.as_boolean().unwrap());
```
