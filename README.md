# JMESPath for Rust

[![GitHub Actions](https://github.com/jmespath/jmespath.rs/workflows/CI/badge.svg)](https://github.com/jmespath/jmespath.rs/actions?query=workflow%3ACI)
[![Coverage Status](https://coveralls.io/repos/github/mtdowling/jmespath.rs/badge.svg?branch=master)](https://coveralls.io/github/mtdowling/jmespath.rs?branch=master)
[![Current Version](http://meritbadge.herokuapp.com/jmespath)](https://crates.io/crates/jmespath)
[![Gitter](https://badges.gitter.im/Join%20Chat.svg)](https://gitter.im/jmespath/chat)

Rust implementation of [JMESPath](http://jmespath.org), a query language for JSON.

[Documentation](https://docs.rs/jmespath/)

## Installing

This crate is [on crates.io](https://crates.io/crates/jmespath) and can be used
by adding `jmespath` to the dependencies in your project's `Cargo.toml`.

```toml
[dependencies]
jmespath = "^0.2.0"
```

If you are using a nightly compiler, or reading this when specialization in Rust
is stable (see [rust#31844](https://github.com/rust-lang/rust/issues/31844)), then
enable the `specialized` feature to switch on usage of specialization to get more
efficient code:

```toml
[dependencies.jmespath]
version = "^0.2.0"
features = ["specialized"]
```

## Examples

```rust
extern crate jmespath;

let expr = jmespath::compile("foo.bar").unwrap();

// Parse some JSON data into a JMESPath variable
let json_str = r#"{"foo": {"bar": true}}"#;
let data = jmespath::Variable::from_json(json_str).unwrap();

// Search the data with the compiled expression
let result = expr.search(data).unwrap();
assert_eq!(true, result.as_boolean().unwrap());
```

## jmespath! compiler plugin

The `jmespath-macros` crate provides the `jmespath!` macro used to
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
    // Create our statically compiled expression. The build will fail
    // if the expression is invalid.
    let expr = jmespath!("foo.bar");

    // Parse some JSON data into a JMESPath variable
    let json_str = r#"{"foo": {"bar": true}}"#;
    let data = jmespath::Variable::from_json(json_str).unwrap();
    let result = expr.search(data).unwrap();
    assert_eq!(true, result.as_boolean().unwrap());
}
```
