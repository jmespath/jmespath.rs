# JMESPath for Rust

[![Build Status](https://travis-ci.org/mtdowling/jmespath.rs.svg?branch=master)](https://travis-ci.org/mtdowling/jmespath.rs)
[![Coverage Status](https://coveralls.io/repos/github/mtdowling/jmespath.rs/badge.svg?branch=master)](https://coveralls.io/github/mtdowling/jmespath.rs?branch=master)
[![Current Version](http://meritbadge.herokuapp.com/jmespath)](https://crates.io/crates/jmespath)
[![Gitter](https://badges.gitter.im/Join Chat.svg)](https://gitter.im/jmespath/chat)

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
