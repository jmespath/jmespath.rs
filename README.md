# JMESPath for Rust

[![Crates.io](https://img.shields.io/crates/v/jmespath.svg)](https://crates.io/crates/jmespath)
[![Documentation](https://docs.rs/jmespath/badge.svg)](https://docs.rs/jmespath/)
[![License: MIT](https://img.shields.io/badge/License-MIT-blue.svg)](LICENSE)

Rust implementation of [JMESPath](https://jmespath.org), a query language for JSON.

## Installation

Add `jmespath` to your `Cargo.toml`:

```toml
[dependencies]
jmespath = "0.5"
```

If you are using a nightly compiler, enable the `specialized` feature for more efficient code:

```toml
[dependencies]
jmespath = { version = "0.5", features = ["specialized"] }
```

## Quick Start

```rust
use jmespath;

// Compile a JMESPath expression
let expr = jmespath::compile("foo.bar").unwrap();

// Parse JSON data
let data = jmespath::Variable::from_json(r#"{"foo": {"bar": "hello"}}"#).unwrap();

// Search the data
let result = expr.search(data).unwrap();
assert_eq!("hello", result.as_string().unwrap());
```

## Examples

### Accessing Nested Data

```rust
use jmespath;

let expr = jmespath::compile("person.address.city").unwrap();
let data = jmespath::Variable::from_json(r#"
{
  "person": {
    "name": "Alice",
    "address": {
      "city": "Seattle",
      "state": "WA"
    }
  }
}
"#).unwrap();

let result = expr.search(data).unwrap();
assert_eq!("Seattle", result.as_string().unwrap());
```

### Array Indexing and Slicing

```rust
use jmespath;

let data = jmespath::Variable::from_json(r#"{"items": ["a", "b", "c", "d", "e"]}"#).unwrap();

// Get first element
let expr = jmespath::compile("items[0]").unwrap();
assert_eq!("a", expr.search(&data).unwrap().as_string().unwrap());

// Get last element
let expr = jmespath::compile("items[-1]").unwrap();
assert_eq!("e", expr.search(&data).unwrap().as_string().unwrap());

// Slice: get elements 1-3
let expr = jmespath::compile("items[1:4]").unwrap();
let result = expr.search(&data).unwrap();
assert_eq!(3, result.as_array().unwrap().len());
```

### Projections and Filtering

```rust
use jmespath;

let data = jmespath::Variable::from_json(r#"
{
  "people": [
    {"name": "Alice", "age": 30},
    {"name": "Bob", "age": 25},
    {"name": "Charlie", "age": 35}
  ]
}
"#).unwrap();

// Project: get all names
let expr = jmespath::compile("people[*].name").unwrap();
let result = expr.search(&data).unwrap();
let names: Vec<_> = result.as_array().unwrap()
    .iter()
    .map(|v| v.as_string().unwrap())
    .collect();
assert_eq!(vec!["Alice", "Bob", "Charlie"], names);

// Filter: people over 28
let expr = jmespath::compile("people[?age > \`28\`].name").unwrap();
let result = expr.search(&data).unwrap();
let names: Vec<_> = result.as_array().unwrap()
    .iter()
    .map(|v| v.as_string().unwrap())
    .collect();
assert_eq!(vec!["Alice", "Charlie"], names);
```

### Built-in Functions

```rust
use jmespath;

let data = jmespath::Variable::from_json(r#"{"numbers": [1, 2, 3, 4, 5]}"#).unwrap();

// length()
let expr = jmespath::compile("length(numbers)").unwrap();
assert_eq!(5.0, expr.search(&data).unwrap().as_number().unwrap());

// sum()
let expr = jmespath::compile("sum(numbers)").unwrap();
assert_eq!(15.0, expr.search(&data).unwrap().as_number().unwrap());

// max() and min()
let expr = jmespath::compile("max(numbers)").unwrap();
assert_eq!(5.0, expr.search(&data).unwrap().as_number().unwrap());
```

### Multi-select and Object Creation

```rust
use jmespath;

let data = jmespath::Variable::from_json(r#"
{
  "person": {"first": "Alice", "last": "Smith"},
  "address": {"city": "Seattle"}
}
"#).unwrap();

// Multi-select list
let expr = jmespath::compile("[person.first, address.city]").unwrap();
let result = expr.search(&data).unwrap();
assert_eq!(2, result.as_array().unwrap().len());

// Multi-select hash (create new object)
let expr = jmespath::compile("{name: person.first, location: address.city}").unwrap();
let result = expr.search(&data).unwrap();
assert_eq!("Alice", result.get_field("name").as_string().unwrap());
assert_eq!("Seattle", result.get_field("location").as_string().unwrap());
```

## Command Line Tool

A command line tool `jp` is available in the `jmespath-cli` crate:

```bash
cargo install jmespath-cli
echo '{"foo": {"bar": "baz"}}' | jp foo.bar
# "baz"
```

## Learn More

- [JMESPath Specification](https://jmespath.org/specification.html)
- [JMESPath Tutorial](https://jmespath.org/tutorial.html)
- [API Documentation](https://docs.rs/jmespath/)

## License

This project is licensed under the MIT License - see the [LICENSE](LICENSE) file for details.
