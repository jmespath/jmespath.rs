# jmespath-macros

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
