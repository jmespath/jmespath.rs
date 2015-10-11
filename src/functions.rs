use std::rc::Rc;

use interpreter::InterpretResult;
use variable::Variable;

/// Handles the dispatching of named functions using an array of arguments.
pub trait FnDispatcher {
    /// Dispatches and interprets a function by name.
    fn call(&self, fn_name: &str, args: &Vec<Rc<Variable>>) -> InterpretResult;
}

/// Built-in function implementations.
#[derive(Clone)]
pub struct BuiltinFunctions;

impl BuiltinFunctions {
    /// Creates a new Builtins function dispatcher.
    pub fn new() -> BuiltinFunctions {
        BuiltinFunctions
    }
}

impl FnDispatcher for BuiltinFunctions {
    fn call(&self, fn_name: &str, args: &Vec<Rc<Variable>>) -> InterpretResult {
        match fn_name {
            "length" => {
                if args.len() > 1 {
                    Err("Too many arguments".to_string())
                } else {
                    Ok(Rc::new(match *(args[0]) {
                        Variable::Array(ref array) => Variable::U64(array.len() as u64),
                        Variable::Object(ref map) => Variable::U64(map.len() as u64),
                        Variable::String(ref s) => Variable::U64(s.len() as u64),
                        _ => Variable::Null
                    }))
                }
            },
            _ => Err(format!("Unknown function: {}", fn_name))
        }
    }
}
