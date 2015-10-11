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

/// Validates the arity of a function.
#[inline]
fn arity(fn_name: &str, arity: usize, args: &Vec<Rc<Variable>>) -> Result<(), String> {
    if args.len() != arity {
        Err(format!("{} arity error: expected {} args, found {}", fn_name, arity, args.len()))
    } else {
        Ok(())
    }
}

/// Macro used to format a type error.
macro_rules! type_err {
    ($f:expr, $position:expr, $expected:expr, $given:expr) => {
        format!("{} expects arg {} to be {}. Given {:?}", $f, $position, $expected, $given)
    }
}

/// Macro used to variadically validate validate Variable and argument arity.
macro_rules! validate {
    // Validate positional arguments only.
    ($name:expr, $args:expr, $($x:expr),*) => (
        {
            let validators: Vec<Box<Fn(&Rc<Variable>) -> Result<(), String>>> = vec![$($x), *];
            try!(arity($name, validators.len(), $args));
            for (k, v) in $args.iter().enumerate() {
                if let Err(e) = validators[k](v) {
                    return Err(format!("{} error at argument {}: {}", $name, k, e));
                }
            }
        }
    );
    // Validate positional arguments with a variadic validator.
    ($name:expr, $args:expr, $($x:expr),* ...$variadic:expr ) => (
        {
            let validators: Vec<Box<Fn(&Rc<Variable>) -> Result<(), String>>> = vec![$($x), *];
            if $args.len() < validators.len() {
                return Err(format!("{} arity error: expected at least {} args, found {}",
                                   $name, validators.len(), $args.len()));
            }
            for (k, v) in $args.iter().enumerate() {
                try!((match validators.get(k) {
                    Some(validator) => validator(v),
                    None => $variadic(v)
                }).or_else(|e| Err(format!("{} error at argument {}: {}", $name, k, e))));
            }
        }
    );
}

/// Creates a closure used to validate the type of the given variable.
macro_rules! jptype {
    // Validate a type against a single acceptable type.
    ($type_name:ident) => [
        Box::new(move |arg: &Rc<Variable>| -> Result<(), String> {
            let arg_type = arg.get_type();
            if arg_type != "any" && arg_type != stringify!($type_name) {
                Err(format!("type {}", stringify!($type_name)))
            } else {
                Ok(())
            }
        })
    ];
    // Validate a type against multiple acceptable types
    ($($x:ident)|*) => [
        {
            Box::new(move |arg: &Rc<Variable>| -> Result<(), String> {
                let valid_types = vec![$(stringify!($x)), *];
                let arg_type = arg.get_type();
                if arg_type != "any" && !valid_types.contains(&arg_type) {
                    Err(format!("type {}", valid_types.join("|")))
                } else {
                    Ok(())
                }
            })
        }
    ];
}

impl FnDispatcher for BuiltinFunctions {
    fn call(&self, fn_name: &str, args: &Vec<Rc<Variable>>) -> InterpretResult {
        match fn_name {
            "abs" => {
                validate!("abs", args, jptype![number]);
                Ok(Rc::new(Variable::F64(args[0].as_f64().unwrap().abs())))
            },
            "avg" => {
                try!(arity("avg", 1, args));
                args[0].as_array()
                    .and_then(|array| {
                        let mut total = 0f64;
                        for value in array {
                            match **value {
                                Variable::I64(n) => total += n as f64,
                                Variable::U64(n) => total += n as f64,
                                Variable::F64(n) => total += n,
                                _ => return None
                            }
                        }
                        Some(Rc::new(Variable::F64(total / array.len() as f64)))
                    })
                    .ok_or(type_err!("avg", 0, "array[number]", args[0]))
            },
            "ceil" => {
                validate!("ceil", args, jptype![number]);
                Ok(Rc::new(Variable::F64(args[0].as_f64().unwrap().ceil())))
            },
            "contains" => {
                validate!("contains", args, jptype![array|string], jptype![any]);
                match *args[0] {
                    Variable::Array(ref a) => Ok(Rc::new(Variable::Boolean(a.contains(&args[1])))),
                    Variable::String(ref subj) => {
                        match args[1].as_string() {
                            Some(search) => Ok(Rc::new(Variable::Boolean(subj.contains(search)))),
                            None => Err(format!("contains found {:?} for string search arg",
                                                args[1]))
                        }
                    },
                    _ => panic!() // never encountered due to previous validation
                }
            },
            "ends_with" => {
                validate!("ends_with", args, jptype![string], jptype![string]);
                let subject = args[0].as_string().unwrap();
                let search = args[1].as_string().unwrap();
                Ok(Rc::new(Variable::Boolean(subject.ends_with(search))))
            },
            "floor" => {
                validate!("floor", args, jptype![number]);
                Ok(Rc::new(Variable::F64(args[0].as_f64().unwrap().floor())))
            },
            "keys" => {
                validate!("keys", args, jptype![object]);
                Ok(Rc::new(args[0].object_keys_to_array().unwrap()))
            },
            "length" => {
                validate!("length", args, jptype![array|object|string]);
                match *args[0] {
                    Variable::Array(ref a) => Ok(Rc::new(Variable::U64(a.len() as u64))),
                    Variable::Object(ref m) => Ok(Rc::new(Variable::U64(m.len() as u64))),
                    Variable::String(ref s) => Ok(Rc::new(Variable::U64(s.len() as u64))),
                    _ => panic!() // never encountered due to previous validation
                }
            },
            "not_null" => {
                validate!("not_null", args, jptype![any] ...jptype![any]);
                for arg in args {
                    if **arg != Variable::Null {
                        return Ok(arg.clone());
                    }
                }
                Ok(Rc::new(Variable::Null))
            },
            "starts_with" => {
                validate!("starts_with", args, jptype![string], jptype![string]);
                let subject = args[0].as_string().unwrap();
                let search = args[1].as_string().unwrap();
                Ok(Rc::new(Variable::Boolean(subject.starts_with(search))))
            },
            "type" => {
                validate!("type", args, jptype![any]);
                Ok(Rc::new(Variable::String(args[0].get_type().to_string())))
            },
            "values" => {
                validate!("values", args, jptype![object]);
                Ok(Rc::new(args[0].object_values_to_array().unwrap()))
            },
            _ => Err(format!("Unknown function: {}", fn_name))
        }
    }
}
