use std::rc::Rc;

use std::cmp::{max, min, Ordering};
use interpreter::{TreeInterpreter, InterpretResult};
use variable::Variable;

/// Handles the dispatching of named functions using an array of arguments.
pub trait FnDispatcher {
    /// Dispatches and interprets a function by name.
    fn call(&self, fn_name: &str, args: &Vec<Rc<Variable>>, intr: &TreeInterpreter)
        -> InterpretResult;
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

/// Validates that an array contains only a single allowed type.
#[inline]
fn homogeneous_array(valid_types: Vec<&str>, array: &Vec<Rc<Variable>>) -> bool {
    let matched_type = array[0].get_type();
    if !valid_types.contains(&matched_type) {
        return false;
    }
    for a in array {
        if a.get_type() != matched_type {
            return false;
        }
    }
    return true;
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

/// Validates that a vector contains a homogeneous array of a specific type(s).
macro_rules! array {
    ($($x:ident)|*) => [
        Box::new(move |arg: &Rc<Variable>| -> Result<(), String> {
            let valid_types = vec![$(stringify!($x)), *];
            match **arg {
                Variable::Array(ref array) if array.is_empty() => Ok(()),
                Variable::Array(ref array) if homogeneous_array(valid_types, array) => Ok(()),
                _ => Err(format!("type array[{}]", valid_types.join("|")))
            }
        })
    ];
}

/// Creates a closure used to validate the type of the given variable.
macro_rules! types {
    ($($x:ident)|*) => [
        {
            Box::new(move |arg: &Rc<Variable>| -> Result<(), String> {
                let valid_types = vec![$(stringify!($x)), *];
                let arg_type = arg.get_type();
                if arg_type == "any" || valid_types.contains(&arg_type) {
                    Ok(())
                } else {
                    Err(format!("type {}", valid_types.join("|")))
                }
            })
        }
    ];
}

/// Macro used to implement min and max functions.
macro_rules! min_max {
    ($operator:ident, $args:expr) => (
        match *$args[0] {
            Variable::Array(ref array) if array.is_empty() => Ok(Rc::new(Variable::Null)),
            Variable::Array(ref array) => {
                if array[0].is_string() {
                    Ok(Rc::new(Variable::String(array.iter().fold(
                        array[0].as_string().unwrap().clone(),
                        |acc, item| $operator(acc, item.as_string().unwrap().clone())))))
                } else {
                    Ok(Rc::new(Variable::F64(array.iter().fold(
                        array[0].as_f64().unwrap(),
                        |acc, item| acc.$operator(item.as_f64().unwrap())))))
                }
            },
            _ => panic!() // never encountered due to previous validation
        }
    )
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
    fn call(&self, fn_name: &str, args: &Vec<Rc<Variable>>, intr: &TreeInterpreter)
        -> InterpretResult
    {
        match fn_name {
            "abs" => {
                validate!("abs", args, types![number]);
                Ok(Rc::new(Variable::F64(args[0].as_f64().unwrap().abs())))
            },
            "avg" => {
                validate!("avg", args, array!(number));
                let array = args[0].as_array().unwrap();
                let sum = array.iter().fold(0f64, |a, ref b| a + b.as_f64().unwrap());
                Ok(Rc::new(Variable::F64(sum / (array.len() as f64))))
            },
            "ceil" => {
                validate!("ceil", args, types![number]);
                Ok(Rc::new(Variable::F64(args[0].as_f64().unwrap().ceil())))
            },
            "contains" => {
                validate!("contains", args, types![array|string], types![any]);
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
                validate!("ends_with", args, types![string], types![string]);
                let subject = args[0].as_string().unwrap();
                let search = args[1].as_string().unwrap();
                Ok(Rc::new(Variable::Boolean(subject.ends_with(search))))
            },
            "floor" => {
                validate!("floor", args, types![number]);
                Ok(Rc::new(Variable::F64(args[0].as_f64().unwrap().floor())))
            },
            "join" => {
                validate!("join", args, types![string], array![string]);
                Ok(Rc::new(Variable::String(args.iter().skip(1)
                    .map(|ref v| v.as_string().unwrap().clone())
                    .collect::<Vec<String>>()
                    .join(args[0].as_string().unwrap()))))
            },
            "keys" => {
                validate!("keys", args, types![object]);
                Ok(Rc::new(args[0].object_keys_to_array().unwrap()))
            },
            "length" => {
                validate!("length", args, types![array|object|string]);
                match *args[0] {
                    Variable::Array(ref a) => Ok(Rc::new(Variable::U64(a.len() as u64))),
                    Variable::Object(ref m) => Ok(Rc::new(Variable::U64(m.len() as u64))),
                    Variable::String(ref s) => Ok(Rc::new(Variable::U64(s.len() as u64))),
                    _ => panic!() // never encountered due to previous validation
                }
            },
            "max" => {
                validate!("max", args, array![string|number]);
                min_max!(max, args)
            },
            "max_by" => {
                validate!("max_by", args, types![array], types![expref]);
                let vals = args[0].as_array().expect("Expected array");
                let ast = args[1].as_expref().expect("Expected expref");
                if vals.is_empty() { return Ok(Rc::new(Variable::Null)); }
                let mut acc = try!(intr.interpret(args[0].clone(), ast));
                let iter = vals.iter().skip(1).map(|v| intr.interpret(v.clone(), ast));
                match acc.get_type() {
                    "string" => {
                        for item in iter {
                            match item {
                                Err(_) => return item,
                                Ok(ref v) if v.is_string() => acc = max(acc, v.clone()),
                                _ => return Err(format!("max_by: expected string from expref. \
                                                         Found {:?}", item))
                            }
                        }
                    },
                    "number" => {
                        for item in iter {
                            match item {
                                Err(_) => return item,
                                Ok(ref v) if v.is_number() => acc = max(acc, v.clone()),
                                _ => return Err(format!("max_by: expected number from expref. \
                                                         Found {:?}", item))
                            }
                        }
                    },
                    _ => return Err("max_by: expected string or number from expref".to_string())
                }
                Ok(acc)
            },
            "merge" => {
                validate!("merge", args, types![object] ...types![object]);
                let mut result = args[0].as_object().unwrap().clone();
                for arg in args.iter().skip(1) {
                    result.extend(arg.as_object().unwrap().clone());
                }
                Ok(Rc::new(Variable::Object(result)))
            },
            "min" => {
                validate!("min", args, array![string|number]);
                min_max!(min, args)
            },
            "not_null" => {
                validate!("not_null", args, types![any] ...types![any]);
                for arg in args {
                    if **arg != Variable::Null {
                        return Ok(arg.clone());
                    }
                }
                Ok(Rc::new(Variable::Null))
            },
            "reverse" => {
                validate!("reverse", args, types![array]);
                let mut values = args.clone();
                values.reverse();
                Ok(Rc::new(Variable::Array(values)))
            },
            "sort" => {
                validate!("sort", args, array![string|number]);
                let mut values: Vec<Rc<Variable>> = args[0].as_array().unwrap().clone();
                if values[0].is_string() {
                    values.sort_by(|a, b| a.as_string().unwrap().cmp(b.as_string().unwrap()));
                } else {
                    values.sort_by(|a, b| a.as_f64().unwrap()
                        .partial_cmp(&b.as_f64().unwrap())
                        .unwrap_or(Ordering::Equal));
                }
                Ok(Rc::new(Variable::Array(values)))
            },
            "starts_with" => {
                validate!("starts_with", args, types![string], types![string]);
                let subject = args[0].as_string().unwrap();
                let search = args[1].as_string().unwrap();
                Ok(Rc::new(Variable::Boolean(subject.starts_with(search))))
            },
            "sum" => {
                validate!("sum", args, array![number]);
                let array = args[0].as_array().unwrap();
                Ok(Rc::new(Variable::F64(array.iter().fold(
                    array[0].as_f64().unwrap().clone(),
                    |acc, item| acc.max(item.as_f64().unwrap())))))
            },
            "to_array" => {
                try!(arity("to_array", 1, args));
                match *args[0] {
                    Variable::Array(_) => Ok(args[0].clone()),
                    _ => Ok(Rc::new(Variable::Array(vec![args[0].clone()])))
                }
            },
            "to_number" => {
                try!(arity("to_number", 1, args));
                match *args[0] {
                    Variable::I64(_) | Variable::F64(_) | Variable::U64(_) => Ok(args[0].clone()),
                    Variable::String(ref s) => {
                        match s.parse::<f64>() {
                            Ok(f)  => Ok(Rc::new(Variable::F64(f))),
                            Err(_) => Ok(Rc::new(Variable::Null))
                        }
                    },
                    _ => Ok(Rc::new(Variable::Null))
                }
            },
            "to_string" => {
                validate!("to_string", args, types![object|array|boolean|number|string|null]);
                Ok(Rc::new(Variable::String(args[0].to_string().unwrap())))
            },
            "type" => {
                try!(arity("type", 1, args));
                Ok(Rc::new(Variable::String(args[0].get_type().to_string())))
            },
            "values" => {
                validate!("values", args, types![object]);
                Ok(Rc::new(args[0].object_values_to_array().unwrap()))
            },
            _ => Err(format!("Unknown function: {}", fn_name))
        }
    }
}
