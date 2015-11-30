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
    ($operator:ident, $args:expr, $intr:expr) => (
        {
            validate!(stringify!($operator), $args, array![string|number]);
            match *$args[0] {
                Variable::Array(ref array) if array.is_empty() => Ok($intr.arena.alloc_null()),
                Variable::Array(ref array) => {
                    if array[0].is_string() {
                        Ok($intr.arena.alloc(
                            array.iter().fold(
                                array[0].as_string().unwrap().clone(),
                                |acc, item| $operator(acc, item.as_string().unwrap().clone()))))
                    } else {
                        Ok($intr.arena.alloc(
                            array.iter().fold(
                                array[0].as_f64().unwrap(),
                                |acc, item| acc.$operator(item.as_f64().unwrap()))))
                    }
                },
                _ => unreachable!()
            }
        }
    )
}

/// Macro used to implement max_by and min_by functions.
macro_rules! max_by_min_by {
    ($operator:ident, $args:expr, $interpreter:expr) => (
        {
            validate!(stringify!($operator), $args, types![array], types![expref]);
            let vals = $args[0].as_array().expect("Expected array");
            let ast = $args[1].as_expref().expect("Expected expref");
            let initial = try!($interpreter.interpret(vals[0].clone(), ast));
            let entered_type = initial.get_type();
            if entered_type != "string" && entered_type != "number" {
                return Err(format!("{}_by expref expects string|number, found {}",
                                   stringify!($operator), entered_type));
            }
            vals.iter().skip(1).map(|v| $interpreter.interpret(v.clone(), ast))
                .fold(Ok(initial.clone()), |a, b| {
                    let (a_val, b_val) = (try!(a), try!(b));
                    if b_val.get_type() != entered_type {
                        Err(format!("{}_by expref expects {}, found {:?}",
                                    stringify!($operator), entered_type, b_val))
                    } else {
                        Ok($operator(a_val, b_val))
                    }
                })
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
                Ok(intr.arena.alloc(args[0].as_f64().expect("f64").abs()))
            },
            "avg" => {
                validate!("avg", args, array!(number));
                let array = args[0].as_array().expect("as_array");
                let sum = array.iter().fold(0f64, |a, ref b| a + b.as_f64().expect("f64"));
                Ok(intr.arena.alloc(sum / (array.len() as f64)))
            },
            "ceil" => {
                validate!("ceil", args, types![number]);
                Ok(intr.arena.alloc(args[0].as_f64().expect("f64").ceil()))
            },
            "contains" => {
                validate!("contains", args, types![array|string], types![any]);
                match *args[0] {
                    Variable::Array(ref a) => Ok(intr.arena.alloc_bool(a.contains(&args[1]))),
                    Variable::String(ref subj) => {
                        match args[1].as_string() {
                            None => Ok(intr.arena.alloc_bool(false)),
                            Some(s) => Ok(intr.arena.alloc_bool(subj.contains(s)))
                        }
                    },
                    _ => unreachable!()
                }
            },
            "ends_with" => {
                validate!("ends_with", args, types![string], types![string]);
                let subject = args[0].as_string().expect("ends_with:0:string");
                let search = args[1].as_string().expect("ends_with:1:string");
                Ok(intr.arena.alloc_bool(subject.ends_with(search)))
            },
            "floor" => {
                validate!("floor", args, types![number]);
                Ok(intr.arena.alloc(args[0].as_f64().expect("f64").floor()))
            },
            "join" => {
                validate!("join", args, types![string], array![string]);
                let mut result = String::new();
                for value in args[1].as_array().unwrap() {
                    result.push_str(value.as_string().unwrap());
                }
                Ok(intr.arena.alloc(result))
            },
            "keys" => {
                validate!("keys", args, types![object]);
                let keys = args[0].object_keys().expect("object keys")
                    .iter()
                    .map(|k| intr.arena.alloc((*k).clone()))
                    .collect::<Vec<Rc<Variable>>>();
                Ok(intr.arena.alloc(keys))
            },
            "length" => {
                validate!("length", args, types![array|object|string]);
                match *args[0] {
                    Variable::Array(ref a) => Ok(intr.arena.alloc(a.len())),
                    Variable::Object(ref m) => Ok(intr.arena.alloc(m.len())),
                    Variable::String(ref s) => Ok(intr.arena.alloc(s.len())),
                    _ => unreachable!()
                }
            },
            "map" => {
                validate!("length", args, types![expref], types![array]);
                let ast = args[0].as_expref().expect("Expected expref argument");
                let mut results = vec![];
                for value in args[1].as_array().expect("Expected array argument") {
                    results.push(try!(intr.interpret((*value).clone(), ast)));
                }
                Ok(intr.arena.alloc(results))
            },
            "max" => min_max!(max, args, intr),
            "min" => min_max!(min, args, intr),
            "max_by" => max_by_min_by!(max, args, intr),
            "min_by" => max_by_min_by!(min, args, intr),
            "merge" => {
                validate!("merge", args, types![object] ...types![object]);
                let mut result = args[0].as_object().expect("object").clone();
                for arg in args.iter().skip(1) {
                    result.extend(arg.as_object().expect("object").clone());
                }
                Ok(intr.arena.alloc(result))
            },
            "not_null" => {
                validate!("not_null", args, types![any] ...types![any]);
                for arg in args {
                    if **arg != Variable::Null {
                        return Ok(arg.clone());
                    }
                }
                Ok(intr.arena.alloc_null())
            },
            "reverse" => {
                validate!("reverse", args, types![array]);
                let mut values = args.clone();
                values.reverse();
                Ok(intr.arena.alloc(values))
            },
            "sort" => {
                validate!("sort", args, array![string|number]);
                let mut values: Vec<Rc<Variable>> = args[0].as_array().expect("array").clone();
                if values.len() != 0 {
                    if values[0].is_string() {
                        values.sort_by(|a, b| a.as_string()
                            .expect("sort_by:string")
                            .cmp(b.as_string().expect("sort_by:string (cmp)")));
                    } else {
                        values.sort_by(|a, b| a.as_f64().expect("f64")
                            .partial_cmp(&b.as_f64().expect("f64"))
                            .unwrap_or(Ordering::Equal));
                    }
                }
                Ok(intr.arena.alloc(values))
            },
            "sort_by" => sort_by(args, intr),
            "starts_with" => {
                validate!("starts_with", args, types![string], types![string]);
                let subject = args[0].as_string().expect("starts_with:0:string");
                let search = args[1].as_string().expect("starts_with:1:string");
                Ok(intr.arena.alloc_bool(subject.starts_with(search)))
            },
            "sum" => {
                validate!("sum", args, array![number]);
                let array = args[0].as_array().expect("array");
                if array.len() == 0 {
                    Ok(intr.arena.alloc(vec![]))
                } else {
                    Ok(intr.arena.alloc(array.iter().fold(
                        array[0].as_f64().expect("f64").clone(),
                        |acc, item| acc.max(item.as_f64().expect("f64")))))
                }
            },
            "to_array" => {
                try!(arity("to_array", 1, args));
                match *args[0] {
                    Variable::Array(_) => Ok(args[0].clone()),
                    _ => Ok(intr.arena.alloc(vec![args[0].clone()]))
                }
            },
            "to_number" => {
                try!(arity("to_number", 1, args));
                match *args[0] {
                    Variable::I64(_) | Variable::F64(_) | Variable::U64(_) => Ok(args[0].clone()),
                    Variable::String(ref s) => {
                        match s.parse::<f64>() {
                            Ok(f)  => Ok(intr.arena.alloc(f)),
                            Err(_) => Ok(intr.arena.alloc_null())
                        }
                    },
                    _ => Ok(intr.arena.alloc_null())
                }
            },
            "to_string" => {
                validate!("to_string", args, types![object|array|boolean|number|string|null]);
                Ok(intr.arena.alloc(args[0].to_string().expect("cast to string")))
            },
            "type" => {
                try!(arity("type", 1, args));
                Ok(intr.arena.alloc(args[0].get_type().to_string()))
            },
            "values" => {
                validate!("values", args, types![object]);
                Ok(intr.arena.alloc(args[0].object_values().expect("Object")))
            },
            _ => Err(format!("Unknown function: {}", fn_name))
        }
    }
}

enum SortByState {
    Initial,
    FoundString,
    FoundNumber,
    Error(String)
}

fn sort_by(args: &Vec<Rc<Variable>>, intr: &TreeInterpreter) -> InterpretResult {
    validate!("sort_by", args, types![array], types![expref]);
    let mut state = SortByState::Initial;
    let mut vals = args[0].as_array().expect("Expected array").clone();
    let ast = args[1].as_expref().expect("Expected expref");

    vals.sort_by(|ref lhs, ref rhs| {
        if let SortByState::Error(_) = state {
            return Ordering::Equal;
        }
        let a = match intr.interpret((*lhs).clone(), ast) {
            Ok(result) => result,
            Err(e) => {
                state = SortByState::Error(e);
                return Ordering::Equal
            }
        };
        let b = match intr.interpret((*rhs).clone(), ast) {
            Ok(result) => result,
            Err(e) => {
                state = SortByState::Error(e);
                return Ordering::Equal
            }
        };
        let a_type = a.get_type();
        let b_type = b.get_type();
        match state {
            SortByState::Initial if a_type == "string" && b_type == a_type => {
                state = SortByState::FoundString;
                a.as_string().expect("string").cmp(b.as_string().expect("string"))
            },
            SortByState::Initial if a_type == "number" && b_type == a_type => {
                state = SortByState::FoundNumber;
                a.as_f64().expect("f64").partial_cmp(&b.as_f64().expect("f64")).expect("cmp")
            },
            SortByState::FoundString if a_type == "string" && b_type == "string" =>
                a.as_string().expect("string").cmp(b.as_string().expect("string")),
            SortByState::FoundNumber if a_type == "number" && b_type == "number" =>
                a.as_f64().expect("f64").partial_cmp(&b.as_f64().expect("f64")).expect("cmp"),
            _ => {
                state = SortByState::Error("sort_by expref is expected to return all strings \
                                           or all numbers".to_string());
                Ordering::Equal
            }
        }
    });

    match state {
        SortByState::Initial => Ok(intr.arena.alloc(vec![])),
        SortByState::Error(e) => Err(e),
        _ => Ok(intr.arena.alloc(vals))
    }
}
