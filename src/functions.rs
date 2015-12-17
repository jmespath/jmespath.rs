use std::collections::{BTreeMap, HashMap};
use std::rc::Rc;
use std::cmp::{max, min, Ordering};
use std::fmt;

use super::RuntimeError;
use super::interpreter::{TreeInterpreter, JPResult};
use super::variable::Variable;

/// Represents an argument type
#[derive(Clone,Debug,PartialEq)]
pub enum ArgumentType {
    Any,
    String,
    Number,
    Boolean,
    Array,
    Object,
    Null,
    Expref,
    HomogeneousArray(Vec<ArgumentType>),
    OneOf(Vec<ArgumentType>),
    ExprefReturns(Vec<ArgumentType>)
}

impl ArgumentType {
    /// Convert a Vec of types to Vec<String>
    pub fn types_to_strings(types: &Vec<ArgumentType>) -> Vec<String> {
        types.iter().map(|t| t.to_string()).collect::<Vec<String>>()
    }

    /// Returns true/false if the variable is valid for the type.
    pub fn is_valid(&self, value: &Rc<Variable>) -> bool {
        use self::ArgumentType::*;
        match self {
            &Any => true,
            &Null if value.is_null() => true,
            &String if value.is_string() => true,
            &Number if value.is_number() => true,
            &Object if value.is_object() => true,
            &Boolean if value.is_boolean() => true,
            &Expref if value.is_expref() => true,
            &ExprefReturns(_) if value.is_expref() => true,
            &Array if value.is_array() => true,
            &OneOf(ref types) => types.iter().any(|t| t.is_valid(value)),
            &HomogeneousArray(ref types) if value.is_array() => {
                let values = value.as_array().unwrap();
                if values.is_empty() {
                    true
                } else {
                    let alts = OneOf(types.clone());
                    let first_type = values[0].get_type();
                    values.iter().all(|v| alts.is_valid(v) && v.get_type() == first_type)
                }
            },
            _ => false
        }
    }
}

impl fmt::Display for ArgumentType {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        use self::ArgumentType::*;
        match self {
            &Any => write!(fmt, "any"),
            &String => write!(fmt, "string"),
            &Number => write!(fmt, "number"),
            &Boolean => write!(fmt, "boolean"),
            &Array => write!(fmt, "array"),
            &Object => write!(fmt, "object"),
            &Null => write!(fmt, "null"),
            &Expref => write!(fmt, "expref"),
            &ExprefReturns(ref types) => {
                let mut type_strings = vec![];
                for t in types {
                    type_strings.push(format!("expref->{}", t));
                }
                write!(fmt, "{}", type_strings.join("|"))
            },
            &OneOf(ref types) => write!(fmt, "{}", Self::types_to_strings(types).join("|")),
            &HomogeneousArray(ref types) => {
                write!(fmt, "array[{}]", Self::types_to_strings(types).join("|"))
            }
        }
    }
}

/// JMESPath function
pub trait JPFunction {
    /// Evaluates a function with the given arguments
    fn evaluate(&self, args: Vec<Rc<Variable>>, intr: &TreeInterpreter) -> JPResult;
}

/// Map of JMESPath function names to their implementation
pub type Functions = HashMap<String, Box<JPFunction + 'static>>;

/// Validates the arity of a function.
#[inline]
fn validate_arity(expected: usize, actual: usize) -> Result<(), RuntimeError> {
    if actual == expected {
        Ok(())
    } else if actual < expected {
        Err(RuntimeError::NotEnoughArguments { expected: expected, actual: actual })
    } else {
        Err(RuntimeError::TooManyArguments { expected: expected, actual: actual })
    }
}

/// Macro used to variadically validate validate Variable and argument arity.
#[macro_export]
macro_rules! validate {
    // Validate positional arguments only.
    ($args:expr, $($x:expr),*) => (
        {
            let arg_types: Vec<ArgumentType> = vec![$($x), *];
            try!(validate_arity(arg_types.len(), $args.len()));
            for (k, v) in $args.iter().enumerate() {
                if !arg_types[k].is_valid(v) {
                    return Err(RuntimeError::wrong_type(
                        arg_types[k].to_string(), v.get_type(), k));
                }
            }
        }
    );
    // Validate positional arguments with a variadic validator.
    ($args:expr, $($x:expr),* ...$variadic:expr ) => (
        {
            let arg_types: Vec<ArgumentType> = vec![$($x), *];
            // Validate the minimum arity
            if $args.len() < arg_types.len() {
                return Err(RuntimeError::NotEnoughArguments {
                    expected: arg_types.len(),
                    actual: $args.len()
                });
            }
            // Validate each variadic agument
            for (k, v) in $args.iter().enumerate() {
                if !$variadic.is_valid(v) {
                    return Err(RuntimeError::wrong_type(
                        $variadic.to_string(), v.get_type(), k));
                }
                match arg_types.get(k) {
                    Some(validator) => {
                        if !validator.is_valid(v) {
                            return Err(RuntimeError::wrong_type(
                                validator.to_string(), v.get_type(), k));
                        }
                    },
                    None => {
                        if !$variadic.is_valid(v) {
                            return Err(RuntimeError::wrong_type(
                                $variadic.to_string(), v.get_type(), k));
                        }
                    }
                }
            }
        }
    );
}

/// Macro used to implement max_by and min_by functions.
macro_rules! max_by_min_by {
    ($operator:ident, $args:expr, $interpreter:expr) => (
        {
            validate!($args, ArgumentType::Array, ArgumentType::Expref);
            let vals = $args[0].as_array().unwrap();
            let ast = $args[1].as_expref().unwrap();
            let initial = try!($interpreter.interpret(vals[0].clone(), &ast));
            let entered_type = initial.get_type();
            if entered_type != "string" && entered_type != "number" {
                return Err(RuntimeError::wrong_type(
                    "expression->number|expression->string".to_string(),
                    entered_type, 1));
            }
            vals.iter().skip(1).map(|v| $interpreter.interpret(v.clone(), &ast))
                .fold(Ok(initial.clone()), |a, b| {
                    let (a_val, b_val) = (try!(a), try!(b));
                    if b_val.get_type() != entered_type {
                        Err(RuntimeError::wrong_type(
                            format!("expression->{}", entered_type),
                            b_val.get_type(), 1))
                    } else {
                        Ok($operator(a_val, b_val))
                    }
                })
        }
    )
}

/// Registers the default JMESPath functions into a map.
pub fn register_core_functions(functions: &mut Functions) {
    functions.insert("abs".to_string(), Box::new(Abs));
    functions.insert("avg".to_string(), Box::new(Avg));
    functions.insert("ceil".to_string(), Box::new(Ceil));
    functions.insert("contains".to_string(), Box::new(Contains));
    functions.insert("ends_with".to_string(), Box::new(EndsWith));
    functions.insert("floor".to_string(), Box::new(Floor));
    functions.insert("join".to_string(), Box::new(Join));
    functions.insert("keys".to_string(), Box::new(Keys));
    functions.insert("length".to_string(), Box::new(Length));
    functions.insert("map".to_string(), Box::new(Map));
    functions.insert("min".to_string(), Box::new(Min));
    functions.insert("max".to_string(), Box::new(Max));
    functions.insert("max_by".to_string(), Box::new(MaxBy));
    functions.insert("min_by".to_string(), Box::new(MinBy));
    functions.insert("merge".to_string(), Box::new(Merge));
    functions.insert("not_null".to_string(), Box::new(NotNull));
    functions.insert("reverse".to_string(), Box::new(Reverse));
    functions.insert("sort".to_string(), Box::new(Sort));
    functions.insert("sort_by".to_string(), Box::new(SortBy));
    functions.insert("starts_with".to_string(), Box::new(StartsWith));
    functions.insert("sum".to_string(), Box::new(Sum));
    functions.insert("to_array".to_string(), Box::new(ToArray));
    functions.insert("to_number".to_string(), Box::new(ToNumber));
    functions.insert("to_string".to_string(), Box::new(ToString));
    functions.insert("type".to_string(), Box::new(Type));
    functions.insert("values".to_string(), Box::new(Values));
}

struct Abs;

impl JPFunction for Abs {
    fn evaluate(&self, args: Vec<Rc<Variable>>, intr: &TreeInterpreter) -> JPResult {
        validate![args, ArgumentType::Number];
        let n = args[0].as_number().unwrap();
        Ok(intr.arena.alloc(n.abs()))
    }
}

struct Avg;

impl JPFunction for Avg {
    fn evaluate(&self, args: Vec<Rc<Variable>>, intr: &TreeInterpreter) -> JPResult {
        validate!(args, ArgumentType::HomogeneousArray(vec![ArgumentType::Number]));
        let values = args[0].as_array().unwrap();
        let sum = values.iter()
            .map(|n| n.as_number().unwrap())
            .fold(0f64, |a, ref b| a + b);
        Ok(intr.arena.alloc(sum / (values.len() as f64)))
    }
}

struct Ceil;

impl JPFunction for Ceil {
    fn evaluate(&self, args: Vec<Rc<Variable>>, intr: &TreeInterpreter) -> JPResult {
        validate!(args, ArgumentType::Number);
        let n = args[0].as_number().unwrap();
        Ok(intr.arena.alloc(n.ceil()))
    }
}

struct Contains;

impl JPFunction for Contains {
    fn evaluate(&self, args: Vec<Rc<Variable>>, intr: &TreeInterpreter) -> JPResult {
        validate!(args, ArgumentType::OneOf(vec![ArgumentType::String, ArgumentType::Array]),
            ArgumentType::Any);
        let ref haystack = args[0];
        let ref needle = args[1];
        match **haystack {
           Variable::Array(ref a) => Ok(intr.arena.alloc_bool(a.contains(&needle))),
           Variable::String(ref subj) => {
               match needle.as_string() {
                   None => Ok(intr.arena.alloc_bool(false)),
                   Some(s) => Ok(intr.arena.alloc_bool(subj.contains(s)))
               }
           },
           _ => unreachable!()
        }
    }
}

struct EndsWith;

impl JPFunction for EndsWith {
    fn evaluate(&self, args: Vec<Rc<Variable>>, intr: &TreeInterpreter) -> JPResult {
        validate!(args, ArgumentType::String, ArgumentType::String);
        let subject = args[0].as_string().unwrap();
        let search = args[1].as_string().unwrap();
        Ok(intr.arena.alloc_bool(subject.ends_with(search)))
    }
}

struct Floor;

impl JPFunction for Floor {
    fn evaluate(&self, args: Vec<Rc<Variable>>, intr: &TreeInterpreter) -> JPResult {
        validate!(args, ArgumentType::Number);
        let n = args[0].as_number().unwrap();
        Ok(intr.arena.alloc(n.floor()))
    }
}

struct Join;

impl JPFunction for Join {
    fn evaluate(&self, args: Vec<Rc<Variable>>, intr: &TreeInterpreter) -> JPResult {
        validate!(args, ArgumentType::String,
            ArgumentType::HomogeneousArray(vec![ArgumentType::String]));
        let glue = args[0].as_string().unwrap();
        let values = args[1].as_array().unwrap();
        let result = values.iter()
            .map(|v| v.as_string().unwrap())
            .cloned()
            .collect::<Vec<String>>()
            .join(&glue);
        Ok(intr.arena.alloc(result))
    }
}

struct Keys;

impl JPFunction for Keys {
    fn evaluate(&self, args: Vec<Rc<Variable>>, intr: &TreeInterpreter) -> JPResult {
        validate!(args, ArgumentType::Object);
        let object = args[0].as_object().unwrap();
        let keys = object.keys()
            .map(|k| intr.arena.alloc((*k).clone()))
            .collect::<Vec<Rc<Variable>>>();
        Ok(intr.arena.alloc(keys))
    }
}

struct Length;

impl JPFunction for Length {
    fn evaluate(&self, args: Vec<Rc<Variable>>, intr: &TreeInterpreter) -> JPResult {
        let acceptable = vec![ArgumentType::Array, ArgumentType::Object, ArgumentType::String];
        validate!(args, ArgumentType::OneOf(acceptable));
        match *args[0] {
            Variable::Array(ref a) => Ok(intr.arena.alloc(a.len())),
            Variable::Object(ref m) => Ok(intr.arena.alloc(m.len())),
            Variable::String(ref s) => Ok(intr.arena.alloc(s.len())),
            _ => unreachable!()
        }
    }
}

struct Map;

impl JPFunction for Map {
    fn evaluate(&self, args: Vec<Rc<Variable>>, intr: &TreeInterpreter) -> JPResult {
        validate!(args, ArgumentType::Expref, ArgumentType::Array);
        let ast = args[0].as_expref().unwrap();
        let values = args[1].as_array().unwrap();
        let mut results = vec![];
        for value in values {
            results.push(try!(intr.interpret(value.clone(), &ast)));
        }
        Ok(intr.arena.alloc(results))
    }
}

struct Max;

impl JPFunction for Max {
    fn evaluate(&self, args: Vec<Rc<Variable>>, intr: &TreeInterpreter) -> JPResult {
        let acceptable = vec![ArgumentType::String, ArgumentType::Number];
        validate!(args, ArgumentType::HomogeneousArray(acceptable));
        let values = args[0].as_array().unwrap();
        let initial = intr.arena.alloc_null();
        let result: Rc<Variable> = values
            .iter()
            .skip(1)
            .fold(initial, |acc, item| max(acc, item.clone()));
        Ok(result)
    }
}

struct Min;

impl JPFunction for Min {
    fn evaluate(&self, args: Vec<Rc<Variable>>, intr: &TreeInterpreter) -> JPResult {
        let acceptable = vec![ArgumentType::String, ArgumentType::Number];
        validate!(args, ArgumentType::HomogeneousArray(acceptable));
        let values = args[0].as_array().unwrap();
        let initial = intr.arena.alloc_null();
        let result: Rc<Variable> = values
            .iter()
            .skip(1)
            .fold(initial, |acc, item| min(acc, item.clone()));
        Ok(result)
    }
}

struct MaxBy;

impl JPFunction for MaxBy {
    fn evaluate(&self, args: Vec<Rc<Variable>>, intr: &TreeInterpreter) -> JPResult {
        max_by_min_by!(max, args, intr)
    }
}

struct MinBy;

impl JPFunction for MinBy {
    fn evaluate(&self, args: Vec<Rc<Variable>>, intr: &TreeInterpreter) -> JPResult {
        max_by_min_by!(min, args, intr)
    }
}

struct Merge;

impl JPFunction for Merge {
    fn evaluate(&self, args: Vec<Rc<Variable>>, intr: &TreeInterpreter) -> JPResult {
        validate!(args, ArgumentType::Object ...ArgumentType::Object);
        let mut result = BTreeMap::new();
        for arg in args {
            result.extend(arg.as_object().unwrap().clone());
        }
        Ok(intr.arena.alloc(result))
    }
}

struct NotNull;

impl JPFunction for NotNull {
    fn evaluate(&self, args: Vec<Rc<Variable>>, intr: &TreeInterpreter) -> JPResult {
        validate!(args, ArgumentType::Any ...ArgumentType::Any);
        for arg in args {
            if !arg.is_null() {
                return Ok(arg.clone());
            }
        }
        Ok(intr.arena.alloc_null())
    }
}

struct Reverse;

impl JPFunction for Reverse {
    fn evaluate(&self, args: Vec<Rc<Variable>>, intr: &TreeInterpreter) -> JPResult {
        validate!(args, ArgumentType::Array);
        let mut values = args[0].as_array().unwrap().clone();
        values.reverse();
        Ok(intr.arena.alloc(values))
    }
}

struct Sort;

impl JPFunction for Sort {
    fn evaluate(&self, args: Vec<Rc<Variable>>, intr: &TreeInterpreter) -> JPResult {
        let acceptable = vec![ArgumentType::String, ArgumentType::Number];
        validate!(args, ArgumentType::HomogeneousArray(acceptable));
        let mut values = args[0].as_array().unwrap().clone();
        values.sort();
        Ok(intr.arena.alloc(values))
    }
}

enum SortByState {
    Initial,
    FoundString,
    FoundNumber,
    Error(RuntimeError)
}

struct SortBy;

impl JPFunction for SortBy {
    fn evaluate(&self, args: Vec<Rc<Variable>>, intr: &TreeInterpreter) -> JPResult {
        validate!(args, ArgumentType::Array, ArgumentType::Expref);
        let mut state = SortByState::Initial;
        let mut vals = args[0].as_array().unwrap().clone();
        let ast = args[1].as_expref().unwrap();
        vals.sort_by(|ref lhs, ref rhs| {
            if let SortByState::Error(_) = state {
                return Ordering::Equal;
            }
            let a = match intr.interpret((*lhs).clone(), &ast) {
                Ok(result) => result,
                Err(e) => {
                    state = SortByState::Error(e);
                    return Ordering::Equal
                }
            };
            let b = match intr.interpret((*rhs).clone(), &ast) {
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
                    a.as_string().unwrap().cmp(b.as_string().unwrap())
                },
                SortByState::Initial if a_type == "number" && b_type == a_type => {
                    state = SortByState::FoundNumber;
                    a.as_number().unwrap().partial_cmp(&b.as_number().unwrap()).unwrap()
                },
                SortByState::FoundString if a_type == "string" && b_type == "string" =>
                    a.as_string().unwrap().cmp(b.as_string().unwrap()),
                SortByState::FoundNumber if a_type == "number" && b_type == "number" =>
                    a.as_number().unwrap().partial_cmp(&b.as_number().unwrap()).unwrap(),
                _ => {
                    let expr_string = format!("{}", ArgumentType::ExprefReturns(
                        vec![ArgumentType::Number, ArgumentType::String]));
                    state = SortByState::Error(
                        RuntimeError::wrong_return_type(expr_string, b_type, 1));
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
}

struct StartsWith;

impl JPFunction for StartsWith {
    fn evaluate(&self, args: Vec<Rc<Variable>>, intr: &TreeInterpreter) -> JPResult {
        validate!(args, ArgumentType::String, ArgumentType::String);
        let subject = args[0].as_string().unwrap();
        let search = args[1].as_string().unwrap();
        Ok(intr.arena.alloc_bool(subject.starts_with(search)))
    }
}

struct Sum;

impl JPFunction for Sum {
    fn evaluate(&self, args: Vec<Rc<Variable>>, intr: &TreeInterpreter) -> JPResult {
        validate!(args, ArgumentType::HomogeneousArray(vec![ArgumentType::Number]));
        let result = args[0].as_array().unwrap().iter().fold(
            0.0, |acc, item| acc + item.as_number().unwrap());
        Ok(intr.arena.alloc(result))
    }
}

struct ToArray;

impl JPFunction for ToArray {
    fn evaluate(&self, args: Vec<Rc<Variable>>, intr: &TreeInterpreter) -> JPResult {
        validate!(args, ArgumentType::Any);
        match *args[0] {
            Variable::Array(_) => Ok(args[0].clone()),
            _ => Ok(intr.arena.alloc(vec![args[0].clone()]))
        }
    }
}

struct ToNumber;

impl JPFunction for ToNumber {
    fn evaluate(&self, args: Vec<Rc<Variable>>, intr: &TreeInterpreter) -> JPResult {
        validate!(args, ArgumentType::Any);
        match *args[0] {
            Variable::Number(_) => Ok(args[0].clone()),
            Variable::String(ref s) => {
                match s.parse::<f64>() {
                    Ok(f)  => Ok(intr.arena.alloc(f)),
                    Err(_) => Ok(intr.arena.alloc_null())
                }
            },
            _ => Ok(intr.arena.alloc_null())
        }
    }
}

struct ToString;

impl JPFunction for ToString {
    fn evaluate(&self, args: Vec<Rc<Variable>>, intr: &TreeInterpreter) -> JPResult {
        validate!(args, ArgumentType::OneOf(vec![
            ArgumentType::Object, ArgumentType::Array, ArgumentType::Boolean,
            ArgumentType::Number, ArgumentType::String, ArgumentType::Null]));
        Ok(intr.arena.alloc(args[0].to_string().unwrap()))
    }
}

struct Type;

impl JPFunction for Type {
    fn evaluate(&self, args: Vec<Rc<Variable>>, intr: &TreeInterpreter) -> JPResult {
        validate!(args, ArgumentType::Any);
        Ok(intr.arena.alloc(args[0].get_type().to_string()))
    }
}

struct Values;

impl JPFunction for Values {
    fn evaluate(&self, args: Vec<Rc<Variable>>, intr: &TreeInterpreter) -> JPResult {
        validate!(args, ArgumentType::Object);
        let map = args[0].as_object().unwrap();
        Ok(intr.arena.alloc(map.values().cloned().collect::<Vec<Rc<Variable>>>()))
    }
}
