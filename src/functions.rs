//! JMESPath functions.

use std::collections::HashMap;
use std::collections::BTreeMap;
use std::cmp::{max, min};
use std::fmt;
use std::rc::Rc;

use super::{Context, Error, ErrorReason, RcVar, RuntimeError};
use super::interpreter::{interpret, SearchResult};
use super::variable::Variable;

/* ------------------------------------------
 * Argument types
 * ------------------------------------------ */

/// Function argument types used when validating.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum ArgumentType {
    Any,
    Null,
    String,
    Number,
    Bool,
    Object,
    Array,
    Expref,
    /// Each element of the array must matched the provided type.
    TypedArray(Box<ArgumentType>),
    /// Accepts one of a number of `ArgumentType`s
    Union(Vec<ArgumentType>),
}

impl ArgumentType {
    /// Returns true/false if the variable is valid for the type.
    pub fn is_valid(&self, value: &RcVar) -> bool {
        use self::ArgumentType::*;
        match *self {
            Any => true,
            Null if value.is_null() => true,
            String if value.is_string() => true,
            Number if value.is_number() => true,
            Object if value.is_object() => true,
            Bool if value.is_boolean() => true,
            Expref if value.is_expref() => true,
            Array if value.is_array() => true,
            TypedArray(ref t) if value.is_array() => {
                value.as_array().unwrap().iter().all(|v| t.is_valid(v))
            },
            Union(ref types) => types.iter().any(|t| t.is_valid(value)),
            _ => false
        }
    }
}

impl fmt::Display for ArgumentType {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        use self::ArgumentType::*;
        match *self {
            Any => write!(fmt, "any"),
            String => write!(fmt, "string"),
            Number => write!(fmt, "number"),
            Bool => write!(fmt, "boolean"),
            Array => write!(fmt, "array"),
            Object => write!(fmt, "object"),
            Null => write!(fmt, "null"),
            Expref => write!(fmt, "expref"),
            TypedArray(ref t) => write!(fmt, "array[{}]", t),
            Union(ref types) => {
                let str_value = types.iter().map(|t| t.to_string()).collect::<Vec<_>>().join("|");
                write!(fmt, "{}", str_value)
            },
        }
    }
}

macro_rules! arg {
    (any) => (ArgumentType::Any);
    (null) => (ArgumentType::Null);
    (string) => (ArgumentType::String);
    (bool) => (ArgumentType::Bool);
    (number) => (ArgumentType::Number);
    (object) => (ArgumentType::Object);
    (expref) => (ArgumentType::Expref);
    (array_number) => (ArgumentType::TypedArray(Box::new(ArgumentType::Number)));
    (array_string) => (ArgumentType::TypedArray(Box::new(ArgumentType::String)));
    (array) => (ArgumentType::Array);
    ($($x:ident) | *) => (ArgumentType::Union(vec![$(arg!($x)), *]));
}

/* ------------------------------------------
 * Function registry and default registry
 * ------------------------------------------ */

/// Stores and evaluates JMESPath functions.
pub trait FnRegistry {
    /// Gets a function signature by name from the registry.
    ///
    /// Returns the signature if found, or None if not found.
    fn get_signature(&self, name: &str) -> Option<&Signature>;

    /// Evaluates a function by name in the registry.
    ///
    /// The registry is responsible for validating function signatures
    /// before invoking the function, and functions should assume that
    /// the arguments provided to them are correct.
    fn evaluate(&self, name: &str, args: &[RcVar], ctx: &mut Context) -> Option<SearchResult>;
}

/// Default JMESPath function registry.
pub struct BuiltinFnRegistry {
    functions: HashMap<String, Box<Function>>,
}

impl BuiltinFnRegistry {
    /// Creates a new BuiltinFnRegistry.
    pub fn new() -> BuiltinFnRegistry {
        let mut funcs: HashMap<String, Box<Function>> = HashMap::with_capacity(26);
        funcs.insert("abs".to_owned(), Box::new(AbsFn::new()));
        funcs.insert("avg".to_owned(), Box::new(AvgFn::new()));
        funcs.insert("ceil".to_owned(), Box::new(CeilFn::new()));
        funcs.insert("contains".to_owned(), Box::new(ContainsFn::new()));
        funcs.insert("ends_with".to_owned(), Box::new(EndsWithFn::new()));
        funcs.insert("floor".to_owned(), Box::new(FloorFn::new()));
        funcs.insert("join".to_owned(), Box::new(JoinFn::new()));
        funcs.insert("keys".to_owned(), Box::new(KeysFn::new()));
        funcs.insert("length".to_owned(), Box::new(LengthFn::new()));
        funcs.insert("map".to_owned(), Box::new(MapFn::new()));
        funcs.insert("min".to_owned(), Box::new(MinFn::new()));
        funcs.insert("max".to_owned(), Box::new(MaxFn::new()));
        funcs.insert("max_by".to_owned(), Box::new(MaxByFn::new()));
        funcs.insert("min_by".to_owned(), Box::new(MinByFn::new()));
        funcs.insert("merge".to_owned(), Box::new(MergeFn::new()));
        funcs.insert("not_null".to_owned(), Box::new(NotNullFn::new()));
        funcs.insert("reverse".to_owned(), Box::new(ReverseFn::new()));
        funcs.insert("sort".to_owned(), Box::new(SortFn::new()));
        funcs.insert("sort_by".to_owned(), Box::new(SortByFn::new()));
        funcs.insert("starts_with".to_owned(), Box::new(StartsWithFn::new()));
        funcs.insert("sum".to_owned(), Box::new(SumFn::new()));
        funcs.insert("to_array".to_owned(), Box::new(ToArrayFn::new()));
        funcs.insert("to_number".to_owned(), Box::new(ToNumberFn::new()));
        funcs.insert("to_string".to_owned(), Box::new(ToStringFn::new()));
        funcs.insert("type".to_owned(), Box::new(TypeFn::new()));
        funcs.insert("values".to_owned(), Box::new(ValuesFn::new()));
        BuiltinFnRegistry {
            functions: funcs,
        }
    }
}

impl FnRegistry for BuiltinFnRegistry {
    fn get_signature(&self, name: &str) -> Option<&Signature> {
        self.functions.get(name).map(|f| f.signature())
    }

    fn evaluate(&self, name: &str, args: &[RcVar], ctx: &mut Context) -> Option<SearchResult> {
        self.functions.get(name)
            .map(|f| {
                try!(f.signature().validate(ctx, args));
                f.evaluate(args, ctx)
            })
    }
}

/* ------------------------------------------
 * Custom functions.
 * ------------------------------------------ */

/// Custom function that allows the creation of runtime functions.
pub struct CustomFunction {
    fn_signature: Signature,
    f: Box<(Fn(&[RcVar], &mut Context) -> SearchResult) + Sync>,
}

impl CustomFunction {
    /// Creates a new custom function.
    pub fn new(fn_signature: Signature,
               f: Box<(Fn(&[RcVar], &mut Context) -> SearchResult) + Sync>)
               -> CustomFunction {
        CustomFunction {
            fn_signature: fn_signature,
            f: f,
        }
    }
}

impl Function for CustomFunction {
    fn signature(&self) -> &Signature {
        &self.fn_signature
    }

    fn evaluate(&self, args: &[RcVar], ctx: &mut Context) -> SearchResult {
        (self.f)(args, ctx)
    }
}

/// Allows the use of custom functions in addition to existing
/// JMESPath functions.
pub struct CustomFnRegistry {
    functions: HashMap<String, Box<Function>>,
}

impl CustomFnRegistry {
    /// Creates a new CustomFnRegistry.
    pub fn new() -> CustomFnRegistry {
        CustomFnRegistry {
            functions: HashMap::new(),
        }
    }

    /// Adds a new custom function to the registry.
    pub fn register_function(&mut self, name: &str, f: Box<Function>) {
        self.functions.insert(name.to_owned(), f);
    }

    /// Deregisters a function by name and returns it if found.
    pub fn deregister_function(&mut self, name: &str) -> Option<Box<Function>> {
        self.functions.remove(name)
    }
}

impl FnRegistry for CustomFnRegistry {
    fn get_signature(&self, name: &str) -> Option<&Signature> {
        self.functions.get(name).map(|f| f.signature())
    }

    fn evaluate(&self, name: &str, args: &[RcVar], ctx: &mut Context) -> Option<SearchResult> {
        self.functions.get(name)
            .map(|f| {
                try!(f.signature().validate(ctx, args));
                f.evaluate(args, ctx)
            })
    }
}

/* ------------------------------------------
 * Function and signature types
 * ------------------------------------------ */

/// Represents a function's signature.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Signature {
    pub inputs: Vec<ArgumentType>,
    pub variadic: Option<ArgumentType>,
    pub output: ArgumentType,
}

impl Signature {
    /// Creates a new Signature struct.
    pub fn new(inputs: Vec<ArgumentType>,
               variadic: Option<ArgumentType>,
               output: ArgumentType)
               -> Signature {
        Signature {
            inputs: inputs,
            variadic: variadic,
            output: output,
        }
    }

    /// Validates the arity of a function. If the arity is invalid, a runtime
    /// error is returned with the relative position of the error and the
    /// expression that was being executed.
    pub fn validate_arity(&self, ctx: &Context, actual: usize) -> Result<(), Error> {
        let expected = self.inputs.len();
        if self.variadic.is_some() {
            if actual >= expected {
                Ok(())
            } else {
                Err(Error::from_ctx(ctx, ErrorReason::Runtime(RuntimeError::NotEnoughArguments {
                    expected: expected,
                    actual: actual
                })))
            }
        } else if actual == expected {
            Ok(())
        } else if actual < expected {
            Err(Error::from_ctx(ctx, ErrorReason::Runtime(RuntimeError::NotEnoughArguments {
                expected: expected,
                actual: actual,
            })))
        } else {
            Err(Error::from_ctx(ctx, ErrorReason::Runtime(RuntimeError::TooManyArguments {
                expected: expected,
                actual: actual,
            })))
        }
    }

    /// Validates the provided function arguments against the signature.
    pub fn validate(&self, ctx: &Context, args: &[RcVar]) -> Result<(), Error> {
        try!(self.validate_arity(ctx, args.len()));
        if let Some(ref variadic) = self.variadic {
            for (k, v) in args.iter().enumerate() {
                let validator = self.inputs.get(k).unwrap_or(variadic);
                try!(self.validate_arg(ctx, k, v, validator));
            }
        } else {
            for (k, v) in args.iter().enumerate() {
                try!(self.validate_arg(ctx, k, v, &self.inputs[k]));
            }
        }
        Ok(())
    }

    fn validate_arg(&self,
                    ctx: &Context,
                    position: usize,
                    value: &RcVar,
                    validator: &ArgumentType)
                    -> Result<(), Error> {
        if validator.is_valid(value) {
            Ok(())
        } else {
            Err(Error::from_ctx(ctx, ErrorReason::Runtime(RuntimeError::InvalidType {
                expected: validator.to_string(),
                actual: value.get_type().to_owned(),
                actual_value: value.clone(),
                position: position
            })))
        }
    }
}

/// Represents a JMESPath function.
pub trait Function: Sync {
    /// Gets the signature of the function.
    fn signature(&self) -> &Signature;

    /// Evaluates the function against an in-memory variable.
    fn evaluate(&self, args: &[RcVar], ctx: &mut Context) -> SearchResult;
}

/* ------------------------------------------
 * Function definitions
 * ------------------------------------------ */

/// Macro to more easily and quickly define a function and signature.
macro_rules! defn {
    ($name:ident, $args:expr, $variadic:expr, $retval:expr) => {
        struct $name {
            fn_signature: Signature,
        }

        impl $name {
            pub fn new() -> $name {
                $name {
                    fn_signature: Signature::new($args, $variadic, $retval),
                }
            }
        }
    };
}

/// Macro used to implement max_by and min_by functions.
macro_rules! min_and_max_by {
    ($ctx:expr, $operator:ident, $args:expr) => (
        {
            let vals = $args[0].as_array().unwrap();
            // Return null when there are not values in the array
            if vals.is_empty() {
                return Ok(Rc::new(Variable::Null));
            }
            let ast = $args[1].as_expref().unwrap();
            // Map over the first value to get the homogeneous required return type
            let initial = try!(interpret(&vals[0], &ast, $ctx));
            let entered_type = initial.get_type();
            if entered_type != "string" && entered_type != "number" {
                return Err(Error::from_ctx($ctx,
                    ErrorReason::Runtime(RuntimeError::InvalidReturnType {
                        expected: "expression->number|expression->string".to_owned(),
                        actual: entered_type.to_owned(),
                        actual_value: initial.clone(),
                        position: 1,
                        invocation: 1
                    }
                )));
            }
            // Map over each value, finding the best candidate value and fail on error.
            let mut candidate = (vals[0].clone(), initial.clone());
            for (invocation, v) in vals.iter().enumerate().skip(1) {
                let mapped = try!(interpret(v, &ast, $ctx));
                if mapped.get_type() != entered_type {
                    return Err(Error::from_ctx($ctx,
                        ErrorReason::Runtime(RuntimeError::InvalidReturnType {
                            expected: format!("expression->{}", entered_type),
                            actual: mapped.get_type().to_owned(),
                            actual_value: mapped.clone(),
                            position: 1,
                            invocation: invocation
                        }
                    )));
                }
                if mapped.$operator(&candidate.1) {
                    candidate = (v.clone(), mapped);
                }
            }
            Ok(candidate.0)
        }
    )
}

/// Macro used to implement max and min functions.
macro_rules! min_and_max {
    ($operator:ident, $args:expr) => (
        {
            let values = $args[0].as_array().unwrap();
            if values.is_empty() {
                Ok(Rc::new(Variable::Null))
            } else {
                let result: RcVar = values
                    .iter()
                    .skip(1)
                    .fold(values[0].clone(), |acc, item| $operator(acc, item.clone()));
                Ok(result)
            }
        }
    )
}

defn!(AbsFn, vec![arg!(number)], None, arg!(number));

impl Function for AbsFn {
    fn signature(&self) -> &Signature {
        &self.fn_signature
    }

    fn evaluate(&self, args: &[RcVar], _: &mut Context) -> SearchResult {
        match *args[0] {
            Variable::I64(n) => Ok(Rc::new(Variable::I64(n.abs()))),
            Variable::F64(f) => Ok(Rc::new(Variable::F64(f.abs()))),
            _ => Ok(args[0].clone())
        }
    }
}

defn!(AvgFn, vec![arg!(array_number)], None, arg!(number));

impl Function for AvgFn {
    fn signature(&self) -> &Signature {
        &self.fn_signature
    }

    fn evaluate(&self, args: &[RcVar], _: &mut Context) -> SearchResult {
        let values = args[0].as_array().unwrap();
        let sum = values.iter()
            .map(|n| n.as_f64().unwrap())
            .fold(0f64, |a, ref b| a + b);
        Ok(Rc::new(Variable::F64(sum / (values.len() as f64))))
    }
}

defn!(CeilFn, vec![arg!(number)], None, arg!(number));

impl Function for CeilFn {
    fn signature(&self) -> &Signature {
        &self.fn_signature
    }

    fn evaluate(&self, args: &[RcVar], _: &mut Context) -> SearchResult {
        let n = args[0].as_f64().unwrap();
        Ok(Rc::new(Variable::F64(n.ceil())))
    }
}

defn!(ContainsFn, vec![arg!(string | array), arg!(any)], None, arg!(bool));

impl Function for ContainsFn {
    fn signature(&self) -> &Signature {
        &self.fn_signature
    }

    fn evaluate(&self, args: &[RcVar], _: &mut Context) -> SearchResult {
        let haystack = &args[0];
        let needle = &args[1];
        match **haystack {
           Variable::Array(ref a) => {
               Ok(Rc::new(Variable::Bool(a.contains(&needle))))
           },
           Variable::String(ref subj) => {
               match needle.as_string() {
                   None => Ok(Rc::new(Variable::Bool(false))),
                   Some(s) => Ok(Rc::new(Variable::Bool(subj.contains(s))))
               }
           },
           _ => unreachable!()
        }
    }
}

defn!(EndsWithFn, vec![arg!(string), arg!(string)], None, arg!(bool));

impl Function for EndsWithFn {
    fn signature(&self) -> &Signature {
        &self.fn_signature
    }

    fn evaluate(&self, args: &[RcVar], _: &mut Context) -> SearchResult {
        let subject = args[0].as_string().unwrap();
        let search = args[1].as_string().unwrap();
        Ok(Rc::new(Variable::Bool(subject.ends_with(search))))
    }
}

defn!(FloorFn, vec![arg!(number)], None, arg!(number));

impl Function for FloorFn {
    fn signature(&self) -> &Signature {
        &self.fn_signature
    }

    fn evaluate(&self, args: &[RcVar], _: &mut Context) -> SearchResult {
        let n = args[0].as_f64().unwrap();
        Ok(Rc::new(Variable::F64(n.floor())))
    }
}

defn!(JoinFn, vec![arg!(string), arg!(array_string)], None, arg!(string));

impl Function for JoinFn {
    fn signature(&self) -> &Signature {
        &self.fn_signature
    }

    fn evaluate(&self, args: &[RcVar], _: &mut Context) -> SearchResult {
        let glue = args[0].as_string().unwrap();
        let values = args[1].as_array().unwrap();
        let result = values.iter()
            .map(|v| v.as_string().unwrap())
            .cloned()
            .collect::<Vec<String>>()
            .join(&glue);
        Ok(Rc::new(Variable::String(result)))
    }
}

defn!(KeysFn, vec![arg!(object)], None, arg!(array));

impl Function for KeysFn {
    fn signature(&self) -> &Signature {
        &self.fn_signature
    }

    fn evaluate(&self, args: &[RcVar], _: &mut Context) -> SearchResult {
        let object = args[0].as_object().unwrap();
        let keys = object.keys()
            .map(|k| Rc::new(Variable::String((*k).clone())))
            .collect::<Vec<RcVar>>();
        Ok(Rc::new(Variable::Array(keys)))
    }
}

defn!(LengthFn, vec![arg!(array | object | string)], None, arg!(number));

impl Function for LengthFn {
    fn signature(&self) -> &Signature {
        &self.fn_signature
    }

    fn evaluate(&self, args: &[RcVar], _: &mut Context) -> SearchResult {
        match *args[0] {
            Variable::Array(ref a) => Ok(Rc::new(Variable::U64(a.len() as u64))),
            Variable::Object(ref m) => Ok(Rc::new(Variable::U64(m.len() as u64))),
            // Note that we need to count the code points not the number of unicode characters
            Variable::String(ref s) => Ok(Rc::new(Variable::U64(s.chars().count() as u64))),
            _ => unreachable!()
        }
    }
}

defn!(MapFn, vec![arg!(expref), arg!(array)], None, arg!(array));

impl Function for MapFn {
    fn signature(&self) -> &Signature {
        &self.fn_signature
    }

    fn evaluate(&self, args: &[RcVar], ctx: &mut Context) -> SearchResult {
        let ast = args[0].as_expref().unwrap();
        let values = args[1].as_array().unwrap();
        let mut results = vec![];
        for value in values {
            results.push(try!(interpret(&value, &ast, ctx)));
        }
        Ok(Rc::new(Variable::Array(results)))
    }
}

defn!(MaxFn, vec![arg!(array_string | array_number)], None, arg!(string | number));

impl Function for MaxFn {
    fn signature(&self) -> &Signature {
        &self.fn_signature
    }

    fn evaluate(&self, args: &[RcVar], _: &mut Context) -> SearchResult {
        min_and_max!(max, args)
    }
}

defn!(MinFn, vec![arg!(array_string | array_number)], None, arg!(string | number));

impl Function for MinFn {
    fn signature(&self) -> &Signature {
        &self.fn_signature
    }

    fn evaluate(&self, args: &[RcVar], _: &mut Context) -> SearchResult {
        min_and_max!(min, args)
    }
}

defn!(MaxByFn, vec![arg!(array), arg!(expref)], None, arg!(string | number));

impl Function for MaxByFn {
    fn signature(&self) -> &Signature {
        &self.fn_signature
    }

    fn evaluate(&self, args: &[RcVar], ctx: &mut Context) -> SearchResult {
        min_and_max_by!(ctx, gt, args)
    }
}

defn!(MinByFn, vec![arg!(array), arg!(expref)], None, arg!(string | number));

impl Function for MinByFn {
    fn signature(&self) -> &Signature {
        &self.fn_signature
    }

    fn evaluate(&self, args: &[RcVar], ctx: &mut Context) -> SearchResult {
        min_and_max_by!(ctx, lt, args)
    }
}

defn!(MergeFn, vec![arg!(object)], Some(arg!(object)), arg!(object));

impl Function for MergeFn {
    fn signature(&self) -> &Signature {
        &self.fn_signature
    }

    fn evaluate(&self, args: &[RcVar], _: &mut Context) -> SearchResult {
        let mut result = BTreeMap::new();
        for arg in args {
            result.extend(arg.as_object().unwrap().clone());
        }
        Ok(Rc::new(Variable::Object(result)))
    }
}

defn!(NotNullFn, vec![arg!(any)], Some(arg!(any)), arg!(any));

impl Function for NotNullFn {
    fn signature(&self) -> &Signature {
        &self.fn_signature
    }

    fn evaluate(&self, args: &[RcVar], _: &mut Context) -> SearchResult {
        for arg in args {
            if !arg.is_null() {
                return Ok(arg.clone());
            }
        }
        Ok(Rc::new(Variable::Null))
    }
}

defn!(ReverseFn, vec![arg!(array | string)], None, arg!(array | string));

impl Function for ReverseFn {
    fn signature(&self) -> &Signature {
        &self.fn_signature
    }

    fn evaluate(&self, args: &[RcVar], _: &mut Context) -> SearchResult {
        if args[0].is_array() {
            let mut values = args[0].as_array().unwrap().clone();
            values.reverse();
            Ok(Rc::new(Variable::Array(values)))
        } else {
            let word: String = args[0].as_string().unwrap().chars().rev().collect();
            Ok(Rc::new(Variable::String(word)))
        }
    }
}

defn!(SortFn, vec![arg!(array_string | array_number)], None, arg!(array));

impl Function for SortFn {
    fn signature(&self) -> &Signature {
        &self.fn_signature
    }

    fn evaluate(&self, args: &[RcVar], _: &mut Context) -> SearchResult {
        let mut values = args[0].as_array().unwrap().clone();
        values.sort();
        Ok(Rc::new(Variable::Array(values)))
    }
}

defn!(SortByFn, vec![arg!(array), arg!(expref)], None, arg!(array));

impl Function for SortByFn {
    fn signature(&self) -> &Signature {
        &self.fn_signature
    }

    fn evaluate(&self, args: &[RcVar], ctx: &mut Context) -> SearchResult {
        let vals = args[0].as_array().unwrap().clone();
        if vals.is_empty() {
            return Ok(Rc::new(Variable::Array(vals)));
        }
        let ast = args[1].as_expref().unwrap();
        let mut mapped: Vec<(RcVar, RcVar)> = vec![];
        let first_value = try!(interpret(&vals[0], &ast, ctx));
        let first_type = first_value.get_type();
        if first_type != "string" && first_type != "number" {
            return Err(Error::from_ctx(ctx, ErrorReason::Runtime(RuntimeError::InvalidReturnType {
                expected: "expression->string|expression->number".to_owned(),
                actual: first_type.to_owned(),
                actual_value: first_value.clone(),
                position: 1,
                invocation: 1
            })));
        }
        mapped.push((vals[0].clone(), first_value.clone()));
        for (invocation, v) in vals.iter().enumerate().skip(1) {
            let mapped_value = try!(interpret(v, &ast, ctx));
            if mapped_value.get_type() != first_type {
                return Err(Error::from_ctx(ctx,
                    ErrorReason::Runtime(RuntimeError::InvalidReturnType {
                        expected: format!("expression->{}", first_type),
                        actual: mapped_value.get_type().to_owned(),
                        actual_value: mapped_value.clone(),
                        position: 1,
                        invocation: invocation
                    }
                )));
            }
            mapped.push((v.clone(), mapped_value));
        }
        mapped.sort_by(|a, b| a.1.cmp(&b.1));
        Ok(Rc::new(Variable::Array(vals)))
    }
}

defn!(StartsWithFn, vec![arg!(string), arg!(string)], None, arg!(bool));

impl Function for StartsWithFn {
    fn signature(&self) -> &Signature {
        &self.fn_signature
    }

    fn evaluate(&self, args: &[RcVar], _: &mut Context) -> SearchResult {
        let subject = args[0].as_string().unwrap();
        let search = args[1].as_string().unwrap();
        Ok(Rc::new(Variable::Bool(subject.starts_with(search))))
    }
}

defn!(SumFn, vec![arg!(array_number)], None, arg!(number));

impl Function for SumFn {
    fn signature(&self) -> &Signature {
        &self.fn_signature
    }

    fn evaluate(&self, args: &[RcVar], _: &mut Context) -> SearchResult {
        let result = args[0].as_array().unwrap().iter().fold(
            0.0, |acc, item| acc + item.as_f64().unwrap());
        Ok(Rc::new(Variable::F64(result)))
    }
}

defn!(ToArrayFn, vec![arg!(any)], None, arg!(array));

impl Function for ToArrayFn {
    fn signature(&self) -> &Signature {
        &self.fn_signature
    }

    fn evaluate(&self, args: &[RcVar], _: &mut Context) -> SearchResult {
        match *args[0] {
            Variable::Array(_) => Ok(args[0].clone()),
            _ => Ok(Rc::new(Variable::Array(vec![args[0].clone()])))
        }
    }
}

defn!(ToNumberFn, vec![arg!(any)], None, arg!(number));

impl Function for ToNumberFn {
    fn signature(&self) -> &Signature {
        &self.fn_signature
    }

    fn evaluate(&self, args: &[RcVar], _: &mut Context) -> SearchResult {
        match *args[0] {
            Variable::I64(_) | Variable::F64(_) | Variable::U64(_) => Ok(args[0].clone()),
            Variable::String(ref s) => {
                match Variable::from_json(s) {
                    Ok(f)  => Ok(Rc::new(f)),
                    Err(_) => Ok(Rc::new(Variable::Null))
                }
            },
            _ => Ok(Rc::new(Variable::Null))
        }
    }
}

defn!(ToStringFn, vec![arg!(object | array | bool | number | string | null)], None, arg!(string));

impl Function for ToStringFn {
    fn signature(&self) -> &Signature {
        &self.fn_signature
    }

    fn evaluate(&self, args: &[RcVar], _: &mut Context) -> SearchResult {
        match *args[0] {
            Variable::String(_) => Ok(args[0].clone()),
            _ => Ok(Rc::new(Variable::String(args[0].to_string())))
        }
    }
}

defn!(TypeFn, vec![arg!(any)], None, arg!(string));

impl Function for TypeFn {
    fn signature(&self) -> &Signature {
        &self.fn_signature
    }

    fn evaluate(&self, args: &[RcVar], _: &mut Context) -> SearchResult {
        Ok(Rc::new(Variable::String(args[0].get_type().to_owned())))
    }
}

defn!(ValuesFn, vec![arg!(object)], None, arg!(array));

impl Function for ValuesFn {
    fn signature(&self) -> &Signature {
        &self.fn_signature
    }

    fn evaluate(&self, args: &[RcVar], _: &mut Context) -> SearchResult {
        let map = args[0].as_object().unwrap();
        Ok(Rc::new(Variable::Array(map.values().cloned().collect::<Vec<RcVar>>())))
    }
}
