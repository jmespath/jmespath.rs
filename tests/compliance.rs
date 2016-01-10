//! JMESPath compliance tests.
//!
//! Test cases are generated using build.rs. This may eventually be exposed
//! as a library (leading to possibilities like a compliance test runner CLI).

extern crate serde_json;
extern crate jmespath;

use std::fmt;
use std::rc::Rc;

use serde_json::Value;

use jmespath::{Variable, RcVar, RuntimeError, Expression};

/// Avaliable benchmark types.
#[derive(Debug)]
pub enum BenchType {
    /// The benchmark must only parse an expression.
    Parse,
    /// The benchmark must parse and evaluate an expression.
    Full
}

/// Test case assertions.
pub enum Assertion {
    /// Ensures that the expression fails due to an invalid-arity error.
    InvalidArity,
    /// Ensures that the expression fails due to an invalid-type error.
    InvalidType,
    /// Ensures that the expression fails due to an invalid-value error.
    InvalidSlice,
    /// Ensures that the expression fails due to an unknown-function error.
    UnknownFunction,
    /// Ensures that an expression cannot be parsed due to a syntax error.
    SyntaxError,
    /// Ignores the result and marks the test as a benchmark
    Bench(BenchType),
    /// Ensures that the expression is parsed and returns an expected result.
    ValidResult(RcVar)
}

impl Assertion {
    /// Runs the assertion of a test case
    pub fn assert(&self,
                  suite: &str,
                  case: &TestCase,
                  given: RcVar) -> Result<(), String> {
        match self {
            &Assertion::InvalidArity => {
                match try!(self.try_parse(suite, case)).search(given.clone()) {
                    Err(RuntimeError::NotEnoughArguments{..}) => Ok(()),
                    Err(RuntimeError::TooManyArguments{..}) => Ok(()),
                    Err(e) => Err(self.err_message(suite, case, format!("{}", e))),
                    Ok(r) => Err(self.err_message(suite, case, r.to_string().unwrap())),
                }
            },
            &Assertion::InvalidType => {
                match try!(self.try_parse(suite, case)).search(given.clone()) {
                    Err(RuntimeError::InvalidType{..}) => Ok(()),
                    Err(RuntimeError::InvalidReturnType{..}) => Ok(()),
                    Err(e) => Err(self.err_message(suite, case, format!("{}", e))),
                    Ok(r) => Err(self.err_message(suite, case, r.to_string().unwrap())),
                }
            },
            &Assertion::InvalidSlice => {
                match try!(self.try_parse(suite, case)).search(given.clone()) {
                    Err(RuntimeError::InvalidSlice) => Ok(()),
                    Err(e) => Err(self.err_message(suite, case, format!("{}", e))),
                    Ok(r) => Err(self.err_message(suite, case, r.to_string().unwrap())),
                }
            },
            &Assertion::UnknownFunction => {
                match try!(self.try_parse(suite, case)).search(given) {
                    Err(RuntimeError::UnknownFunction{..}) => Ok(()),
                    Err(e) => Err(self.err_message(suite, case, format!("{}", e))),
                    Ok(r) => Err(self.err_message(suite, case, r.to_string().unwrap())),
                }
            },
            &Assertion::SyntaxError => {
                match Expression::new(&case.expression) {
                    Err(_) => Ok(()),
                    Ok(expr) => Err(self.err_message(suite, case, format!("Parsed {:?}", expr)))
                }
            },
            &Assertion::Bench(_) => Ok(()),
            &Assertion::ValidResult(ref expected_result) => {
                match try!(self.try_parse(suite, case)).search(given) {
                    Err(e) => Err(self.err_message(suite, case, format!("{}", e))),
                    Ok(r) => {
                        match r.as_string() {
                            Some(s) if s != expected_result.as_string().unwrap() => {
                                Err(self.err_message(suite, case, r.to_string().unwrap()))
                            },
                            Some(_) if r != expected_result.clone() => {
                                Err(self.err_message(suite, case, r.to_string().unwrap()))
                            },
                            _ => Ok(())
                        }
                    }
                }
            }
        }
    }

    /// Attempts to parse an expression for a case, returning the expression or an error string.
    fn try_parse<'a>(&self, suite: &str, case: &'a TestCase) -> Result<Expression<'a>, String> {
        match Expression::new(&case.expression) {
            Err(e) => Err(self.err_message(suite, case, format!("{}", e))),
            Ok(expr) => Ok(expr)
        }
    }

    /// Formats an error message for a test case failure.
    fn err_message(&self, suite: &str, case: &TestCase, message: String) -> String {
        format!("Test suite: {}\nExpression: {}\nAssertion: {}\nResult: {}\n==============",
                 suite, case.expression, self, message).to_string()
    }

    /// Try to create a benchmark assertion from a JSON value.
    fn bench_from_json(bench_type: &Value) -> Result<Self, TestCaseError> {
        bench_type.as_string()
            .ok_or(TestCaseError::BenchIsNotString)
            .and_then(|b| {
                match b {
                    "parse" => Ok(Assertion::Bench(BenchType::Parse)),
                    "full" => Ok(Assertion::Bench(BenchType::Full)),
                    s @ _ => Err(TestCaseError::UnknownBenchType(s.to_string()))
                }
            })
    }

    /// Try to create an error assertion from a JSON value.
    fn error_from_json(error_type: &Value) -> Result<Self, TestCaseError> {
        error_type.as_string()
            .ok_or(TestCaseError::ErrorIsNotString)
            .and_then(|b| {
                match b {
                    "syntax" => Ok(Assertion::SyntaxError),
                    "invalid-type" => Ok(Assertion::InvalidType),
                    "invalid-value" => Ok(Assertion::InvalidSlice),
                    "invalid-arity" => Ok(Assertion::InvalidArity),
                    "unknown-function" => Ok(Assertion::UnknownFunction),
                    e @ _ => Err(TestCaseError::UnknownErrorType(e.to_string())),
                }
            })
    }
}

impl fmt::Display for Assertion {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        use self::Assertion::*;
        match self {
            &InvalidArity => write!(fmt, "expects error(invalid-arity)"),
            &InvalidType => write!(fmt, "expects error(invalid-type)"),
            &InvalidSlice => write!(fmt, "expects error(invalid-value)"),
            &UnknownFunction => write!(fmt, "expects error(unknown-function)"),
            &SyntaxError => write!(fmt, "expects error(syntax)"),
            &Bench(ref b) => write!(fmt, "expects benchmark({:?})", b),
            &ValidResult(ref r) => write!(fmt, "expects result({:?})", r),
        }
    }
}

/// The test suite holds a collection of test cases and has a given value.
#[allow(dead_code)]
pub struct TestSuite<'a> {
    /// Filename of the test suite
    filename: &'a str,
    /// Given data of the test suite
    given: RcVar,
    /// Collection of test cases to perform
    cases: Vec<TestCase>,
}

impl<'a> TestSuite<'a> {
    /// Creates a test suite from JSON string.
    pub fn from_str(filename: &'a str, suite: &str) -> Result<TestSuite<'a>, String> {
        serde_json::from_str::<Value>(suite)
            .map_err(|e| e.to_string())
            .and_then(|j| TestSuite::from_json(filename, &j))
    }

    /// Creates a test suite from parsed JSON data.
    fn from_json(filename: &'a str, suite: &Value) -> Result<TestSuite<'a>, String> {
        let suite = try!(suite.as_object().ok_or("test suite is not an object"));
        let test_case = try!(suite.get("cases").ok_or("No cases value".to_string()));
        let case_array = try!(test_case.as_array().ok_or("cases is not an array".to_string()));
        let mut cases = vec![];
        for case in case_array {
            cases.push(try!(TestCase::from_json(case).map_err(|e| e.to_string())));
        }

        Ok(TestSuite {
            filename: filename,
            given: Rc::new(Variable::from_json(try!(
                suite.get("given").ok_or("No given value".to_string())))),
            cases: cases
        })
    }
}

/// Errors that can occur when creating a TestCase
pub enum TestCaseError {
    InvalidJSON(String),
    NoCaseType,
    NoResult,
    ResultCannotToString,
    NoExpression,
    ExpressionIsNotString,
    ErrorIsNotString,
    UnknownErrorType(String),
    UnknownBenchType(String),
    BenchIsNotString,
}

impl fmt::Display for TestCaseError {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        use self::TestCaseError::*;
        match self {
            &InvalidJSON(ref msg) => write!(fmt, "invalid test case JSON: {}", msg),
            &NoCaseType => write!(fmt, "case has no result, error, or bench"),
            &NoResult => write!(fmt, "test case has no result key"),
            &ResultCannotToString => write!(fmt, "result could not be cast to string"),
            &NoExpression => write!(fmt, "test case has no expression key"),
            &ExpressionIsNotString => write!(fmt, "test case expression is not a string"),
            &ErrorIsNotString => write!(fmt, "test case error value is not a string"),
            &UnknownErrorType(ref t) => write!(fmt, "unknown error type: {}", t),
            &BenchIsNotString => write!(fmt, "bench value is not a string"),
            &UnknownBenchType(ref bench) => {
                write!(fmt, "unknown bench value: {}, expected one of of parse|full", bench)
            },
        }
    }
}

impl fmt::Debug for TestCaseError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self)
    }
}

/// Represents a test case that contains an expression and assertion.
pub struct TestCase {
    /// The expression being evaluated.
    pub expression: String,
    /// The assertion to perform for the test case.
    pub assertion: Assertion,
}

impl TestCase {
    /// Creates a test case from a JSON encoded string.
    pub fn from_str(case: &str) -> Result<TestCase, TestCaseError> {
        serde_json::from_str::<Value>(case)
            .map_err(|e| TestCaseError::InvalidJSON(e.to_string()))
            .and_then(|json| TestCase::from_json(&json))
    }

    /// Creates a test case from parsed JSON data.
    fn from_json(case: &Value) -> Result<TestCase, TestCaseError> {
        use TestCaseError::*;
        let case = try!(case.as_object().ok_or(InvalidJSON("not an object".to_string())));
        Ok(TestCase {
            expression: try!(
                case.get("expression")
                    .ok_or(NoExpression)
                    .and_then(|expression| expression.as_string()
                        .ok_or(ExpressionIsNotString)
                        .map(|expression_str| expression_str.to_string()))),
            assertion: match case.get("error") {
                Some(err) => try!(Assertion::error_from_json(err)),
                None if case.contains_key("result") => {
                    let value = Rc::new(Variable::from_json(case.get("result").unwrap()));
                    Assertion::ValidResult(value)
                },
                None if case.contains_key("bench") => {
                    try!(Assertion::bench_from_json(case.get("bench").unwrap()))
                },
                _ => return Err(NoCaseType)
            }
        })
    }

    /// Perform the test case assertion against a given value.
    pub fn assert(&self, suite_filename: &str, given: RcVar) -> Result<(), String> {
        self.assertion.assert(suite_filename, self, given)
    }
}

include!(concat!(env!("OUT_DIR"), "/compliance_tests.rs"));
