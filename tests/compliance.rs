extern crate jmespath;

use std::fs::{self, File};
use std::io::Read;

use jmespath::RcVar;
use jmespath::RuntimeError;
use jmespath::Expression;

/// Test case assertions.
enum Assertion {
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
    /// Ensures that the expression is parsed and returns an expected result.
    ValidResult(RcVar)
}

impl Assertion {
    /// Runs the assertion of a test case
    fn assert(&self, suite: &TestSuite, case: &TestCase) -> Result<(), String> {
        match self {
            &Assertion::InvalidArity => {
                match try!(self.try_parse(suite, case)).search(suite.given.clone()) {
                    Err(RuntimeError::NotEnoughArguments{..}) => Ok(()),
                    Err(RuntimeError::TooManyArguments{..}) => Ok(()),
                    Err(e) => Err(self.err_message(suite, case, format!("{}", e))),
                    Ok(r) => Err(self.err_message(suite, case, r.to_string().unwrap())),
                }
            },
            &Assertion::InvalidType => {
                match try!(self.try_parse(suite, case)).search(suite.given.clone()) {
                    Err(RuntimeError::InvalidType{..}) => Ok(()),
                    Err(RuntimeError::InvalidReturnType{..}) => Ok(()),
                    Err(e) => Err(self.err_message(suite, case, format!("{}", e))),
                    Ok(r) => Err(self.err_message(suite, case, r.to_string().unwrap())),
                }
            },
            &Assertion::InvalidSlice => {
                match try!(self.try_parse(suite, case)).search(suite.given.clone()) {
                    Err(RuntimeError::InvalidSlice) => Ok(()),
                    Err(e) => Err(self.err_message(suite, case, format!("{}", e))),
                    Ok(r) => Err(self.err_message(suite, case, r.to_string().unwrap())),
                }
            },
            &Assertion::UnknownFunction => {
                match try!(self.try_parse(suite, case)).search(suite.given.clone()) {
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
            &Assertion::ValidResult(ref expected_result) => {
                match try!(self.try_parse(suite, case)).search(suite.given.clone()) {
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
    fn try_parse<'a>(&self,
                     suite: &TestSuite,
                     case: &'a TestCase)
                     -> Result<Expression<'a>, String> {
        match Expression::new(&case.expression) {
            Err(e) => Err(self.err_message(suite, case, format!("{}", e))),
            Ok(expr) => Ok(expr)
        }
    }

    /// Formats an error message for a test case failure.
    fn err_message(&self, suite: &TestSuite, case: &TestCase, message: String) -> String {
        format!("Test suite: {}\nExpression: {}\nExpected: {}\nResult: {}\n==============",
                 suite.filename, case.expression, case.expected_result, message).to_string()
    }
}

struct TestSuite {
    /// Filename of the test suite
    filename: String,
    /// Given data of the test suite
    given: RcVar,
    /// Collection of test cases to perform
    cases: Vec<TestCase>,
}

impl TestSuite {
    /// Creates a test suite from parsed JSON data.
    fn from_variable(filename: String, suite: &RcVar) -> TestSuite {
        TestSuite {
            filename: filename,
            given: suite.get_value("given").unwrap(),
            cases: suite.get_value("cases").unwrap()
                .as_array()
                .unwrap()
                .iter()
                .map(|v| TestCase::from_variable(v))
                .collect::<Vec<TestCase>>()
        }
    }
}

struct TestCase {
    /// The expression being evaluated
    expression: String,
    /// The human-readable expected result of the test-case
    expected_result: String,
    /// The assertion to perform for the test case
    assertion: Assertion,
}

impl TestCase {
    /// Creates a test case from parsed JSON data.
    fn from_variable(case: &RcVar) -> TestCase {
        TestCase {
            expression: case.get_value("expression").unwrap().as_string().unwrap().clone(),
            expected_result: match case.get_value("error") {
                None => case.get_value("result").unwrap().to_string().unwrap(),
                Some(err) => err.as_string().unwrap().clone()
            },
            assertion: match case.get_value("error") {
                None => Assertion::ValidResult(case.get_value("result").unwrap()),
                Some(err) => {
                    match err.as_string().unwrap().as_ref() {
                        "syntax" => Assertion::SyntaxError,
                        "invalid-type" => Assertion::InvalidType,
                        "invalid-value" => Assertion::InvalidSlice,
                        "invalid-arity" => Assertion::InvalidArity,
                        "unknown-function" => Assertion::UnknownFunction,
                        v @ _ => panic!("Unknown error type: {}", v),
                    }
                }
            }
        }
    }
}

fn load_test_suites() -> Vec<TestSuite> {
    let mut result = vec![];
    let files = fs::read_dir("tests/compliance/").unwrap();
    for filename in files {
        let path = filename.unwrap().path();
        let file_path = path.to_str().unwrap().to_string();
        let mut f = File::open(path).unwrap();
        let mut file_data = String::new();
        f.read_to_string(&mut file_data).unwrap();
        let data = jmespath::Variable::from_str(&file_data).unwrap();
        let suites = data.as_array().unwrap();
        for suite in suites {
            result.push(TestSuite::from_variable(file_path.clone(), suite));
        }
    }
    result
}

#[test]
fn run_compliance() {
    let mut failures = 0;
    let suites = load_test_suites();
    for suite in suites.iter() {
        for case in suite.cases.iter() {
            if let Err(e) = case.assertion.assert(suite, case) {
                println!("{}\n", e);
                failures += 1;
            }
        }
    }
    if failures > 0 {
        panic!("{} compliance tests failed", failures);
    }
}
