extern crate jmespath;

use std::fs;
use std::fs::File;
use std::io::Read;
use std::rc::Rc;

use jmespath::RuntimeError;
use jmespath::{Expression, Variable};

type AssertionBox = Box<TestAssertion>;

/// Performs a test-case assertion.
trait TestAssertion {
    /// Runs the assertion of a test case
    fn assert(&self, suite: &TestSuite, case: &TestCase) -> Result<(), String>;

    /// Attempts to parse an expression for a case, returning the expression or an error string.
    fn try_parse(&self, suite: &TestSuite, case: &TestCase) -> Result<Expression, String> {
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
    filename: String,
    given: Rc<Variable>,
    cases: Vec<TestCase>,
}

impl TestSuite {
    /// Creates a test suite from parsed JSON data.
    fn from_variable(filename: String, suite: &Rc<Variable>) -> TestSuite {
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
    expression: String,
    expected_result: String,
    assertion: AssertionBox
}

impl TestCase {
    /// Creates a test case from parsed JSON data.
    fn from_variable(case: &Rc<Variable>) -> TestCase {
        TestCase {
            expression: case.get_value("expression").unwrap().as_string().unwrap().clone(),
            expected_result: match case.get_value("error") {
                None => case.get_value("result").unwrap().to_string().unwrap(),
                Some(err) => err.as_string().unwrap().clone()
            },
            assertion: match case.get_value("error") {
                None => Box::new(ValidResult {
                    expected_result: case.get_value("result").unwrap()
                }),
                Some(err) => {
                    match err.as_string().unwrap().as_ref() {
                        "syntax" => Box::new(SyntaxError),
                        "invalid-type" => Box::new(InvalidType),
                        "invalid-value" => Box::new(InvalidSlice),
                        "invalid-arity" => Box::new(InvalidArity),
                        "unknown-function" => Box::new(UnknownFunction),
                        v @ _ => panic!("Unknown error type: {}", v),
                    }
                }
            }
        }
    }
}

/// Ensures that the expression fails due to an invalid-arity error.
struct InvalidArity;

impl TestAssertion for InvalidArity {
    fn assert(&self, suite: &TestSuite, case: &TestCase) -> Result<(), String> {
        match try!(self.try_parse(suite, case)).search(suite.given.clone()) {
            Err(RuntimeError::NotEnoughArguments{..}) => Ok(()),
            Err(RuntimeError::TooManyArguments{..}) => Ok(()),
            Err(e) => Err(self.err_message(suite, case, format!("{}", e))),
            Ok(r) => Err(self.err_message(suite, case, r.to_string().unwrap())),
        }
    }
}

/// Ensures that the expression fails due to an invalid-type error.
struct InvalidType;

impl TestAssertion for InvalidType {
    fn assert(&self, suite: &TestSuite, case: &TestCase) -> Result<(), String> {
        match try!(self.try_parse(suite, case)).search(suite.given.clone()) {
            Err(RuntimeError::InvalidType{..}) => Ok(()),
            Err(RuntimeError::InvalidReturnType{..}) => Ok(()),
            Err(e) => Err(self.err_message(suite, case, format!("{}", e))),
            Ok(r) => Err(self.err_message(suite, case, r.to_string().unwrap())),
        }
    }
}

/// Ensures that the expression fails due to an invalid-value error.
struct InvalidSlice;

impl TestAssertion for InvalidSlice {
    fn assert(&self, suite: &TestSuite, case: &TestCase) -> Result<(), String> {
        match try!(self.try_parse(suite, case)).search(suite.given.clone()) {
            Err(RuntimeError::InvalidSlice) => Ok(()),
            Err(e) => Err(self.err_message(suite, case, format!("{}", e))),
            Ok(r) => Err(self.err_message(suite, case, r.to_string().unwrap())),
        }
    }
}

/// Ensures that the expression fails due to an unknown-function error.
struct UnknownFunction;

impl TestAssertion for UnknownFunction {
    fn assert(&self, suite: &TestSuite, case: &TestCase) -> Result<(), String> {
        match try!(self.try_parse(suite, case)).search(suite.given.clone()) {
            Err(RuntimeError::UnknownFunction{..}) => Ok(()),
            Err(e) => Err(self.err_message(suite, case, format!("{}", e))),
            Ok(r) => Err(self.err_message(suite, case, r.to_string().unwrap())),
        }
    }
}

/// Ensures taht an expression cannot be parsed due to a syntax error.
struct SyntaxError;

impl TestAssertion for SyntaxError {
    fn assert(&self, suite: &TestSuite, case: &TestCase) -> Result<(), String> {
        match Expression::new(&case.expression) {
            Err(_) => Ok(()),
            Ok(expr) => Err(self.err_message(suite, case, format!("Parsed {:?}", expr)))
        }
    }
}

/// Ensures that the expression is parsed and returns an expected result.
struct ValidResult {
    expected_result: Rc<Variable>
}

impl TestAssertion for ValidResult {
    fn assert(&self, suite: &TestSuite, case: &TestCase) -> Result<(), String> {
        match try!(self.try_parse(suite, case)).search(suite.given.clone()) {
            Err(e) => Err(self.err_message(suite, case, format!("{}", e))),
            Ok(r) => {
                if r != self.expected_result {
                    Err(self.err_message(suite, case, r.to_string().unwrap()))
                } else {
                    Ok(())
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
