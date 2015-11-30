extern crate jmespath;

use std::fs;
use std::fs::File;
use std::io::Read;

use jmespath::Expression;
use jmespath::parser::parse;

fn get_tests() -> Vec<jmespath::Variable> {
    let mut result = vec![];
    let files = fs::read_dir("tests/compliance/").unwrap();
    for filename in files {
        let mut f = File::open(filename.unwrap().path()).unwrap();
        let mut data = String::new();
        f.read_to_string(&mut data).unwrap();
        result.push(jmespath::Variable::from_str(&data).unwrap());
    }
    result
}

#[test]
fn run_compliance() {
    let mut passed = 0;
    let mut failures: Vec<(String, String, String)> = vec![];
    for test in get_tests() {
        for suite in test.as_array().unwrap() {
            let given_data = suite.get_value("given").unwrap();
            for case in suite.get_value("cases").unwrap().as_array().unwrap() {
                // println!("{}", case.get_value("expression").unwrap().as_string().unwrap());
                match case.get_value("result") {
                    Some(result) => {
                        let expr_str = case.get_value("expression")
                            .unwrap()
                            .as_string()
                            .unwrap()
                            .clone();
                        match Expression::new(&expr_str) {
                            Ok(expr) => {
                                let actual_result = expr.search(given_data.clone());
                                match actual_result {
                                    Ok(actual) => {
                                        if actual == result {
                                            passed += 1;
                                        } else {
                                            println!("{}:{:?}", expr_str, expr.ast);
                                            failures.push((format!("{}:{:?}", expr_str, expr.ast),
                                                           result.to_string().unwrap(),
                                                           actual.to_string().unwrap()));
                                        }
                                    },
                                    Err(e) => {
                                        println!("{}:{:?}", expr_str, e);
                                        failures.push((format!("{}:{:?}", expr_str, e),
                                                       result.to_string().unwrap(),
                                                       "runtime error".to_string()));
                                    }
                                }
                            },
                            Err(e) => {
                                println!("{}:{:?}", expr_str, e);
                                failures.push((format!("{}:{:?}", expr_str, e),
                                               result.to_string().unwrap(),
                                               "parse error".to_string()));
                            }
                        }
                    },
                    None => {}
                }
            }
        }
    }
    if failures.len() > 0 {
        let mut message = String::new();
        message.push_str(&format!("Passed: {}, Failed: {}\n", passed, failures.len()));
        for failure in failures {
            message.push_str(&format!("{}, {}, {}\n", failure.0, failure.1, failure.2));
        }
        panic!(message);
    }
}
