use std::process::{Command, Stdio};

const JPBIN: &str = "../target/debug/jp";

fn get_output(args: Vec<&str>) -> Result<String, String> {
    let mut cmd = Command::new(JPBIN);
    for arg in args {
        cmd.arg(arg);
    }
    let output = cmd.output().unwrap();
    if output.status.success() {
        Ok(String::from_utf8(output.stdout).unwrap())
    } else {
        Err(String::from_utf8(output.stderr).unwrap())
    }
}

#[test]
fn prints_ast() {
    let output = get_output(vec!["--ast", "foo"]).unwrap();
    assert_eq!("Field {\n    offset: 0,\n    name: \"foo\",\n}\n", output);
}

#[test]
fn shows_parse_error_information_with_non_zero_rc() {
    let output = get_output(vec!["--ast", "foo{"]).unwrap_err();
    assert_eq!(
        "Parse error: Unexpected led token -- found Lbrace (line 0, column 3)\nfoo{\
               \n   ^\n\n",
        output
    );
}

#[test]
fn shows_help_info() {
    let output = get_output(vec!["--help"]).unwrap();
    assert!(output.contains("JMESPath command line interface"));
}

#[test]
fn executes_query_against_files() {
    let output = get_output(vec![
        "-e",
        "tests/fixtures/valid-expression",
        "-f",
        "tests/fixtures/valid-json",
    ])
    .unwrap();
    assert_eq!("\"bar\"\n", output);
}

#[test]
fn allows_unquoted_strings() {
    let output = get_output(vec![
        "-e",
        "tests/fixtures/valid-expression",
        "-f",
        "tests/fixtures/valid-json",
        "-u",
    ])
    .unwrap();
    assert_eq!("bar\n", output);
}

#[test]
fn unquoted_does_nothing_for_non_strings() {
    let output = get_output(vec!["-f", "tests/fixtures/valid-json", "-u", "`[\"foo\"]`"]).unwrap();
    assert_eq!("[\n  \"foo\"\n]\n", output);
}

#[test]
fn validates_json_file_exists() {
    let output = get_output(vec![
        "-e",
        "tests/fixtures/valid-expression",
        "-f",
        "tests/fixtures/not-there",
    ])
    .unwrap_err();
    assert_eq!(
        "Error opening JSON file at tests/fixtures/not-there: \
                No such file or directory (os error 2)\n",
        output
    );
}

#[test]
fn validates_expression_file_exists() {
    let output = get_output(vec![
        "-e",
        "tests/fixtures/not-there",
        "-f",
        "tests/fixtures/valid-json",
    ])
    .unwrap_err();
    assert_eq!(
        "Error opening expression file at tests/fixtures/not-there: \
                No such file or directory (os error 2)\n",
        output
    );
}

#[test]
fn validates_json_file_is_valid_json() {
    let output = get_output(vec![
        "-e",
        "tests/fixtures/valid-expression",
        "-f",
        "tests/fixtures/invalid-json",
    ])
    .unwrap_err();
    assert!(output.contains("Error parsing JSON"));
}

#[test]
fn validates_expression_file_is_valid_expression() {
    let output = get_output(vec![
        "-e",
        "tests/fixtures/invalid-expression",
        "-f",
        "tests/fixtures/valid-json",
    ])
    .unwrap_err();
    assert!(output.contains("Parse error"));
}

#[test]
fn can_read_json_from_stdin() {
    use std::io::prelude::*;
    let mut child = Command::new(JPBIN)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .arg("foo")
        .spawn()
        .expect("Failed to spawn process");
    child
        .stdin
        .as_mut()
        .unwrap()
        .write("{\"foo\":\"bar\"}".as_bytes())
        .ok();
    let output = child.wait_with_output().unwrap();
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert_eq!("\"bar\"\n", stdout);
}
