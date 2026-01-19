use jmespath_cli::{JpArgs, run, run_with_stdin};

fn run_jp(args: JpArgs) -> Result<String, String> {
    match run(args) {
        Ok(output) => Ok(output.stdout),
        Err(output) => Err(output.stderr),
    }
}

fn run_jp_with_stdin(args: JpArgs, stdin: &str) -> Result<String, String> {
    match run_with_stdin(args, Some(stdin)) {
        Ok(output) => Ok(output.stdout),
        Err(output) => Err(output.stderr),
    }
}

#[test]
fn prints_ast() {
    let args = JpArgs {
        ast: true,
        expression: Some("foo".to_string()),
        ..Default::default()
    };
    let output = run_jp(args).unwrap();
    assert_eq!("Field {\n    offset: 0,\n    name: \"foo\",\n}\n", output);
}

#[test]
fn shows_parse_error_information() {
    let args = JpArgs {
        ast: true,
        expression: Some("foo{".to_string()),
        ..Default::default()
    };
    let output = run_jp(args).unwrap_err();
    assert_eq!(
        "Parse error: Unexpected led token -- found Lbrace (line 0, column 3)\nfoo{\
               \n   ^\n\n",
        output
    );
}

#[test]
fn executes_query_against_files() {
    let args = JpArgs {
        expr_file: Some("tests/fixtures/valid-expression".to_string()),
        filename: Some("tests/fixtures/valid-json".to_string()),
        ..Default::default()
    };
    let output = run_jp(args).unwrap();
    assert_eq!("\"bar\"\n", output);
}

#[test]
fn allows_unquoted_strings() {
    let args = JpArgs {
        expr_file: Some("tests/fixtures/valid-expression".to_string()),
        filename: Some("tests/fixtures/valid-json".to_string()),
        unquoted: true,
        ..Default::default()
    };
    let output = run_jp(args).unwrap();
    assert_eq!("bar\n", output);
}

#[test]
fn unquoted_does_nothing_for_non_strings() {
    let args = JpArgs {
        filename: Some("tests/fixtures/valid-json".to_string()),
        unquoted: true,
        expression: Some("`[\"foo\"]`".to_string()),
        ..Default::default()
    };
    let output = run_jp(args).unwrap();
    assert_eq!("[\n  \"foo\"\n]\n", output);
}

#[test]
fn validates_json_file_exists() {
    let args = JpArgs {
        expr_file: Some("tests/fixtures/valid-expression".to_string()),
        filename: Some("tests/fixtures/not-there".to_string()),
        ..Default::default()
    };
    let output = run_jp(args).unwrap_err();
    assert_eq!(
        "Error opening JSON file at tests/fixtures/not-there: \
                No such file or directory (os error 2)\n",
        output
    );
}

#[test]
fn validates_expression_file_exists() {
    let args = JpArgs {
        expr_file: Some("tests/fixtures/not-there".to_string()),
        filename: Some("tests/fixtures/valid-json".to_string()),
        ..Default::default()
    };
    let output = run_jp(args).unwrap_err();
    assert_eq!(
        "Error opening expression file at tests/fixtures/not-there: \
                No such file or directory (os error 2)\n",
        output
    );
}

#[test]
fn validates_json_file_is_valid_json() {
    let args = JpArgs {
        expr_file: Some("tests/fixtures/valid-expression".to_string()),
        filename: Some("tests/fixtures/invalid-json".to_string()),
        ..Default::default()
    };
    let output = run_jp(args).unwrap_err();
    assert!(output.contains("Error parsing JSON"));
}

#[test]
fn validates_expression_file_is_valid_expression() {
    let args = JpArgs {
        expr_file: Some("tests/fixtures/invalid-expression".to_string()),
        filename: Some("tests/fixtures/valid-json".to_string()),
        ..Default::default()
    };
    let output = run_jp(args).unwrap_err();
    assert!(output.contains("Parse error"));
}

#[test]
fn can_read_json_from_stdin() {
    let args = JpArgs {
        expression: Some("foo".to_string()),
        ..Default::default()
    };
    let output = run_jp_with_stdin(args, "{\"foo\":\"bar\"}").unwrap();
    assert_eq!("\"bar\"\n", output);
}
