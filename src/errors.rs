//! JMESPath errors.

use std::fmt;

use super::RcVar;
use super::interpreter::Context;

/// JMESPath error
#[derive(Clone,Debug,PartialEq)]
pub struct Error {
    /// Coordinates to where the error was encountered in the original
    /// expression string.
    pub coordinates: Coordinates,
    /// Expression being evaluated.
    pub expression: String,
    /// Error reason information.
    pub error_reason: ErrorReason
}

impl Error {
    /// Create a new JMESPath Error
    pub fn new(expr: &str, offset: usize, error_reason: ErrorReason) -> Error {
        Error {
            expression: expr.to_owned(),
            coordinates: Coordinates::from_offset(expr, offset),
            error_reason: error_reason
        }
    }

    /// Create a new JMESPath Error from a Context struct.
    pub fn from_ctx(ctx: &Context, error_reason: ErrorReason) -> Error {
        Error {
            expression: ctx.expression.to_owned(),
            coordinates: ctx.create_coordinates(),
            error_reason: error_reason
        }
    }
}

impl fmt::Display for Error {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(fmt, "{} ({})\n{}", self.error_reason, self.coordinates,
            self.coordinates.expression_with_carat(&self.expression))
    }
}

/// Error context provides specific details about an error.
#[derive(Clone,Debug,PartialEq)]
pub enum ErrorReason {
    /// An error occurred while parsing an expression.
    Parse(String),
    /// An error occurred while evaluating an expression.
    Runtime(RuntimeError)
}

impl fmt::Display for ErrorReason {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match *self {
            ErrorReason::Parse(ref e) => write!(fmt, "Parse error: {}", e),
            ErrorReason::Runtime(ref e) => write!(fmt, "Runtime error: {}", e),
        }
    }
}

/// Runtime JMESPath error
#[derive(Clone,Debug,PartialEq)]
pub enum RuntimeError {
    /// Encountered when a slice expression uses a step of 0
    InvalidSlice,
    /// Encountered when too many arguments are provided to a function.
    TooManyArguments {
        expected: usize,
        actual: usize,
    },
    /// Encountered when too few arguments are provided to a function.
    NotEnoughArguments {
        expected: usize,
        actual: usize,
    },
    /// Encountered when an unknown function is called.
    UnknownFunction(String),
    /// Encountered when a type of variable given to a function is invalid.
    InvalidType {
        expected: String,
        actual: String,
        actual_value: RcVar,
        position: usize,
    },
    /// Encountered when an expression reference returns an invalid type.
    InvalidReturnType {
        expected: String,
        actual: String,
        actual_value: RcVar,
        position: usize,
        invocation: usize,
    },
}

impl fmt::Display for RuntimeError {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        use self::RuntimeError::*;
        match *self {
            UnknownFunction(ref function) => {
                write!(fmt, "Call to undefined function {}", function)
            },
            TooManyArguments { ref expected, ref actual } => {
                write!(fmt, "Too many arguments: expected {}, found {}", expected, actual)
            },
            NotEnoughArguments { ref expected, ref actual } => {
                write!(fmt, "Not enough arguments: expected {}, found {}", expected, actual)
            },
            InvalidType { ref expected, ref actual, ref position, ref actual_value } => {
                write!(fmt, "Argument {} expects type {}, given {} {}",
                    position, expected, actual, actual_value.to_owned())
            },
            InvalidSlice => write!(fmt, "Invalid slice"),
            InvalidReturnType { ref expected, ref actual, ref position, ref invocation,
                    ref actual_value } => {
                write!(fmt, "Argument {} must return {} but invocation {} returned {} {}",
                    position, expected, invocation, actual, actual_value.to_owned())
            },
        }
    }
}

/// Defines the coordinates to a position in an expression string.
#[derive(Clone, Debug, PartialEq)]
pub struct Coordinates {
    /// Absolute character position.
    pub offset: usize,
    /// Line number of the coordinate.
    pub line: usize,
    /// Column of the line number.
    pub column: usize,
}

impl Coordinates {
    /// Create an expression coordinates struct based on an offset
    // position in the expression.
    pub fn from_offset(expr: &str, offset: usize) -> Coordinates {
        // Find each new line and create a formatted error message.
        let mut current_line: usize = 0;
        let mut current_col: usize = 0;
        for c in expr.chars().take(offset) {
            match c {
                '\n' => {
                    current_line += 1;
                    current_col = 0;
                },
                _ => current_col += 1
            }
        }
        Coordinates {
            line: current_line,
            column: current_col,
            offset: offset
        }
    }

    fn inject_carat(&self, buff: &mut String) {
        buff.push_str(&(0..self.column).map(|_| ' ').collect::<String>());
        buff.push_str(&"^\n");
    }

    /// Returns a string that shows the expression and a carat pointing to
    /// the coordinate.
    pub fn expression_with_carat(&self, expr: &str) -> String {
        let mut buff = String::new();
        let mut matched = false;
        let mut current_line = 0;
        for c in expr.chars() {
            buff.push(c);
            if c == '\n' {
                current_line += 1;
                if current_line == self.line + 1 {
                    matched = true;
                    self.inject_carat(&mut buff);
                }
            }
        }
        if !matched {
            buff.push('\n');
            self.inject_carat(&mut buff);
        }
        buff
    }
}

impl fmt::Display for Coordinates {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(fmt, "line {}, column {}", self.line, self.column)
    }
}

#[cfg(test)]
mod test {
    use std::rc::Rc;

    use super::*;
    use Variable;

    #[test]
    fn coordinates_can_be_created_from_string_with_new_lines() {
        let expr = "foo\n..bar";
        let coords = Coordinates::from_offset(expr, 5);
        assert_eq!(1, coords.line);
        assert_eq!(1, coords.column);
        assert_eq!(5, coords.offset);
        assert_eq!("foo\n..bar\n ^\n", coords.expression_with_carat(expr));
    }

    #[test]
    fn coordinates_can_be_created_from_string_with_new_lines_pointing_to_non_last() {
        let expr = "foo\n..bar\nbaz";
        let coords = Coordinates::from_offset(expr, 5);
        assert_eq!(1, coords.line);
        assert_eq!(1, coords.column);
        assert_eq!(5, coords.offset);
        assert_eq!("foo\n..bar\n ^\nbaz", coords.expression_with_carat(expr));
    }

    #[test]
    fn coordinates_can_be_created_from_string_with_no_new_lines() {
        let expr = "foo..bar";
        let coords = Coordinates::from_offset(expr, 4);
        assert_eq!(0, coords.line);
        assert_eq!(4, coords.column);
        assert_eq!(4, coords.offset);
        assert_eq!("foo..bar\n    ^\n", coords.expression_with_carat(expr));
    }

    #[test]
    fn error_reason_displays_parse_errors() {
        let reason = ErrorReason::Parse("bar".to_owned());
        assert_eq!("Parse error: bar", reason.to_string());
    }

    #[test]
    fn error_reason_displays_runtime_errors() {
        let reason = ErrorReason::Runtime(RuntimeError::UnknownFunction("a".to_owned()));
        assert_eq!("Runtime error: Call to undefined function a", reason.to_string());
    }

    #[test]
    fn displays_invalid_type_error() {
        let error = RuntimeError::InvalidType {
            expected: "string".to_owned(),
            actual: "boolean".to_owned(),
            actual_value: Rc::new(Variable::Bool(true)),
            position: 0,
        };
        assert_eq!("Argument 0 expects type string, given boolean true", error.to_string());
    }

    #[test]
    fn displays_invalid_slice() {
        let error = RuntimeError::InvalidSlice;
        assert_eq!("Invalid slice", error.to_string());
    }

    #[test]
    fn displays_too_many_arguments_error() {
        let error = RuntimeError::TooManyArguments {
            expected: 1,
            actual: 2
        };
        assert_eq!("Too many arguments: expected 1, found 2", error.to_string());
    }

    #[test]
    fn displays_not_enough_arguments_error() {
        let error = RuntimeError::NotEnoughArguments {
            expected: 2,
            actual: 1
        };
        assert_eq!("Not enough arguments: expected 2, found 1", error.to_string());
    }

    #[test]
    fn displays_invalid_return_type_error() {
        let error = RuntimeError::InvalidReturnType {
            expected: "string".to_string(),
            actual: "boolean".to_string(),
            actual_value: Rc::new(Variable::Bool(true)),
            position: 0,
            invocation: 2,
        };
        assert_eq!("Argument 0 must return string but invocation 2 returned boolean true",
                   error.to_string());
    }
}
