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
            expression: expr.to_string(),
            coordinates: Coordinates::from_offset(expr, offset),
            error_reason: error_reason
        }
    }

    /// Create a new JMESPath Error from a Context struct.
    pub fn from_ctx(ctx: &Context, error_reason: ErrorReason) -> Error {
        Error {
            expression: ctx.expression.to_string(),
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
        match self {
            &ErrorReason::Parse(ref e) => write!(fmt, "Parse error: {}", e),
            &ErrorReason::Runtime(ref e) => write!(fmt, "Runtime error: {}", e),
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
        match self {
            &UnknownFunction(ref function) => {
                write!(fmt, "Call to undefined function {}", function)
            },
            &TooManyArguments { ref expected, ref actual } => {
                write!(fmt, "Too many arguments, expected {}, found {}", expected, actual)
            },
            &NotEnoughArguments { ref expected, ref actual } => {
                write!(fmt, "Not enough arguments, expected {}, found {}", expected, actual)
            },
            &InvalidType { ref expected, ref actual, ref position, ref actual_value } => {
                write!(fmt, "Argument {} expects type {}, given {} {}",
                    position, expected, actual, actual_value.to_string())
            },
            &InvalidSlice => write!(fmt, "Invalid slice"),
            &InvalidReturnType { ref expected, ref actual, ref position, ref invocation,
                    ref actual_value } => {
                write!(fmt, "Argument {} must return {} but invocation {} returned {} {}",
                    position, expected, invocation, actual, actual_value.to_string())
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
    use super::*;

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
}
