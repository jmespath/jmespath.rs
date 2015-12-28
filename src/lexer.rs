//! Module for tokenizing JMESPath expression.
use std::rc::Rc;
use std::iter::Peekable;
use std::str::CharIndices;
use std::collections::VecDeque;

use self::Token::*;
use super::variable::Variable;

/// Represents a lexical token of a JMESPath expression.
#[derive(Clone, PartialEq, Debug)]
pub enum Token {
    Identifier(String),
    QuotedIdentifier(String),
    Number(i32),
    Literal(Rc<Variable>),
    Error { value: String, msg: String },
    Dot,
    Star,
    Flatten,
    And,
    Or,
    Pipe,
    Filter,
    Lbracket,
    Rbracket,
    Comma,
    Colon,
    Not,
    Ne,
    Eq,
    Gt,
    Gte,
    Lt,
    Lte,
    At,
    Ampersand,
    Lparen,
    Rparen,
    Lbrace,
    Rbrace,
    Eof,
}

impl Token {
    /// Provides the left binding power of the token.
    pub fn lbp(&self) -> usize {
        match *self {
            Pipe     => 1,
            Or       => 2,
            And      => 3,
            Eq       => 5,
            Gt       => 5,
            Lt       => 5,
            Gte      => 5,
            Lte      => 5,
            Ne       => 5,
            Flatten  => 9,
            Star     => 20,
            Filter   => 21,
            Dot      => 40,
            Not      => 45,
            Lbrace   => 50,
            Lbracket => 55,
            Lparen   => 60,
            _        => 0,
        }
    }
}

pub type TokenTuple = (usize, Token);
type CharIter<'a> = Peekable<CharIndices<'a>>;

pub fn tokenize(expr: &str) -> VecDeque<TokenTuple> {
    let last_position = expr.len();
    let mut iter = expr.char_indices().peekable();
    let mut tokens = VecDeque::new();
    macro_rules! tok {
        ($pos:expr, $tok:expr) => {{ iter.next(); tokens.push_back(($pos, $tok)); }};
    }
    loop {
        match iter.peek() {
            Some(&(pos, ch)) => {
                match ch {
                    'a' ... 'z' | 'A' ... 'Z' | '_' =>
                        tokens.push_back((pos, consume_identifier(&mut iter))),
                    '.' => tok!(pos, Dot),
                    '[' => tok!(pos, consume_lbracket(&mut iter)),
                    '*' => tok!(pos, Star),
                    '|' => tok!(pos, alt(&mut iter, &'|', Or, Pipe)),
                    '@' => tok!(pos, At),
                    ']' => tok!(pos, Rbracket),
                    '{' => tok!(pos, Lbrace),
                    '}' => tok!(pos, Rbrace),
                    '&' => tok!(pos, alt(&mut iter, &'&', And, Ampersand)),
                    '(' => tok!(pos, Lparen),
                    ')' => tok!(pos, Rparen),
                    ',' => tok!(pos, Comma),
                    ':' => tok!(pos, Colon),
                    '"' => tokens.push_back((pos, consume_quoted_identifier(&mut iter))),
                    '\'' => tokens.push_back((pos, consume_raw_string(&mut iter))),
                    '`' => tokens.push_back((pos, consume_literal(&mut iter))),
                    '=' => tok!(pos, alt(&mut iter, &'=', Eq, Error {
                        value: '='.to_string(),
                        msg: "Did you mean \"==\"?".to_string() })),
                    '>' => tok!(pos, alt(&mut iter, &'=', Gte, Gt)),
                    '<' => tok!(pos, alt(&mut iter, &'=', Lte, Lt)),
                    '!' => tok!(pos, alt(&mut iter, &'=', Ne, Not)),
                    '0' ... '9' => tokens.push_back((pos, consume_number(&mut iter, false))),
                    '-' => tokens.push_back((pos, consume_negative_number(&mut iter))),
                    // Skip whitespace tokens
                    ' ' | '\n' | '\t' | '\r' => {
                        iter.next();
                        continue;
                    },
                    c @ _ => tok!(pos, Error { value: c.to_string(), msg: "".to_string() })
                }
            },
            None => {
                tokens.push_back((last_position, Eof));
                return tokens;
            }
        }
    }
}

// Consumes characters while the predicate function returns true.
#[inline]
fn consume_while<F>(iter: &mut CharIter,
                    predicate: F) -> String
                    where F: Fn(char) -> bool {
    let mut buffer = iter.next().expect("Expected token").1.to_string();
    loop {
        match iter.peek() {
            None => break,
            Some(&(_, c)) if !predicate(c) => break,
            Some(&(_, c)) => {
                buffer.push(c);
                iter.next();
            }
        }
    }
    buffer
}

// Consumes "[", "[]", "[?
#[inline]
fn consume_lbracket(iter: &mut CharIter) -> Token {
    match iter.peek() {
        Some(&(_, ']')) => {
            iter.next();
            Flatten
        },
        Some(&(_, '?')) => {
            iter.next();
            Filter
        },
        _ => Lbracket,
    }
}

// Consume identifiers: ( ALPHA / "_" ) *( DIGIT / ALPHA / "_" )
#[inline]
fn consume_identifier(iter: &mut CharIter) -> Token {
    Identifier(consume_while(iter, |c| {
        match c {
            'a' ... 'z' | '_' | 'A' ... 'Z' | '0' ... '9' => true,
            _ => false
        }
    }))
}

// Consumes numbers: *"-" "0" / ( %x31-39 *DIGIT )
#[inline]
fn consume_number(iter: &mut CharIter, is_negative: bool) -> Token {
    let lexeme = consume_while(iter, |c| c.is_digit(10));
    let numeric_value: i32 = lexeme.parse().expect("Expected valid number");
    match is_negative {
        true => Number(numeric_value * -1),
        false => Number(numeric_value)
    }
}

// Consumes a negative number
#[inline]
fn consume_negative_number(iter: &mut CharIter) -> Token {
    // Skip the "-" number token.
    iter.next();
    // Ensure that the next value is a number > 0
    match iter.peek() {
        Some(&(_, c)) if c.is_numeric() && c != '0' => consume_number(iter, true),
        _ => Error {
            value: "-".to_string(),
            msg: "Negative sign must be followed by numbers 1-9".to_string()
        }
    }
}

// Consumes tokens inside of a closing character. The closing character
// can be escaped using a "\" character.
#[inline]
fn consume_inside<F>(iter: &mut CharIter, wrapper: char, invoke: F) -> Token
    where F: Fn(String) -> Token
{
    let mut buffer = String::new();
    // Skip the opening character.
    iter.next();
    while let Some((_, c)) = iter.next() {
        if c == wrapper {
            return invoke(buffer);
        } else if c == '\\' {
            buffer.push(c);
            if let Some((_, c)) = iter.next() {
                buffer.push(c);
            }
        } else {
            buffer.push(c)
        }
    }
    // The token was not closed, so error with the string, including the
    // wrapper (e.g., '"foo').
    Error {
        value: wrapper.to_string() + buffer.as_ref(),
        msg: format!("Unclosed {} delimiter", wrapper)
    }
}

// Consume and parse a quoted identifier token.
#[inline]
fn consume_quoted_identifier(iter: &mut CharIter) -> Token {
    consume_inside(iter, '"', |s| {
        // JSON decode the string to expand escapes
        match Variable::from_str(format!(r##""{}""##, s).as_ref()) {
            // Convert the JSON value into a string literal.
            Ok(j) => QuotedIdentifier(j.as_string().expect("Expected string").to_string()),
            Err(e) => Error {
                value: format!(r#""{}""#, s),
                msg: format!("Unable to parse JSON value in quoted identifier: {}", e)
            }
        }
    })
}

#[inline]
fn consume_raw_string(iter: &mut CharIter) -> Token {
    // Note: we need to unescape here because the backslashes are passed through.
    consume_inside(iter, '\'', |s| Literal(Rc::new(Variable::String(s.replace("\\'", "'")))))
}

// Consume and parse a literal JSON token.
#[inline]
fn consume_literal(iter: &mut CharIter) -> Token {
    consume_inside(iter, '`', |s| {
        let unescapeed = s.replace("\\`", "`");
        match Variable::from_str(unescapeed.as_ref()) {
            Ok(j) => Literal(Rc::new(j)),
            Err(err) => Error {
                value: format!("`{}`", unescapeed),
                msg: format!("Unable to parse literal JSON: {}", err)
            }
        }
    })
}

#[inline]
fn alt(iter: &mut CharIter, expected: &char, match_type: Token, else_type: Token) -> Token {
    match iter.peek() {
        Some(&(_, c)) if c == *expected => {
            iter.next();
            match_type
        },
        _ => else_type
    }
}


#[cfg(test)]
mod tests {
    use std::rc::Rc;
    use super::*;
    use super::Token::*;
    use variable::Variable;

    fn tokenize_queue(expr: &str) -> Vec<TokenTuple> {
        let mut result = tokenize(expr);
        let mut v = Vec::new();
        while let Some(node) = result.pop_front() {
            v.push(node);
        }
        v
    }

    #[test]
    fn tokenize_basic_test() {
        assert_eq!(tokenize_queue("."), vec![(0, Dot), (1, Eof)]);
        assert_eq!(tokenize_queue("*"), vec![(0, Star), (1, Eof)]);
        assert_eq!(tokenize_queue("@"), vec![(0, At), (1, Eof)]);
        assert_eq!(tokenize_queue("]"), vec![(0, Rbracket), (1, Eof)]);
        assert_eq!(tokenize_queue("{"), vec![(0, Lbrace), (1, Eof)]);
        assert_eq!(tokenize_queue("}"), vec![(0, Rbrace), (1, Eof)]);
        assert_eq!(tokenize_queue("("), vec![(0, Lparen), (1, Eof)]);
        assert_eq!(tokenize_queue(")"), vec![(0, Rparen), (1, Eof)]);
        assert_eq!(tokenize_queue(","), vec![(0, Comma), (1, Eof)]);
    }

    #[test]
    fn tokenize_lbracket_test() {
        assert_eq!(tokenize_queue("["), vec![(0, Lbracket), (1, Eof)]);
        assert_eq!(tokenize_queue("[]"), vec![(0, Flatten), (2, Eof)]);
        assert_eq!(tokenize_queue("[?"), vec![(0, Filter), (2, Eof)]);
    }

    #[test]
    fn tokenize_pipe_test() {
        assert_eq!(tokenize_queue("|"), vec![(0, Pipe), (1, Eof)]);
        assert_eq!(tokenize_queue("||"), vec![(0, Or), (2, Eof)]);
    }

    #[test]
    fn tokenize_and_ampersand_test() {
        assert_eq!(tokenize_queue("&"), vec![(0, Ampersand), (1, Eof)]);
        assert_eq!(tokenize_queue("&&"), vec![(0, And), (2, Eof)]);
    }

    #[test]
    fn tokenize_lt_gt_test() {
        assert_eq!(tokenize_queue("<"), vec![(0, Lt), (1, Eof)]);
        assert_eq!(tokenize_queue("<="), vec![(0, Lte), (2, Eof)]);
        assert_eq!(tokenize_queue(">"), vec![(0, Gt), (1, Eof)]);
        assert_eq!(tokenize_queue(">="), vec![(0, Gte), (2, Eof)]);
    }

    #[test]
    fn tokenize_eq_ne_test() {
        assert_eq!(tokenize_queue("="), vec![(0, Error {
            value: "=".to_string(),
            msg: "Did you mean \"==\"?".to_string()
        }), (1, Eof)]);
        assert_eq!(tokenize_queue("=="), vec![(0, Eq), (2, Eof)]);
        assert_eq!(tokenize_queue("!"), vec![(0, Not), (1, Eof)]);
        assert_eq!(tokenize_queue("!="), vec![(0, Ne), (2, Eof)]);
    }

    #[test]
    fn skips_whitespace() {
        let tokens = tokenize_queue(" \t\n\r\t. (");
        assert_eq!(tokens, vec![(5, Dot), (7, Lparen), (8, Eof)]);
    }

    #[test]
    fn tokenize_single_error_test() {
        assert_eq!(tokenize_queue("~"), vec![(0, Error {
            value: "~".to_string(),
            msg: "".to_string()
        }), (1, Eof)]);
    }

    #[test]
    fn tokenize_unclosed_errors_test() {
        assert_eq!(tokenize_queue("\"foo"), vec![
            (0, Error {value: "\"foo".to_string(), msg: "Unclosed \" delimiter".to_string() }),
            (4, Eof)
        ]);
        assert_eq!(tokenize_queue("`foo"), vec![
            (0, Error {
                value: "`foo".to_string(),
                msg: "Unclosed ` delimiter".to_string()
            }),
            (4, Eof)
        ]);
    }

    #[test]
    fn tokenize_identifier_test() {
        assert_eq!(tokenize_queue("foo_bar"), vec![
            (0, Identifier("foo_bar".to_string())),
            (7, Eof)
        ]);
        assert_eq!(tokenize_queue("a"), vec![
            (0, Identifier("a".to_string())),
            (1, Eof)
        ]);
        assert_eq!(tokenize_queue("_a"), vec![
            (0, Identifier("_a".to_string())),
            (2, Eof)
        ]);
    }

    #[test]
    fn tokenize_quoted_identifier_test() {
        assert_eq!(tokenize_queue("\"foo\""), vec![
            (0, QuotedIdentifier("foo".to_string())),
            (5, Eof)
        ]);
        assert_eq!(tokenize_queue("\"\""), vec![
            (0, QuotedIdentifier("".to_string())),
            (2, Eof)
        ]);
        assert_eq!(tokenize_queue("\"a_b\""), vec![
            (0, QuotedIdentifier("a_b".to_string())),
            (5, Eof)
        ]);
        assert_eq!(tokenize_queue("\"a\\nb\""), vec![
            (0, QuotedIdentifier("a\nb".to_string())),
            (6, Eof)
        ]);
        assert_eq!(tokenize_queue("\"a\\\\nb\""), vec![
            (0, QuotedIdentifier("a\\nb".to_string())),
            (7, Eof)
        ]);
    }

    #[test]
    fn tokenize_raw_string_test() {
        assert_eq!(tokenize_queue("'foo'"), vec![
            (0, Literal(Rc::new(Variable::String("foo".to_string())))),
            (5, Eof)
        ]);
        assert_eq!(tokenize_queue("''"), vec![
            (0, Literal(Rc::new(Variable::String("".to_string())))),
            (2, Eof)
        ]);
        assert_eq!(tokenize_queue("'a\\nb'"), vec![
            (0, Literal(Rc::new(Variable::String("a\\nb".to_string())))),
            (6, Eof)
        ]);
    }

    #[test]
    fn tokenize_literal_test() {
        // Must enclose in quotes. See JEP 12.
        assert_eq!(tokenize_queue("`a`"), vec![
            (0, Error {
                value: "`a`".to_string(),
                msg: "Unable to parse literal JSON: SyntaxError(\"invalid syntax\", 1, 1)"
                .to_string()
            }),
            (3, Eof)
        ]);
        assert_eq!(tokenize_queue("`\"a\"`"), vec![
            (0, Literal(Rc::new(Variable::String("a".to_string())))),
            (5, Eof)
        ]);
        assert_eq!(tokenize_queue("`\"a b\"`"), vec![
            (0, Literal(Rc::new(Variable::String("a b".to_string())))),
            (7, Eof)
        ]);
    }

    #[test]
    fn tokenize_number_test() {
        assert_eq!(tokenize_queue("0"), vec![(0, Number(0)), (1, Eof)]);
        assert_eq!(tokenize_queue("1"), vec![(0, Number(1)), (1, Eof)]);
        assert_eq!(tokenize_queue("123"), vec![(0, Number(123)), (3, Eof)]);
    }

    #[test]
    fn tokenize_negative_number_test() {
        assert_eq!(tokenize_queue("-10"), vec![(0, Number(-10)), (3, Eof)]);
    }

    #[test]
    fn tokenize_negative_number_test_failure() {
        assert_eq!(tokenize_queue("-01"), vec![
            (0, Error {
                value: "-".to_string(),
                msg: "Negative sign must be followed by numbers 1-9".to_string()
            }),
            (1, Number(1)),
            (3, Eof)
        ]);
    }

    #[test]
    fn tokenize_successive_test() {
        let expr = "foo.bar || `\"a\"` | 10";
        let tokens = tokenize(expr);
        assert_eq!(tokens[0], (0, Identifier("foo".to_string())));
        assert_eq!(tokens[1], (3, Dot));
        assert_eq!(tokens[2], (4, Identifier("bar".to_string())));
        assert_eq!(tokens[3], (8, Or));
        assert_eq!(tokens[4], (11, Literal(Rc::new(Variable::String("a".to_string())))));
        assert_eq!(tokens[5], (17, Pipe));
        assert_eq!(tokens[6], (19, Number(10)));
        assert_eq!(tokens[7], (21, Eof));
    }

    #[test]
    fn tokenizes_slices() {
        let tokens = tokenize("foo[0::-1]");
        assert_eq!("[(0, Identifier(\"foo\")), (3, Lbracket), (4, Number(0)), (5, Colon), \
                     (6, Colon), (7, Number(-1)), (9, Rbracket), (10, Eof)]",
                   format!("{:?}", tokens));
    }
}
