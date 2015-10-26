//! Module for tokenizing JMESPath expression.
use std::rc::Rc;
use std::iter::Peekable;
use std::str::CharIndices;

use self::Token::*;
use variable::Variable;

/// Tokenizes a JMESPath expression.
pub fn tokenize(expr: &str) -> Lexer {
    Lexer::new(expr)
}

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

/// The lexer is used to tokenize JMESPath expressions.
pub struct Lexer<'a> {
    // Iterator over the characters in the string.
    iter: Peekable<CharIndices<'a>>,
    // Whether or not an EOF token has been returned.
    sent_eof: bool,
    // Last position in the iterator.
    last_position: usize,
}

impl<'a> Lexer<'a> {
    pub fn new(expr: &'a str) -> Lexer<'a> {
        Lexer {
            sent_eof: false,
            iter: expr.char_indices().peekable(),
            last_position: expr.len()
        }
    }

    // Consumes characters while the predicate function returns true.
    #[inline]
    fn consume_while<F>(&mut self, predicate: F) -> String
        where F: Fn(char) -> bool
    {
        let mut buffer = self.iter.next().unwrap().1.to_string();
        loop {
            match self.iter.peek() {
                None => break,
                Some(&(_, c)) if !predicate(c) => break,
                Some(&(_, c)) => { buffer.push(c); self.iter.next(); }
            }
        }
        buffer
    }

    // Consumes "[", "[]", "[?
    #[inline]
    fn consume_lbracket(&mut self) -> Token {
        match self.iter.peek() {
            Some(&(_, ']')) => { self.iter.next(); Flatten },
            Some(&(_, '?')) => { self.iter.next(); Filter },
            _ => Lbracket,
        }
    }

    // Consume identifiers: ( ALPHA / "_" ) *( DIGIT / ALPHA / "_" )
    #[inline]
    fn consume_identifier(&mut self) -> Token {
        Identifier(self.consume_while(|c| {
            match c {
                'a' ... 'z' | '_' | 'A' ... 'Z' | '0' ... '9' => true,
                _ => false
            }
        }))
    }

    // Consumes numbers: *"-" "0" / ( %x31-39 *DIGIT )
    #[inline]
    fn consume_number(&mut self, is_negative: bool) -> Token {
        let lexeme = self.consume_while(|c| c.is_digit(10));
        let numeric_value: i32 = lexeme.parse().unwrap();
        match is_negative {
            true => Number(numeric_value * -1),
            false => Number(numeric_value)
        }
    }

    // Consumes a negative number
    #[inline]
    fn consume_negative_number(&mut self) -> Token {
        // Skip the "-" number token.
        self.iter.next();
        // Ensure that the next value is a number > 0
        match self.iter.peek() {
            Some(&(_, c)) if c.is_numeric() && c != '0' => self.consume_number(true),
            _ => Error {
                value: "-".to_string(),
                msg: "Negative sign must be followed by numbers 1-9".to_string()
            }
        }
    }

    // Consumes tokens inside of a closing character. The closing character
    // can be escaped using a "\" character.
    #[inline]
    fn consume_inside<F>(&mut self, wrapper: char, invoke: F) -> Token
        where F: Fn(String) -> Token
    {
        let mut buffer = String::new();
        // Skip the opening character.
        self.iter.next();
        loop {
            match self.iter.next() {
                Some((_, c)) if c == wrapper => return invoke(buffer),
                Some((_, c)) if c == '\\' => {
                    buffer.push(c);
                    // Break if an escape is followed by the end of the string.
                    match self.iter.next() {
                        Some((_, c)) => buffer.push(c),
                        None => break
                    }
                },
                Some((_, c)) => buffer.push(c),
                None => break
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
    fn consume_quoted_identifier(&mut self) -> Token {
        self.consume_inside('"', |s| {
            // JSON decode the string to expand escapes
            match Variable::from_str(format!(r##""{}""##, s).as_ref()) {
                // Convert the JSON value into a string literal.
                Ok(j) => QuotedIdentifier(j.as_string().unwrap().to_string()),
                Err(e) => Error {
                    value: format!(r#""{}""#, s),
                    msg: format!("Unable to parse JSON value in quoted identifier: {}", e)
                }
            }
        })
    }

    #[inline]
    fn consume_raw_string(&mut self) -> Token {
        self.consume_inside('\'', |s| Literal(Rc::new(Variable::String(s))))
    }

    // Consume and parse a literal JSON token.
    #[inline]
    fn consume_literal(&mut self) -> Token {
        self.consume_inside('`', |s| {
            match Variable::from_str(s.as_ref()) {
                Ok(j) => Literal(Rc::new(j)),
                Err(err) => Error {
                    value: format!("`{}`", s),
                    msg: format!("Unable to parse literal JSON: {}", err)
                }
            }
        })
    }

    #[inline]
    fn alt(&mut self, expected: &char, match_type: Token, else_type: Token) -> Token {
        match self.iter.peek() {
            Some(&(_, c)) if c == *expected => {
                self.iter.next();
                match_type
            },
            _ => else_type
        }
    }
}

impl<'a> Iterator for Lexer<'a> {
    // Each value yielded is the token and the position of the token in the expression.
    type Item = (usize, Token);
    fn next(&mut self) -> Option<(usize, Token)> {
        macro_rules! tok {
            ($x:expr) => {{ self.iter.next(); return Some($x); }};
        }
        loop {
            match self.iter.peek() {
                Some(&(pos, ch)) => {
                    match ch {
                        'a' ... 'z' | 'A' ... 'Z' | '_' =>
                            return Some((pos, self.consume_identifier())),
                        '.' => tok!((pos, Dot)),
                        '[' => tok!((pos, self.consume_lbracket())),
                        '*' => tok!((pos, Star)),
                        '|' => tok!((pos, self.alt(&'|', Or, Pipe))),
                        '@' => tok!((pos, At)),
                        ']' => tok!((pos, Rbracket)),
                        '{' => tok!((pos, Lbrace)),
                        '}' => tok!((pos, Rbrace)),
                        '&' => tok!((pos, self.alt(&'&', And, Ampersand))),
                        '(' => tok!((pos, Lparen)),
                        ')' => tok!((pos, Rparen)),
                        ',' => tok!((pos, Comma)),
                        ':' => tok!((pos, Colon)),
                        '"' => return Some((pos, self.consume_quoted_identifier())),
                        '\'' => return Some((pos, self.consume_raw_string())),
                        '`' => return Some((pos, self.consume_literal())),
                        '=' => tok!((pos, self.alt(&'=', Eq, Error {
                                value: '='.to_string(),
                                msg: "Did you mean \"==\"?".to_string() }))),
                        '>' => tok!((pos, self.alt(&'=', Gte, Gt))),
                        '<' => tok!((pos, self.alt(&'=', Lte, Lt))),
                        '!' => tok!((pos, self.alt(&'=', Ne, Not))),
                        '0' ... '9' => return Some((pos, self.consume_number(false))),
                        '-' => return Some((pos, self.consume_negative_number())),
                        // Skip whitespace tokens
                        ' ' | '\n' | '\t' | '\r' => {
                            self.iter.next();
                            continue;
                        },
                        c @ _ => tok!((pos, Error { value: c.to_string(), msg: "".to_string() }))
                    }
                },
                None if self.sent_eof => return None,
                None => { self.sent_eof = true; return Some((self.last_position, Eof)); }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use std::rc::Rc;
    use super::*;
    use super::Token::*;
    use variable::Variable;

    #[test]
    fn tokenize_basic_test() {
        assert!(tokenize(".").next() == Some((0, Dot)));
        assert!(tokenize("*").next() == Some((0, Star)));
        assert!(tokenize("@").next() == Some((0, At)));
        assert!(tokenize("]").next() == Some((0, Rbracket)));
        assert!(tokenize("{").next() == Some((0, Lbrace)));
        assert!(tokenize("}").next() == Some((0, Rbrace)));
        assert!(tokenize("(").next() == Some((0, Lparen)));
        assert!(tokenize(")").next() == Some((0, Rparen)));
        assert!(tokenize(",").next() == Some((0, Comma)));
    }

    #[test]
    fn tokenize_lbracket_test() {
        assert_eq!(tokenize("[").next(), Some((0, Lbracket)));
        assert_eq!(tokenize("[]").next(), Some((0, Flatten)));
        assert_eq!(tokenize("[?").next(), Some((0, Filter)));
    }

    #[test]
    fn tokenize_pipe_test() {
        assert!(tokenize("|").next() == Some((0, Pipe)));
        assert!(tokenize("||").next() == Some((0, Or)));
    }

    #[test]
    fn tokenize_and_ampersand_test() {
        assert!(tokenize("&").next() == Some((0, Ampersand)));
        assert!(tokenize("&&").next() == Some((0, And)));
    }

    #[test]
    fn tokenize_lt_gt_test() {
        assert!(tokenize("<").next() == Some((0, Lt)));
        assert!(tokenize("<=").next() == Some((0, Lte)));
        assert!(tokenize(">").next() == Some((0, Gt)));
        assert!(tokenize(">=").next() == Some((0, Gte)));
    }

    #[test]
    fn tokenize_eq_ne_test() {
        assert_eq!(tokenize("=").next(),
                   Some((0, Error {
                       value: "=".to_string(),
                       msg: "Did you mean \"==\"?".to_string() })));
        assert!(tokenize("==").next() == Some((0, Eq)));
        assert!(tokenize("!").next() == Some((0, Not)));
        assert!(tokenize("!=").next() == Some((0, Ne)));
    }

    #[test]
    fn skips_whitespace() {
        let mut tokens = tokenize(" \t\n\r\t. (");
        assert_eq!(tokens.next(), Some((5, Dot)));
        assert_eq!(tokens.next(), Some((7, Lparen)));
    }

    #[test]
    fn tokenize_single_error_test() {
        assert_eq!(tokenize("~").next(),
                   Some((0, Error {
                       value: "~".to_string(),
                       msg: "".to_string() })));
    }

    #[test]
    fn tokenize_unclosed_errors_test() {
        assert_eq!(tokenize("\"foo").next(),
                   Some((0, Error {
                       value: "\"foo".to_string(),
                       msg: "Unclosed \" delimiter".to_string() })));
        assert_eq!(tokenize("`foo").next(),
                   Some((0, Error {
                       value: "`foo".to_string(),
                       msg: "Unclosed ` delimiter".to_string() })));
    }

    #[test]
    fn tokenize_identifier_test() {
        assert_eq!(tokenize("foo_bar").next(),
                   Some((0, Identifier("foo_bar".to_string()))));
        assert_eq!(tokenize("a").next(),
                   Some((0, Identifier("a".to_string()))));
        assert_eq!(tokenize("_a").next(),
                   Some((0, Identifier("_a".to_string()))));
    }

    #[test]
    fn tokenize_quoted_identifier_test() {
        assert_eq!(tokenize("\"foo\"").next(),
                   Some((0, QuotedIdentifier("foo".to_string()))));
        assert_eq!(tokenize("\"\"").next(),
                   Some((0, QuotedIdentifier("".to_string()))));
        assert_eq!(tokenize("\"a_b\"").next(),
                   Some((0, QuotedIdentifier("a_b".to_string()))));
        assert_eq!(tokenize("\"a\\nb\"").next(),
                   Some((0, QuotedIdentifier("a\nb".to_string()))));
        assert_eq!(tokenize("\"a\\\\nb\"").next(),
                   Some((0, QuotedIdentifier("a\\nb".to_string()))));
    }

    #[test]
    fn tokenize_raw_string_test() {
        assert_eq!(tokenize("'foo'").next(),
                   Some((0, Literal(Rc::new(Variable::String("foo".to_string()))))));
        assert_eq!(tokenize("''").next(),
                   Some((0, Literal(Rc::new(Variable::String("".to_string()))))));
        assert_eq!(tokenize("'a\\nb'").next(),
                   Some((0, Literal(Rc::new(Variable::String("a\\nb".to_string()))))));
    }

    #[test]
    fn tokenize_literal_test() {
        // Must enclose in quotes. See JEP 12.
        assert_eq!(tokenize("`a`").next(),
                   Some((0, Error {
                       value: "`a`".to_string(),
                       msg: "Unable to parse literal JSON: SyntaxError(\"invalid syntax\", 1, 1)"
                             .to_string() })));
        assert_eq!(tokenize("`\"a\"`").next(),
                   Some((0, Literal(Rc::new(Variable::String("a".to_string()))))));
        assert_eq!(tokenize("`\"a b\"`").next(),
                   Some((0, Literal(Rc::new(Variable::String("a b".to_string()))))));
    }

    #[test]
    fn tokenize_number_test() {
        assert_eq!(tokenize("0").next(), Some((0, Number(0))));
        assert_eq!(tokenize("1").next(), Some((0, Number(1))));
        assert_eq!(tokenize("123").next(), Some((0, Number(123))));
    }

    #[test]
    fn tokenize_negative_number_test() {
        assert_eq!(tokenize("-10").next(), Some((0, Number(-10))));
    }

    #[test]
    fn tokenize_negative_number_test_failure() {
        assert_eq!(tokenize("-01").next(), Some((0, Error {
            value: "-".to_string(),
            msg: "Negative sign must be followed by numbers 1-9".to_string() })));
    }

    #[test]
    fn tokenize_successive_test() {
        let expr = "foo.bar || `\"a\"` | 10";
        let mut tokens = tokenize(expr);
        assert_eq!(tokens.next(), Some((0, Identifier("foo".to_string()))));
        assert_eq!(tokens.next(), Some((3, Dot)));
        assert_eq!(tokens.next(), Some((4, Identifier("bar".to_string()))));
        assert_eq!(tokens.next(), Some((8, Or)));
        assert_eq!(tokens.next(), Some((11, Literal(Rc::new(Variable::String("a".to_string()))))));
        assert_eq!(tokens.next(), Some((17, Pipe)));
        assert_eq!(tokens.next(), Some((19, Number(10))));
        assert_eq!(tokens.next(), Some((21, Eof)));
        assert_eq!(tokens.next(), None);
    }

    #[test]
    fn tokenizes_slices() {
        let tokens: Vec<(usize, Token)> = tokenize("foo[0::-1]").collect();
        assert_eq!("[(0, Identifier(\"foo\")), (3, Lbracket), (4, Number(0)), (5, Colon), \
                     (6, Colon), (7, Number(-1)), (9, Rbracket), (10, Eof)]",
                   format!("{:?}", tokens));
    }
}
