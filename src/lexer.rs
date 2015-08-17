//! Module for tokenizing JMESPath expression.

extern crate rustc_serialize;

use std::iter::Peekable;
use std::str::CharIndices;
use self::rustc_serialize::json::Json;

use self::Token::*;

/// Tokenizes a JMESPath expression
///
/// This function returns a Lexer iterator that yields Tokens.
pub fn tokenize(expr: &str) -> Lexer {
    Lexer::new(expr)
}

/// Represents a lexical token of a JMESPath expression.
///
/// Each token is either a simple token that represents a known
/// character span (e.g., Token::Dot), or a token that spans multiple
/// characters. Tokens that span multiple characters are struct-like
/// variants. Tokens that contain a variable number of characters
/// that are not always equal to the token value contain a `span`
/// attribute. This attribute represents the actual length of the
/// matched lexeme.
///
/// The Identifier token does not need a lexme because the lexeme is
/// exactly the same as the token value.
#[derive(Clone, PartialEq, Debug)]
pub enum Token {
    Identifier(String),
    QuotedIdentifier(String),
    Number(i32),
    Literal(Json),
    Unknown { value: String, hint: String },
    Dot,
    Star,
    Flatten,
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
    /// Gets the string name of the token.
    pub fn token_name(&self) -> String {
        match *self {
            Identifier(_) => "Identifier".to_string(),
            QuotedIdentifier(_) => "Identifier".to_string(),
            Number(_) => "Number".to_string(),
            Literal(_) => "Literal".to_string(),
            Unknown { .. } => "Unknown".to_string(),
            _ => format!("{:?}", self)
        }
    }

    /// Provides the left binding power of the token.
    #[inline]
    pub fn lbp(&self) -> usize {
        match *self {
            Pipe     => 1,
            Eq       => 2,
            Gt       => 2,
            Lt       => 2,
            Gte      => 2,
            Lte      => 2,
            Ne       => 2,
            Or       => 5,
            Flatten  => 6,
            Star     => 20,
            Filter   => 20,
            Dot      => 40,
            Lbrace   => 50,
            Lbracket => 55,
            Lparen   => 60,
            _        => 0,
        }
    }

    /// Returns true if the token is a number token.
    pub fn is_number(&self) -> bool {
        match *self {
            Number(_) => true,
            _ => false
        }
    }
}

/// The lexer is used to tokenize JMESPath expressions.
///
/// A lexer implements Iterator and yields Tokens.
pub struct Lexer<'a> {
    // Iterator over the characters in the string.
    iter: Peekable<CharIndices<'a>>,
    // Whether or not an EOF token has been returned.
    sent_eof: bool,
    // Last position in the iterator.
    last_position: usize,
}

impl<'a> Lexer<'a> {
    // Constructs a new lexer using the given expression string.
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
        let lexeme = self.consume_while(|c| {
            match c {
                'a' ... 'z' | 'A' ... 'Z' | '_' | '0' ... '9' => true,
                _ => false
            }
        });
        Identifier(lexeme)
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
            _ => Unknown {
                value: "-".to_string(),
                hint: "Negative sign must be followed by numbers 1-9".to_string()
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
        Unknown {
            value: wrapper.to_string() + buffer.as_ref(),
            hint: format!("Unclosed {} delimiter", wrapper)
        }
    }

    // Consume and parse a quoted identifier token.
    #[inline]
    fn consume_quoted_identifier(&mut self) -> Token {
        self.consume_inside('"', |s| {
            // JSON decode the string to expand escapes
            match Json::from_str(format!(r##""{}""##, s).as_ref()) {
                // Convert the JSON value into a string literal.
                Ok(j) => QuotedIdentifier(j.as_string().unwrap().to_string()),
                Err(e) => Unknown {
                    value: format!(r#""{}""#, s),
                    hint: format!("Unable to parse JSON value in quoted identifier: {}", e)
                }
            }
        })
    }

    #[inline]
    fn consume_raw_string(&mut self) -> Token {
        self.consume_inside('\'', |s| Literal(Json::String(s)))
    }

    // Consume and parse a literal JSON token.
    #[inline]
    fn consume_literal(&mut self) -> Token {
        self.consume_inside('`', |s| {
            match Json::from_str(s.as_ref()) {
                Ok(j) => Literal(j),
                Err(err) => Unknown {
                    value: format!("`{}`", s),
                    hint: format!("Unable to parse literal JSON: {}", err)
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
                None if self.sent_eof => return None,
                None => { self.sent_eof = true; return Some((self.last_position, Eof)); },
                Some(&(pos, ch)) => {
                    match ch {
                        // Skip whitespace tokens
                        ' ' | '\n' | '\t' | '\r' => {
                            self.iter.next();
                            continue;
                        },
                        '[' => tok!((pos, self.consume_lbracket())),
                        '.' => tok!((pos, Dot)),
                        '*' => tok!((pos, Star)),
                        '|' => tok!((pos, self.alt(&'|', Or, Pipe))),
                        'a' ... 'z' | 'A' ... 'Z' | '_' =>
                            return Some((pos, self.consume_identifier())),
                        '@' => tok!((pos, At)),
                        ']' => tok!((pos, Rbracket)),
                        '{' => tok!((pos, Lbrace)),
                        '}' => tok!((pos, Rbrace)),
                        '&' => tok!((pos, Ampersand)),
                        '(' => tok!((pos, Lparen)),
                        ')' => tok!((pos, Rparen)),
                        ',' => tok!((pos, Comma)),
                        ':' => tok!((pos, Colon)),
                        '"' => return Some((pos, self.consume_quoted_identifier())),
                        '\'' => return Some((pos, self.consume_raw_string())),
                        '`' => return Some((pos, self.consume_literal())),
                        '>' => tok!((pos, self.alt(&'=', Gte, Gt))),
                        '<' => tok!((pos, self.alt(&'=', Lte, Lt))),
                        '!' => tok!((pos, self.alt(&'=', Ne, Not))),
                        '=' => tok!((pos, self.alt(&'=', Eq, Unknown {
                                value: '='.to_string(),
                                hint: "Did you mean \"==\"?".to_string() }))),
                        '-' => return Some((pos, self.consume_negative_number())),
                        '0' ... '9' => return Some((pos, self.consume_number(false))),
                        c @ _ => tok!((pos, Unknown {
                            value: c.to_string(),
                            hint: "".to_string()
                        }))
                    }
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use super::Token::*;
    use super::rustc_serialize::json::Json;

    #[test] fn tokenize_basic_test() {
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

    #[test] fn tokenize_lbracket_test() {
        assert_eq!(tokenize("[").next(), Some((0, Lbracket)));
        assert_eq!(tokenize("[]").next(), Some((0, Flatten)));
        assert_eq!(tokenize("[?").next(), Some((0, Filter)));
    }

    #[test] fn tokenize_pipe_test() {
        assert!(tokenize("|").next() == Some((0, Pipe)));
        assert!(tokenize("||").next() == Some((0, Or)));
    }

    #[test] fn tokenize_lt_gt_test() {
        assert!(tokenize("<").next() == Some((0, Lt)));
        assert!(tokenize("<=").next() == Some((0, Lte)));
        assert!(tokenize(">").next() == Some((0, Gt)));
        assert!(tokenize(">=").next() == Some((0, Gte)));
    }

    #[test] fn tokenize_eq_ne_test() {
        assert_eq!(tokenize("=").next(),
                   Some((0, Unknown {
                       value: "=".to_string(),
                       hint: "Did you mean \"==\"?".to_string() })));
        assert!(tokenize("==").next() == Some((0, Eq)));
        assert!(tokenize("!").next() == Some((0, Not)));
        assert!(tokenize("!=").next() == Some((0, Ne)));
    }

    #[test] fn skips_whitespace() {
        let mut tokens = tokenize(" \t\n\r\t. (");
        assert_eq!(tokens.next(), Some((5, Dot)));
        assert_eq!(tokens.next(), Some((7, Lparen)));
    }

    #[test] fn tokenize_single_unknown_test() {
        assert_eq!(tokenize("~").next(),
                   Some((0, Unknown {
                       value: "~".to_string(),
                       hint: "".to_string() })));
    }

    #[test] fn tokenize_unclosed_unknowns_test() {
        assert_eq!(tokenize("\"foo").next(),
                   Some((0, Unknown {
                       value: "\"foo".to_string(),
                       hint: "Unclosed \" delimiter".to_string() })));
        assert_eq!(tokenize("`foo").next(),
                   Some((0, Unknown {
                       value: "`foo".to_string(),
                       hint: "Unclosed ` delimiter".to_string() })));
    }

    #[test] fn tokenize_identifier_test() {
        assert_eq!(tokenize("foo_bar").next(),
                   Some((0, Identifier("foo_bar".to_string()))));
        assert_eq!(tokenize("a").next(),
                   Some((0, Identifier("a".to_string()))));
        assert_eq!(tokenize("_a").next(),
                   Some((0, Identifier("_a".to_string()))));
    }

    #[test] fn tokenize_quoted_identifier_test() {
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

    #[test] fn tokenize_raw_string_test() {
        assert_eq!(tokenize("'foo'").next(),
                   Some((0, Literal(Json::String("foo".to_string())))));
        assert_eq!(tokenize("''").next(),
                   Some((0, Literal(Json::String("".to_string())))));
        assert_eq!(tokenize("'a\\nb'").next(),
                   Some((0, Literal(Json::String("a\\nb".to_string())))));
    }

    #[test] fn tokenize_literal_test() {
        // Must enclose in quotes. See JEP 12.
        assert_eq!(tokenize("`a`").next(),
                   Some((0, Unknown {
                       value: "`a`".to_string(),
                       hint: "Unable to parse literal JSON: SyntaxError(\"invalid syntax\", 1, 1)"
                             .to_string() })));
        assert_eq!(tokenize("`\"a\"`").next(),
                   Some((0, Literal(Json::String("a".to_string())))));
        assert_eq!(tokenize("`\"a b\"`").next(),
                   Some((0, Literal(Json::String("a b".to_string())))));
    }

    #[test] fn tokenize_number_test() {
        assert_eq!(tokenize("0").next(), Some((0, Number(0))));
        assert_eq!(tokenize("1").next(), Some((0, Number(1))));
        assert_eq!(tokenize("123").next(), Some((0, Number(123))));
    }

    #[test] fn tokenize_negative_number_test() {
        assert_eq!(tokenize("-10").next(), Some((0, Number(-10))));
    }

    #[test] fn tokenize_negative_number_test_failure() {
        assert_eq!(tokenize("-01").next(), Some((0, Unknown {
            value: "-".to_string(),
            hint: "Negative sign must be followed by numbers 1-9".to_string() })));
    }

    #[test] fn tokenize_successive_test() {
        let expr = "foo.bar || `\"a\"` | 10";
        let mut tokens = tokenize(expr);
        assert_eq!(tokens.next(), Some((0, Identifier("foo".to_string()))));
        assert_eq!(tokens.next(), Some((3, Dot)));
        assert_eq!(tokens.next(), Some((4, Identifier("bar".to_string()))));
        assert_eq!(tokens.next(), Some((8, Or)));
        assert_eq!(tokens.next(), Some((11, Literal(Json::String("a".to_string())))));
        assert_eq!(tokens.next(), Some((17, Pipe)));
        assert_eq!(tokens.next(), Some((19, Number(10))));
        assert_eq!(tokens.next(), Some((21, Eof)));
        assert_eq!(tokens.next(), None);
    }

    #[test] fn token_has_lbp_test() {
        assert!(0 == Rparen.lbp());
        assert!(1 == Pipe.lbp());
        assert!(60 == Lparen.lbp());
    }

    #[test] fn returns_token_name_test() {
        assert_eq!("Identifier",
                   Identifier("a".to_string()).token_name());
        assert_eq!("Number", Number(0).token_name());
        assert_eq!("Literal",
                   Literal(Json::String("a".to_string())).token_name());
        assert_eq!("Unknown",
                   Unknown { value: "".to_string(), hint: "".to_string() }.token_name());
        assert_eq!("Dot".to_string(), Dot.token_name());
    }

    #[test] fn tokenizes_slices() {
        let tokens: Vec<(usize, Token)> = tokenize("foo[0::-1]").collect();
        assert_eq!("[(0, Identifier(\"foo\")), (3, Lbracket), (4, Number(0)), (5, Colon), \
                     (6, Colon), (7, Number(-1)), (9, Rbracket), (10, Eof)]",
                   format!("{:?}", tokens));
    }

    #[test] fn determines_if_number() {
        assert_eq!(true, Token::Number(10).is_number());
        assert_eq!(false, Token::Comma.is_number());
    }
}
