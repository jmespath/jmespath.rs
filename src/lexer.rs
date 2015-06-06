//! Creates JMESPath token streams.
//!
//! Use the `tokenize()` function to tokenize JMESPath expressions into a
//! stream of `jmespath::lexer::Token` variants.
//!
//! # Examples
//!
//! The following example tokenizes a JMESPath expression and iterates over
//! each token. Tokens have a `token_name()`, `lbp()`, `is_whitespace()`
//! and `span()` method.
//!
//! ```
//! use jmespath::lexer::tokenize;
//!
//! let lexer = tokenize("foo.bar");
//! for token in lexer {
//!     println!("{}, {}", token.token_name(), token.span());
//! }
//! ```

extern crate rustc_serialize;

use std::str::Chars;
use std::iter::Peekable;
use self::rustc_serialize::json::Json;

pub use self::Token::*;

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
    Identifier { value: String },
    QuotedIdentifier { value: String, span: usize },
    Number { value: i32, span: usize },
    Literal { value: Json, span: usize },
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
    Whitespace,
    Eof,
}

impl Token {
    /// Gets the string name of the token.
    pub fn token_name(&self) -> String {
        match *self {
            Identifier { .. } => "Identifier".to_string(),
            Number { .. } => "Number".to_string(),
            Literal { .. } => "Literal".to_string(),
            Unknown {.. } => "Unknown".to_string(),
            _ => format!("{:?}", self)
        }
    }

    /// Provides the left binding power of the token.
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

    /// Provides the number of characters a token lexem spans.
    pub fn span(&self) -> usize {
        match *self {
            Identifier { ref value, .. } => value.len(),
            QuotedIdentifier { span, .. } => span,
            Number { span, .. } => span,
            Literal { span, .. } => span,
            Unknown { ref value, .. } => value.len(),
            Filter => 2,
            Flatten => 2,
            Eof => 0,
            _ => 1,
        }
    }

    /// Returns `true` if the token is a whitespace token.
    pub fn is_whitespace(&self) -> bool {
        return *self == Whitespace;
    }
}

/// The lexer is used to tokenize JMESPath expressions.
///
/// A lexer implements Iterator and yields Tokens.
pub struct Lexer<'a> {
    // Iterator over the characters in the string.
    iter: Peekable<Chars<'a>>,
    // Whether or not an EOF token has been returned.
    sent_eof: bool,
}

impl<'a> Lexer<'a> {
    // Constructs a new lexer using the given expression string.
    pub fn new(expr: &'a str) -> Lexer<'a> {
        Lexer {
            iter: expr.chars().peekable(),
            sent_eof: false
        }
    }

    // Consumes "[", "[]", and "[?"
    fn consume_lbracket(&mut self) -> Token {
        match self.iter.peek() {
            Some(&']') => { self.iter.next(); Flatten },
            Some(&'?') => { self.iter.next(); Filter },
            _ => Lbracket,
        }
    }

    // Consume identifiers: ( ALPHA / "_" ) *( DIGIT / ALPHA / "_" )
    #[inline]
    fn consume_identifier(&mut self) -> Token {
        let mut lexeme = self.iter.next().unwrap().to_string();
        loop {
            match self.iter.peek() {
                None => break,
                Some(&c) => {
                    match c {
                        'a' ... 'z' | 'A' ... 'Z' | '_' | '0' ... '9' => {
                            lexeme.push(c);
                            self.iter.next();
                        }
                        _ => break
                    }
                }
            }
        }
        Identifier { value: lexeme }
    }

    // Consumes numbers: *"-" "0" / ( %x31-39 *DIGIT )
    fn consume_number(&mut self, is_negative: bool) -> Token {
        let mut lexeme = self.iter.next().unwrap().to_string();
        loop {
            match self.iter.peek() {
                Some(&c) if c.is_digit(10) => {
                    lexeme.push(c);
                    self.iter.next();
                },
                _ => break
            }
        }
        let numeric_value: i32 = lexeme.parse().unwrap();
        if is_negative {
            Number { value: numeric_value * -1, span: lexeme.len() + 1 }
        } else {
            Number { value: numeric_value, span: lexeme.len() }
        }
    }

    // Consumes a negative number
    fn consume_negative_number(&mut self) -> Token {
        // Skip the "-" number token.
        self.iter.next();
        // Ensure that the next value is a number > 0
        match self.iter.peek() {
            Some(&c) if c >= '1' && c <= '9' => self.consume_number(true),
            _ => Unknown {
                value: "-".to_string(),
                hint: "Negative sign must be followed by numbers 1-9".to_string()
            }
        }
    }

    // Consumes tokens inside of a closing character. The closing character
    // can be escaped using a "\" character.
    fn consume_inside<F>(&mut self, wrapper: char, invoke: F) -> Token
        where F: Fn(String) -> Token {
        let mut buffer = String::new();
        // Skip the opening character.
        self.iter.next();
        loop {
            match self.iter.next() {
                Some(c) if c == wrapper => return invoke(buffer),
                Some(c) if c == '\\' => {
                    buffer.push(c);
                    // Break if an escape is followed by the end of the string.
                    match self.iter.next() {
                        Some(c) => buffer.push(c),
                        None    => break
                    }
                },
                Some(c) => buffer.push(c),
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
    fn consume_quoted_identifier(&mut self) -> Token {
        self.consume_inside('"', |s| {
            // JSON decode the string to expand escapes
            match Json::from_str(format!(r##""{}""##, s).as_ref()) {
                // Convert the JSON value into a string literal.
                Ok(j) => QuotedIdentifier {
                    value: j.as_string().unwrap().to_string(),
                    span: s.len() + 2
                },
                Err(e) => Unknown {
                    value: format!(r#""{}""#, s),
                    hint: format!("Unable to parse JSON value in quoted identifier: {}", e)
                }
            }
        })
    }

    fn consume_raw_string(&mut self) -> Token {
        self.consume_inside('\'', |s| Literal {
            value: Json::String(s.clone()),
            span: s.len() + 2
        })
    }

    // Consume and parse a literal JSON token.
    fn consume_literal(&mut self) -> Token {
        self.consume_inside('`', |s| {
            match Json::from_str(s.as_ref()) {
                Ok(j)  => Literal { value: j, span: s.len() + 2 },
                Err(err) => Unknown {
                    value: format!("`{}`", s),
                    hint: format!("Unable to parse literal JSON: {}", err)
                }
            }
        })
    }

    fn alt(&mut self, expected: &char, match_type: Token, else_type: Token) -> Token {
        match self.iter.peek() {
            Some(&c) if c == *expected => {
                self.iter.next();
                match_type
            },
            _ => else_type
        }
    }
}

impl<'a> Iterator for Lexer<'a> {
    type Item = Token;
    fn next(&mut self) -> Option<Token> {
        macro_rules! tok {
            ($x:expr) => {{ self.iter.next(); Some($x) }};
        }
        match self.iter.peek() {
            Some(&c) => {
                match c {
                    '.' => tok!(Dot),
                    '*' => tok!(Star),
                    '|' => tok!(self.alt(&'|', Or, Pipe)),
                    '@' => tok!(At),
                    '[' => tok!(self.consume_lbracket()),
                    ']' => tok!(Rbracket),
                    '{' => tok!(Lbrace),
                    '}' => tok!(Rbrace),
                    '&' => tok!(Ampersand),
                    '(' => tok!(Lparen),
                    ')' => tok!(Rparen),
                    ',' => tok!(Comma),
                    ':' => tok!(Colon),
                    '>' => tok!(self.alt(&'=', Gte, Gt)),
                    '<' => tok!(self.alt(&'=', Lte, Lt)),
                    '=' => tok!(self.alt(&'=', Eq, Unknown {
                        value: '='.to_string(),
                        hint: "Did you mean \"==\"?".to_string() })),
                    '!' => tok!(self.alt(&'=', Ne, Not)),
                    ' ' | '\n' | '\t' | '\r' => tok!(Whitespace),
                    'a' ... 'z' | 'A' ... 'Z' | '_' => Some(self.consume_identifier()),
                    '0' ... '9' => Some(self.consume_number(false)),
                    '-' => Some(self.consume_negative_number()),
                    '"' => Some(self.consume_quoted_identifier()),
                    '\'' => Some(self.consume_raw_string()),
                    '`' => Some(self.consume_literal()),
                    _ => tok!(Unknown { value: c.to_string(), hint: "".to_string() })
                }
            },
            None if self.sent_eof => None,
            _ => { self.sent_eof = true;  Some(Eof) }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use super::rustc_serialize::json::Json;

    #[test] fn tokenize_basic_test() {
        assert!(tokenize(".").next() == Some(Dot));
        assert!(tokenize("*").next() == Some(Star));
        assert!(tokenize("@").next() == Some(At));
        assert!(tokenize("]").next() == Some(Rbracket));
        assert!(tokenize("{").next() == Some(Lbrace));
        assert!(tokenize("}").next() == Some(Rbrace));
        assert!(tokenize("(").next() == Some(Lparen));
        assert!(tokenize(")").next() == Some(Rparen));
        assert!(tokenize(",").next() == Some(Comma));
    }

    #[test] fn tokenize_lbracket_test() {
        assert!(tokenize("[").next() == Some(Lbracket));
        assert!(tokenize("[]").next() == Some(Flatten));
        assert!(tokenize("[?").next() == Some(Filter));
    }

    #[test] fn tokenize_pipe_test() {
        assert!(tokenize("|").next() == Some(Pipe));
        assert!(tokenize("||").next() == Some(Or));
    }

    #[test] fn tokenize_lt_gt_test() {
        assert!(tokenize("<").next() == Some(Lt));
        assert!(tokenize("<=").next() == Some(Lte));
        assert!(tokenize(">").next() == Some(Gt));
        assert!(tokenize(">=").next() == Some(Gte));
    }

    #[test] fn tokenize_eq_ne_test() {
        assert_eq!(tokenize("=").next(),
                   Some(Unknown {
                       value: "=".to_string(),
                       hint: "Did you mean \"==\"?".to_string() }));
        assert!(tokenize("==").next() == Some(Eq));
        assert!(tokenize("!").next() == Some(Not));
        assert!(tokenize("!=").next() == Some(Ne));
    }

    #[test] fn tokenize_whitespace_test() {
        assert!(tokenize(" ").next() == Some(Whitespace));
        assert!(tokenize("\t").next() == Some(Whitespace));
        assert!(tokenize("\r").next() == Some(Whitespace));
        assert!(tokenize("\n").next() == Some(Whitespace));
    }

    #[test] fn tokenize_single_unknown_test() {
        assert_eq!(tokenize("~").next(),
                   Some(Unknown {
                       value: "~".to_string(),
                       hint: "".to_string() }));
    }

    #[test] fn tokenize_unclosed_unknowns_test() {
        assert_eq!(tokenize("\"foo").next(),
                   Some(Unknown {
                       value: "\"foo".to_string(),
                       hint: "Unclosed \" delimiter".to_string() }));
        assert_eq!(tokenize("`foo").next(),
                   Some(Unknown {
                       value: "`foo".to_string(),
                       hint: "Unclosed ` delimiter".to_string() }));
    }

    #[test] fn tokenize_identifier_test() {
        assert_eq!(tokenize("foo_bar").next(),
                   Some(Identifier { value: "foo_bar".to_string() }));
        assert_eq!(tokenize("a").next(),
                   Some(Identifier { value: "a".to_string() }));
        assert_eq!(tokenize("_a").next(),
                   Some(Identifier { value: "_a".to_string() }));
    }

    #[test] fn tokenize_quoted_identifier_test() {
        assert_eq!(tokenize("\"foo\"").next(),
                   Some(QuotedIdentifier { value: "foo".to_string(), span: 5 }));
        assert_eq!(tokenize("\"\"").next(),
                   Some(QuotedIdentifier { value: "".to_string(), span: 2 }));
        assert_eq!(tokenize("\"a_b\"").next(),
                   Some(QuotedIdentifier { value: "a_b".to_string(), span: 5 }));
        assert_eq!(tokenize("\"a\\nb\"").next(),
                   Some(QuotedIdentifier { value: "a\nb".to_string(), span: 6 }));
        assert_eq!(tokenize("\"a\\\\nb\"").next(),
                   Some(QuotedIdentifier { value: "a\\nb".to_string(), span: 7 }));
    }

    #[test] fn tokenize_raw_string_test() {
        assert_eq!(tokenize("'foo'").next(),
                   Some(Literal { value: Json::String("foo".to_string()), span: 5 }));
        assert_eq!(tokenize("''").next(),
                   Some(Literal { value: Json::String("".to_string()), span: 2 }));
        assert_eq!(tokenize("'a\\nb'").next(),
                   Some(Literal { value: Json::String("a\\nb".to_string()), span: 6 }));
    }

    #[test] fn tokenize_literal_test() {
        // Must enclose in quotes. See JEP 12.
        assert_eq!(tokenize("`a`").next(),
                   Some(Unknown {
                       value: "`a`".to_string(),
                       hint: "Unable to parse literal JSON: SyntaxError(\"invalid syntax\", 1, 1)"
                             .to_string() }));
        assert_eq!(tokenize("`\"a\"`").next(),
                   Some(Literal { value: Json::String("a".to_string()), span: 5 }));
        assert_eq!(tokenize("`\"a b\"`").next(),
                   Some(Literal { value: Json::String("a b".to_string()), span: 7 }));
    }

    #[test] fn tokenize_number_test() {
        assert_eq!(tokenize("0").next(), Some(Number { value: 0, span: 1 }));
        assert_eq!(tokenize("1").next(), Some(Number { value: 1, span: 1 }));
        assert_eq!(tokenize("123").next(), Some(Number { value: 123, span: 3 }));
        assert_eq!(tokenize("-10").next(), Some(Number { value: -10, span: 3 }));
        assert_eq!(tokenize("-01").next(), Some(Unknown {
            value: "-".to_string(),
            hint: "Negative sign must be followed by numbers 1-9".to_string() }));
    }

    #[test] fn tokenize_successive_test() {
        let expr = "foo.bar || `\"a\"` | 10";
        let mut tokens = tokenize(expr);
        assert!(tokens.next() == Some(Identifier { value: "foo".to_string() }));
        assert!(tokens.next() == Some(Dot));
        assert!(tokens.next() == Some(Identifier { value: "bar".to_string() }));
        assert!(tokens.next() == Some(Whitespace));
        assert!(tokens.next() == Some(Or));
        assert!(tokens.next() == Some(Whitespace));
        assert!(tokens.next() == Some(Literal { value: Json::String("a".to_string()), span: 5 }));
        assert!(tokens.next() == Some(Whitespace));
        assert!(tokens.next() == Some(Pipe));
        assert!(tokens.next() == Some(Whitespace));
        assert!(tokens.next() == Some(Number { value: 10, span: 2 }));
        assert!(tokens.next() == Some(Eof));
        assert!(tokens.next() == None);
    }

    #[test] fn token_has_size_test() {
        assert!(1 == Rparen.span());
        assert!(2 == Flatten.span());
        assert!(2 == Filter.span());
        assert!(3 == Identifier { value: "abc".to_string() }.span());
        assert!(2 == Number { value: 11, span: 2 }.span());
        assert!(4 == Unknown { value: "test".to_string(), hint: "".to_string() }.span());
    }

    #[test] fn token_has_lbp_test() {
        assert!(0 == Rparen.lbp());
        assert!(1 == Pipe.lbp());
        assert!(60 == Lparen.lbp());
    }

    #[test] fn returns_token_name_test() {
        assert_eq!("Identifier",
                   Identifier { value: "a".to_string() }.token_name());
        assert_eq!("Number", Number { value: 0, span: 1 }.token_name());
        assert_eq!("Literal",
                   Literal { value: Json::String("a".to_string()), span: 5 }.token_name());
        assert_eq!("Unknown",
                   Unknown { value: "".to_string(), hint: "".to_string() }.token_name());
        assert_eq!("Dot".to_string(), Dot.token_name());
        assert_eq!("Star".to_string(), Star.token_name());
        assert_eq!("Flatten".to_string(), Flatten.token_name());
        assert_eq!("Or".to_string(), Or.token_name());
        assert_eq!("Pipe".to_string(), Pipe.token_name());
        assert_eq!("Filter".to_string(), Filter.token_name());
        assert_eq!("Lbracket".to_string(), Lbracket.token_name());
        assert_eq!("Rbracket".to_string(), Rbracket.token_name());
        assert_eq!("Comma".to_string(), Comma.token_name());
        assert_eq!("Colon".to_string(), Colon.token_name());
        assert_eq!("Not".to_string(), Not.token_name());
        assert_eq!("Ne".to_string(), Ne.token_name());
        assert_eq!("Eq".to_string(), Eq.token_name());
        assert_eq!("Gt".to_string(), Gt.token_name());
        assert_eq!("Gte".to_string(), Gte.token_name());
        assert_eq!("Lt".to_string(), Lt.token_name());
        assert_eq!("Lte".to_string(), Lte.token_name());
        assert_eq!("At".to_string(), At.token_name());
        assert_eq!("Ampersand".to_string(), Ampersand.token_name());
        assert_eq!("Lparen".to_string(), Lparen.token_name());
        assert_eq!("Rparen".to_string(), Rparen.token_name());
        assert_eq!("Lbrace".to_string(), Lbrace.token_name());
        assert_eq!("Rbrace".to_string(), Rbrace.token_name());
        assert_eq!("Whitespace".to_string(), Whitespace.token_name());
        assert_eq!("Eof".to_string(), Eof.token_name());
        assert_eq!("Rbracket".to_string(), Rbracket.token_name());
        assert_eq!("Lbracket".to_string(), Lbracket.token_name());
    }

    #[test] fn token_knows_if_is_whitespace_test() {
        assert!(true == Whitespace.is_whitespace());
        assert!(false == Rparen.is_whitespace());
    }
}
