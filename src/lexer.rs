//! Lexer is an iterator that yields Token enums.
extern crate rustc_serialize;

use std::str::Chars;
use std::iter::Peekable;
use self::rustc_serialize::json::Json;

pub use self::Token::*;

/// Tokenizes a JMESPath expression into a stream of tokens.
pub fn tokenize(expr: &str) -> Lexer {
    Lexer::new(expr)
}

/// Represents a lexical token of a JMESPath expression.
#[derive(Clone, PartialEq, Debug)]
pub enum Token {
    // The parsed value followed by the original token length
    Identifier(String, usize),
    // The parsed value followed by the original token length
    Number(i32, usize),
    // The parsed value followed by the original token length
    Literal(Json, usize),
    // Contains the unknown string that was encountered
    Unknown(String),
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
            Identifier(_, _) => "Identifier".to_string(),
            Number(_, _)     => "Number".to_string(),
            Literal(_, _)    => "Literal".to_string(),
            Unknown(_)       => "Unknown".to_string(),
            _                => format!("{:?}", self)
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

    /// Provides the lexeme length of a token.
    pub fn len(&self) -> usize {
        match *self {
            Identifier(_, len) => len,
            Number(_, len)     => len,
            Literal(_, len)    => len,
            Unknown(ref s)     => s.len(),
            Filter             => 2,
            Flatten            => 2,
            Eof                => 0,
            _                  => 1,
        }
    }
}

/// The lexer is used to tokenize JMESPath expressions.
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

    // Consumes from the char iterator while the predicate function returns
    // true and there are peekable tokens. Returns a string buffer of the
    /// consumed characters.
    #[inline]
    fn consume_while<F>(&mut self, predicate: F) -> String
        where F: Fn(char) -> bool {
        let mut buffer = self.iter.next().unwrap().to_string();
        loop {
            match self.iter.peek() {
                None => break,
                Some(&c) if !predicate(c) => break,
                Some(&c) => { buffer.push(c); self.iter.next(); }
            }
        }
        buffer
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
        let len = lexeme.len();
        Identifier(lexeme, len)
    }

    // Consumes numbers: *"-" "0" / ( %x31-39 *DIGIT )
    fn consume_number(&mut self, is_negative: bool) -> Token {
        let lexeme = self.consume_while(|c| c.is_digit(10));
        match lexeme.parse() {
            Ok(n) if is_negative => Number(n * -1, lexeme.len() + 1),
            Ok(n) => Number(n, lexeme.len()),
            _     => Unknown(lexeme)
        }
    }

    // Consumes a negative number
    fn consume_negative_number(&mut self) -> Token {
        // Skip the "-" number token.
        self.iter.next();
        // Ensure that the next value is a number > 0
        match self.iter.peek() {
            Some(&c) if c >= '1' && c <= '9' => self.consume_number(true),
            Some(&c) => { self.iter.next(); Unknown(format!("-{}", c)) },
            None => Unknown("-".to_string()),
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
        Unknown(wrapper.to_string() + buffer.as_ref())
    }

    // Consume and parse a quoted identifier token.
    fn consume_quoted_identifier(&mut self) -> Token {
        self.consume_inside('"', |s| {
            // JSON decode the string to expand escapes
            match Json::from_str(format!(r##""{}""##, s).as_ref()) {
                // Convert the JSON value into a string literal.
                Ok(j)  => Identifier(j.as_string().unwrap().to_string(), s.len() + 2),
                Err(_) => Unknown(format!(r#""{}""#, s))
            }
        })
    }

    fn consume_raw_string(&mut self) -> Token {
        self.consume_inside('\'', |s| Literal(Json::String(s.clone()), s.len() + 2))
    }

    // Consume and parse a literal JSON token.
    fn consume_literal(&mut self) -> Token {
        self.consume_inside('`', |s| {
            match Json::from_str(s.as_ref()) {
                Ok(j)  => Literal(j, s.len() + 2),
                Err(_) => Unknown(format!("`{}`", s))
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
                    '=' => tok!(self.alt(&'=', Eq, Unknown('='.to_string()))),
                    '!' => tok!(self.alt(&'=', Ne, Not)),
                    ' ' | '\n' | '\t' | '\r' => tok!(Whitespace),
                    'a' ... 'z' | 'A' ... 'Z' | '_' => Some(self.consume_identifier()),
                    '0' ... '9' => Some(self.consume_number(false)),
                    '-' => Some(self.consume_negative_number()),
                    '"' => Some(self.consume_quoted_identifier()),
                    '\'' => Some(self.consume_raw_string()),
                    '`' => Some(self.consume_literal()),
                    _ => tok!(Unknown(c.to_string()))
                }
            },
            None if self.sent_eof => None,
            _ => { self.sent_eof = true;  Some(Eof) }
        }
    }
}

#[cfg(test)]
mod test {
    extern crate rustc_serialize;
    use super::*;
    use self::rustc_serialize::json::{Json};

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
        assert!(tokenize("==").next() == Some(Eq));
        assert!(tokenize("=").next() == Some(Unknown("=".to_string())));
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
        assert!(tokenize("~").next() == Some(Unknown("~".to_string())));
        assert!(tokenize("\"foo").next() == Some(Unknown("\"foo".to_string())));
    }

    #[test] fn tokenize_unclosed_unknowns_test() {
        assert!(tokenize("\"foo").next() == Some(Unknown("\"foo".to_string())));
        assert!(tokenize("`foo").next() == Some(Unknown("`foo".to_string())));
    }

    #[test] fn tokenize_identifier_test() {
        assert!(tokenize("foo_bar").next() == Some(Identifier("foo_bar".to_string(), 7)));
        assert!(tokenize("a").next() == Some(Identifier("a".to_string(), 1)));
        assert!(tokenize("_a").next() == Some(Identifier("_a".to_string(), 2)));
    }

    #[test] fn tokenize_quoted_identifier_test() {
        assert!(tokenize("\"foo\"").next() == Some(Identifier("foo".to_string(), 5)));
        assert!(tokenize("\"\"").next() == Some(Identifier("".to_string(), 2)));
        assert!(tokenize("\"a_b\"").next() == Some(Identifier("a_b".to_string(), 5)));
        assert!(tokenize("\"a\\nb\"").next() == Some(Identifier("a\nb".to_string(), 6)));
        assert!(tokenize("\"a\\\\nb\"").next() == Some(Identifier("a\\nb".to_string(), 7)));
    }

    #[test] fn tokenize_raw_string_test() {
        assert!(tokenize("'foo'").next() == Some(Literal(Json::String("foo".to_string()), 5)));
        assert!(tokenize("''").next() == Some(Literal(Json::String("".to_string()), 2)));
        assert!(tokenize("'a\\nb'").next() == Some(Literal(Json::String("a\\nb".to_string()), 6)));
    }

    #[test] fn tokenize_literal_test() {
        // Must enclose in quotes. See JEP 12.
        assert!(tokenize("`a`").next() == Some(Unknown("`a`".to_string())));
        assert!(tokenize("`\"a\"`").next() == Some(Literal(Json::String("a".to_string()), 5)));
        assert!(tokenize("`\"a b\"`").next() == Some(Literal(Json::String("a b".to_string()), 7)));
    }

    #[test] fn tokenize_number_test() {
        assert!(tokenize("0").next() == Some(Number(0, 1)));
        assert!(tokenize("1").next() == Some(Number(1, 1)));
        assert!(tokenize("123").next() == Some(Number(123, 3)));
        assert!(tokenize("-10").next() == Some(Number(-10, 3)));
        assert!(tokenize("-01").next() == Some(Unknown("-0".to_string())));
    }

    #[test] fn tokenize_successive_test() {
        let expr = "foo.bar || `\"a\"` | 10";
        let mut tokens = tokenize(expr);
        assert!(tokens.next() == Some(Identifier("foo".to_string(), 3)));
        assert!(tokens.next() == Some(Dot));
        assert!(tokens.next() == Some(Identifier("bar".to_string(), 3)));
        assert!(tokens.next() == Some(Whitespace));
        assert!(tokens.next() == Some(Or));
        assert!(tokens.next() == Some(Whitespace));
        assert!(tokens.next() == Some(Literal(Json::String("a".to_string()), 5)));
        assert!(tokens.next() == Some(Whitespace));
        assert!(tokens.next() == Some(Pipe));
        assert!(tokens.next() == Some(Whitespace));
        assert!(tokens.next() == Some(Number(10, 2)));
        assert!(tokens.next() == Some(Eof));
        assert!(tokens.next() == None);
    }

    #[test] fn token_has_size_test() {
        assert!(1 == Rparen.len());
        assert!(2 == Flatten.len());
        assert!(2 == Filter.len());
        assert!(3 == Identifier("abc".to_string(), 3).len());
        assert!(2 == Number(11, 2).len());
        assert!(4 == Unknown("test".to_string()).len());
    }

    #[test] fn token_has_lbp_test() {
        assert!(0 == Rparen.lbp());
        assert!(1 == Pipe.lbp());
        assert!(60 == Lparen.lbp());
    }

    #[test] fn returns_token_name_test() {
        assert_eq!("Identifier", Identifier("a".to_string(), 1).token_name());
        assert_eq!("Number", Number(0, 1).token_name());
        assert_eq!("Literal", Literal(Json::String("a".to_string()), 5).token_name());
        assert_eq!("Unknown", Unknown("".to_string()).token_name());
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
}
