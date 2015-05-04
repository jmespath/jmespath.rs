//! JMESPath parser and AST
extern crate rustc_serialize;

use std::iter::Peekable;
use self::rustc_serialize::json::{Json};

use ast::*;
use lexer::Lexer;
use lexer::Token;

/// Parses a JMESPath expression into an AST
pub fn parse(expr: &str) -> Result<Ast, ParseError> {
    Parser::new(expr).parse()
}

/// Encountered when an invalid JMESPath expression is parsed.
#[derive(Clone, PartialEq, Debug)]
pub struct ParseError {
    /// The error message.
    msg: String,
    /// The line number of the error.
    line: usize,
    /// The column of the error.
    col: usize,
}

impl ParseError {
    pub fn new(expr: &str, pos: usize, msg: &str) -> ParseError {
        // Find each new line and create a formatted error message.
        let mut line: usize = 0;
        let mut col: usize = 0;
        let mut buff = String::new();
        let mut placed = false;
        // Determine the line and col, and create an array to the position.
        for (i, c) in expr.chars().enumerate() {
            col += 1;
            buff.push(c);
            if c == '\n' {
                if i > pos && !placed {
                    placed = true;
                    ParseError::inject_err_pointer(&mut buff, col);
                }
                line += 1;
                col = 0;
            }
        }

        if !placed {
            ParseError::inject_err_pointer(&mut buff, col);
        }

        ParseError {
            msg: format!("Parse error at line {}, col {}; {}\n{}", line, col, msg, expr),
            line: line,
            col: col
        }
    }

    fn inject_err_pointer(buff: &mut String, col: usize) {
        buff.push('\n');
        for _ in 0..col {
            buff.push(' ');
        }
        buff.push('^');
        buff.push('\n');
    }
}

/// JMESPath parser. Returns an Ast
pub struct Parser<'a> {
    /// Peekable token stream
    stream: Peekable<Lexer<'a>>,
    /// Expression being parsed
    expr: String,
    /// The current token
    token: Token,
    /// The current character offset in the expression
    pos: usize,
}

impl<'a> Parser<'a> {
    // Constructs a new lexer using the given expression string.
    pub fn new(expr: &'a str) -> Parser<'a> {
        let mut stream = Lexer::new(expr).peekable();
        let tok0 = stream.next().unwrap();
        Parser {
            stream: stream,
            expr: expr.to_string(),
            token: tok0,
            pos: 0,
        }
    }

    /// Parses the expression into result containing an AST or ParseError.
    pub fn parse(&mut self) -> Result<Ast, ParseError> {
        let result = self.expr(0);
        let token = self.stream.next();
        // After parsing the expr, we should reach the end of the stream.
        if result.is_err() || token.is_none() || token.unwrap() == Token::Eof {
            result
        } else {
            Err(self.err(&"Did not reach token stream EOF"))
        }
    }

    /// Ensures that the next token in the token stream is one of the pipe
    /// separated token named provided as the edible argument (e.g.,
    /// "Identifier|Eof").
    fn expect(&mut self, edible: &str) -> Result<Ast, ParseError> {
        self.advance();
        // Get the string name of the token.
        if edible.contains(&self.token.token_to_string()) {
            Ok(CurrentNode)
        } else {
            Err(self.err(&format!("Expected {:?}", edible)))
        }
    }

    /// Advances the cursor position, skipping any whitespace encountered.
    #[inline]
    fn advance(&mut self) {
        loop {
            self.pos += self.token.size();
            match self.stream.next() {
                None => break,
                Some(Token::Whitespace) => continue,
                tok @ _ => { self.token = tok.unwrap(); break }
            }
        }
    }

    /// Main parse function of the Pratt parser that parses while RBP < LBP
    pub fn expr(&mut self, rbp: usize) -> Result<Ast, ParseError> {
        // Parse the nud token.
        let mut left = match self.token.clone() {
            Token::At               => self.nud_at(),
            Token::Identifier(s, _) => self.nud_identifier(s),
            Token::Star             => self.nud_star(),
            Token::Lbracket         => self.nud_lbracket(),
            Token::Flatten          => self.nud_flatten(),
            Token::Literal(v, _)    => self.nud_literal(v),
            Token::Lbrace           => self.nud_lbrace(),
            Token::Ampersand        => self.nud_ampersand(),
            // Token::Filter           => self.nud_filter(),
            _ => return Err(self.token_err()),
        };

        // Parse any led tokens with a higher binding power.
        while rbp < self.token.lbp() {
            left = match self.token {
                Token::Dot      => self.led_dot(left.unwrap()),
                Token::Lbracket => self.led_lbracket(left.unwrap()),
                Token::Flatten  => self.led_flatten(left.unwrap()),
                Token::Or       => self.led_or(left.unwrap()),
                Token::Pipe     => self.led_pipe(left.unwrap()),
                Token::Lparen   => self.led_lparen(left.unwrap()),
                _ => return Err(self.token_err()),
            };
        }

        left
    }

    /// Returns a formatted ParseError with the given message.
    fn err(&self, msg: &str) -> ParseError {
        ParseError::new(&self.expr, self.pos, msg)
    }

    /// Generates a formatted parse error for an out of place token.
    fn token_err(&self) -> ParseError {
        self.err(&format!("Unexpected token: {:?}", self.token))
    }

    /// Examples: &foo
    fn nud_ampersand(&mut self) -> Result<Ast, ParseError> {
        self.advance();
        let rhs = try!(self.expr(Token::Ampersand.lbp()));
        Ok(Expref(Box::new(rhs)))
    }

    /// Examples: "@"
    fn nud_at(&mut self) -> Result<Ast, ParseError> {
        self.advance();
        Ok(Ast::CurrentNode)
    }

    /// Examples: "Foo"
    fn nud_identifier(&mut self, s: String) -> Result<Ast, ParseError> {
        self.advance();
        Ok(Ast::Identifier(s))
    }

    /// Examples: "[0]", "[*]", "[a, b]", "[0:1]", etc...
    fn nud_lbracket(&mut self) -> Result<Ast, ParseError> {
        self.advance();
        match self.token {
            Token::Number(_, _) | Token::Colon => self.parse_array_index(),
            Token::Star => {
                if self.stream.peek() != Some(&Token::Rbracket) {
                    return self.parse_multi_list();
                }
                try!(self.expect("Star"));
                self.parse_wildcard_index(CurrentNode)
            },
            _ => self.parse_multi_list()
        }
    }

    /// Examples: foo[*], foo[0], foo[:-1], etc.
    fn led_lbracket(&mut self, lhs: Ast) -> Result<Ast, ParseError> {
        try!(self.expect("Number|Colon|Star"));
        match self.token {
            Token::Number(_, _) | Token::Colon => {
                Ok(Ast::Subexpr(Box::new(lhs),
                                Box::new(try!(self.parse_array_index()))))
            },
            _ => self.parse_wildcard_index(lhs)
        }
    }

    fn nud_literal(&mut self, value: Json) -> Result<Ast, ParseError> {
        self.advance();
        Ok(Ast::Literal(value))
    }

    /// Examples: "*" (e.g., "* | *" would be a pipe containing two nud stars)
    fn nud_star(&mut self) -> Result<Ast, ParseError> {
        self.advance();
        self.parse_wildcard_values(Ast::CurrentNode)
    }

    /// Examples: "[]". Turns it into a led flatten (i.e., "@[]").
    fn nud_flatten(&mut self) -> Result<Ast, ParseError> {
        self.led_flatten(Ast::CurrentNode)
    }

    /// Example "{foo: bar, baz: `12`}"
    fn nud_lbrace(&mut self) -> Result<Ast, ParseError> {
        let mut pairs = vec![];
        loop {
            // Skip the opening brace and any encountered commas.
            self.advance();
            // Requires at least on key value pair.
            pairs.push(try!(self.parse_kvp()));
            match self.token {
                // Terminal condition is the Rbrace token "}".
                Token::Rbrace => { self.advance(); break; },
                // Skip commas as they are used to delineate kvps
                Token::Comma => continue,
                _ => return Err(self.err("Expected '}' or ','"))
            }
        }
        Ok(Ast::MultiHash(pairs))
    }

    fn parse_kvp(&mut self) -> Result<KeyValuePair, ParseError> {
        match self.token.clone() {
            Token::Identifier(name, _) => {
                try!(self.expect("Colon"));
                self.advance();
                Ok(KeyValuePair {
                    key: Box::new(Ast::Literal(Json::String(name))),
                    value: Box::new(try!(self.expr(0)))
                })
            },
            _ => Err(self.err("Expected Identifier to start key value pair"))
        }
    }

    /// Creates a Projection AST node for a flatten token.
    fn led_flatten(&mut self, lhs: Ast) -> Result<Ast, ParseError> {
        let rhs = try!(self.projection_rhs(Token::Flatten.lbp()));
        Ok(Ast::ArrayProjection(
            Box::new(Ast::Flatten(Box::new(lhs))),
            Box::new(rhs)
        ))
    }

    fn led_dot(&mut self, left: Ast) -> Result<Ast, ParseError> {
        let rhs = try!(self.parse_dot(Token::Dot.lbp()));
        Ok(Ast::Subexpr(Box::new(left), Box::new(rhs)))
    }

    fn led_or(&mut self, left: Ast) -> Result<Ast, ParseError> {
        self.advance();
        let rhs = try!(self.expr(Token::Or.lbp()));
        Ok(Ast::Or(Box::new(left), Box::new(rhs)))
    }

    fn led_lparen(&mut self, lhs: Ast) -> Result<Ast, ParseError> {
        let fname: String;
        match lhs {
            Ast::Identifier(v) => fname = v,
            _ => return Err(self.err("Functions must be preceded by an identifier"))
        }
        self.advance();
        Ok(Ast::Function(fname, try!(self.parse_list(Token::Rparen))))
    }

    fn led_pipe(&mut self, left: Ast) -> Result<Ast, ParseError> {
        self.advance();
        let rhs = try!(self.expr(Token::Pipe.lbp()));
        Ok(Ast::Subexpr(Box::new(left), Box::new(rhs)))
    }

    /// Parses the right hand side of a dot expression.
    fn parse_dot(&mut self, lbp: usize) -> Result<Ast, ParseError> {
        try!(self.expect("Identifier|Star|Lbrace|Lbracket|Ampersand|Filter"));
        match self.token {
            Token::Lbracket => { self.advance(); self.parse_multi_list() },
            _ => self.expr(lbp)
        }
    }

    /// Parses the right hand side of a projection, using the given LBP to
    /// determine when to stop consuming tokens.
    fn projection_rhs(&mut self, lbp: usize) -> Result<Ast, ParseError> {
        if self.token.lbp() < 10 {
            return Ok(CurrentNode);
        }
        match self.token {
            Token::Dot      => self.parse_dot(lbp),
            Token::Lbracket => self.expr(lbp),
            Token::Filter   => self.expr(lbp),
            _               => Err(self.token_err())
        }
    }

    /// Creates a projection for "[*]"
    fn parse_wildcard_index(&mut self, lhs: Ast) -> Result<Ast, ParseError> {
        try!(self.expect("Rbracket"));
        let rhs = try!(self.projection_rhs(Token::Star.lbp()));
        Ok(Ast::ArrayProjection(Box::new(lhs), Box::new(rhs)))
    }

    /// Creates a projection for "*"
    fn parse_wildcard_values(&mut self, lhs: Ast) -> Result<Ast, ParseError> {
        let rhs = try!(self.projection_rhs(Token::Star.lbp()));
        Ok(Ast::ObjectProjection(Box::new(lhs), Box::new(rhs)))
    }

    /// Parses [0], [::-1], [0:-1], [0:1], etc...
    fn parse_array_index(&mut self) -> Result<Ast, ParseError> {
        let mut parts = [None, None, None];
        let mut pos = 0;
        loop {
            match self.token {
                Token::Colon => {
                    pos += 1;
                    if pos > 2 {
                        return Err(self.err("Too many colons in slice expr"));
                    }
                    try!(self.expect("Number|Colon|Rbracket"));
                },
                Token::Number(value, _) => {
                    parts[pos] = Some(value);
                    try!(self.expect("Colon|Rbracket"));
                },
                Token::Rbracket => { self.advance(); break; },
                _ => return Err(self.token_err()),
            }
        }

        if pos == 0 {
            // No colons were found, so this is a simple index extraction.
            Ok(Ast::Index(parts[0].unwrap()))
        } else {
            // Sliced array from start (e.g., [2:])
            let lhs = Ast::Slice(parts[0], parts[1], parts[2]);
            let rhs = try!(self.projection_rhs(Token::Star.lbp()));
            Ok(Ast::ArrayProjection(Box::new(lhs), Box::new(rhs)))
        }
    }

    /// Parses multi-select lists (e.g., "[foo, bar, baz]")
    fn parse_multi_list(&mut self) -> Result<Ast, ParseError> {
        Ok(Ast::MultiList(try!(self.parse_list(Token::Rbracket))))
    }

    /// Parse a comma separated list of expressions until a closing token or
    /// error. This function is used for functions and multi-list parsing.
    fn parse_list(&mut self, closing: Token) -> Result<Vec<Box<Ast>>, ParseError> {
        let mut nodes = vec![];
        loop {
            nodes.push(Box::new(try!(self.expr(0))));
            if self.token == closing {
                break;
            } else if self.token == Token::Comma {
                self.advance();
            }
        }
        self.advance();
        Ok(nodes)
    }
}

#[cfg(test)]
mod test {
    extern crate rustc_serialize;
    use super::*;
    use ast::*;
    use self::rustc_serialize::json::{Json};

    #[test] fn indentifier_test() {
        assert_eq!(parse("foo").unwrap(),
                   Ast::Identifier("foo".to_string()));
    }

    #[test] fn current_node_test() {
        assert_eq!(parse("@").unwrap(), Ast::CurrentNode);
    }

    #[test] fn wildcard_values_test() {
        assert_eq!(parse("*").unwrap(),
                   Ast::ObjectProjection(Box::new(Ast::CurrentNode),
                                         Box::new(Ast::CurrentNode)));
    }

    #[test] fn dot_test() {
        assert_eq!(parse("@.b").unwrap(),
                  Ast::Subexpr(Box::new(Ast::CurrentNode),
                               ident(&"b")));
    }

    #[test] fn ensures_nud_token_is_valid_test() {
        let result = parse(",");
        assert!(result.is_err());
        assert!(result.err().unwrap().msg.contains("Unexpected token: Comma"));
    }

    #[test] fn multi_list_test() {
        let l = MultiList(vec![ident(&"a"), ident(&"b")]);
        assert_eq!(parse("[a, b]").unwrap(), l);
    }

    #[test] fn multi_list_unclosed() {
        let result = parse("[a, b");
        assert!(result.is_err());
        assert!(result.err().unwrap().msg.contains("Unexpected token"));
    }

    #[test] fn multi_list_unclosed_after_comma() {
        let result = parse("[a,");
        assert!(result.is_err());
        assert!(result.err().unwrap().msg.contains("Unexpected token"));
    }

    #[test] fn multi_list_after_dot_test() {
        let l = Ast::MultiList(vec![ident(&"a"), ident(&"b")]);
        assert_eq!(parse("@.[a, b]").unwrap(),
                   Ast::Subexpr(Box::new(Ast::CurrentNode),
                                Box::new(l)));
    }

    #[test] fn parses_simple_index_extractions_test() {
        assert_eq!(parse("[0]").unwrap(), Ast::Index(0));
    }

    #[test] fn parses_single_element_slice_test() {
        assert_eq!(parse("[-1:]").unwrap(),
                   Ast::ArrayProjection(Box::new(Ast::Slice(Some(-1), None, None)),
                                        Box::new(Ast::CurrentNode)));
    }

    #[test] fn parses_double_element_slice_test() {
        assert_eq!(parse("[1:-1].a").unwrap(),
                   Ast::ArrayProjection(Box::new(Ast::Slice(Some(1), Some(-1), None)),
                                        ident(&"a")));
    }

    #[test] fn parses_revese_slice_test() {
        assert_eq!(parse("[::-1].a").unwrap(),
                   Ast::ArrayProjection(Box::new(Ast::Slice(None, None, Some(-1))),
                                        ident(&"a")));
    }

    #[test] fn parses_or_test() {
        let result = Ast::Or(ident(&"a"), ident(&"b"));
        assert_eq!(parse("a || b").unwrap(), result);
    }

    #[test] fn parses_pipe_test() {
        let result = Ast::Subexpr(ident(&"a"), ident(&"b"));
        assert_eq!(parse("a | b").unwrap(), result);
    }

    #[test] fn parses_literal_token_test() {
        assert_eq!(parse("`\"foo\"`").unwrap(),
                   Ast::Literal(Json::String("foo".to_string())))
    }

    #[test] fn parses_multi_hash() {
        let result = MultiHash(vec![
            KeyValuePair {
                key: Box::new(Ast::Literal(Json::String("foo".to_string()))),
                value: ident(&"bar")
            },
            KeyValuePair {
                key: Box::new(Ast::Literal(Json::String("baz".to_string()))),
                value: ident(&"bam")
            }
        ]);
        assert_eq!(parse("{foo: bar, baz: bam}").unwrap(), result);
    }

    #[test] fn parses_functions() {
        let r = Ast::Function("length".to_string(), vec![ident(&"a")]);
        assert_eq!(parse("length(a)").unwrap(), r);
    }

    #[test] fn parses_expref() {
        let result = Ast::Expref(ident(&"foo"));
        assert_eq!(parse("&foo").unwrap(), result);
    }

    fn ident(name: &str) -> Box<Ast> {
        Box::new(Ast::Identifier(name.to_string()))
    }
}
