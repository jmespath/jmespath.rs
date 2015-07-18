//! Module for parsing JMESPath expressions into an AST.

extern crate rustc_serialize;

use std::iter::Peekable;
use self::rustc_serialize::json::Json;

use ast::{Ast, Comparator, KeyValuePair};
use lexer::{Lexer, Token};

/// An alias for computations that can return an `Ast` or `ParseError`.
pub type ParseResult = Result<Ast, ParseError>;

/// Parses a JMESPath expression into an AST
pub fn parse(expr: &str) -> ParseResult {
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
    fn new(expr: &str, pos: usize, msg: &str, hint: &str) -> ParseError {
        // Find each new line and create a formatted error message.
        let mut line: usize = 0;
        let mut col: usize = 0;
        let mut buff = String::new();
        for l in expr.lines().collect::<Vec<&str>>() {
            buff.push_str(l);
            buff.push('\n');
            if buff.len() > pos {
                col = match line {
                    0 => pos,
                    _ => buff.len().checked_sub(2 + pos).unwrap_or(0)
                };
                ParseError::inject_err_pointer(&mut buff, col);
                break;
            }
            line += 1;
        }
        if hint.len() > 0 { buff.push_str(&format!("Hint: {}", hint)); }
        ParseError {
            msg: format!("Parse error at line {}, col {}; {}\n{}", line, col, msg, buff),
            line: line,
            col: col
        }
    }

    fn inject_err_pointer(string_buffer: &mut String, col: usize) {
        let span = (0..col).map(|_| ' ').collect::<String>();
        string_buffer.push_str(&span);
        string_buffer.push_str(&"^\n");
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
        let mut lexer = Lexer::new(expr);
        let tok0 = lexer.next().unwrap_or(Token::Eof);
        Parser {
            stream: lexer.peekable(),
            expr: expr.to_string(),
            token: tok0,
            pos: 0,
        }
    }

    /// Parses the expression into result containing an AST or ParseError.
    pub fn parse(&mut self) -> ParseResult {
        // Skip leading whitespace
        if self.token.is_whitespace() { self.advance(); }
        self.expr(0)
            .and_then(|result| {
                // After parsing the expr, we should reach the end of the stream.
                match self.stream.next() {
                    None | Some(Token::Eof) => Ok(result),
                    _ => Err(self.err(&"Did not reach token stream EOF"))
                }
            })
    }

    /// Main parse function of the Pratt parser that parses while RBP < LBP
    fn expr(&mut self, rbp: usize) -> ParseResult {
        let mut left = self.nud();
        while rbp < self.token.lbp() {
            left = self.led(try!(left), &rbp);
        }
        left
    }

    fn nud(&mut self) -> ParseResult {
        match self.token.clone() {
            Token::At => {
                self.advance();
                Ok(Ast::CurrentNode)
            },
            Token::Identifier { value, .. } => {
                self.advance();
                Ok(Ast::Identifier(value))
            },
            Token::QuotedIdentifier { value, .. } => {
                self.advance();
                match self.token {
                    Token::Lparen => Err(self.err(&"Quoted strings can't be a function name")),
                    _ => Ok(Ast::Identifier(value))
                }
            },
            Token::Star => {
                self.advance();
                self.parse_wildcard_values(Ast::CurrentNode)
            },
            Token::Lbracket => {
                self.advance();
                match self.token {
                    Token::Number { .. } | Token::Colon => self.parse_array_index(),
                    Token::Star => {
                        if self.stream.peek() != Some(&Token::Rbracket) {
                            self.parse_multi_list()
                        } else {
                            try!(self.expect("Star"));
                            self.parse_wildcard_index(Ast::CurrentNode)
                        }
                    },
                    _ => self.parse_multi_list()
                }
            },
            Token::Flatten => self.parse_flatten(Ast::CurrentNode),
            Token::Literal { value, .. } => {
                self.advance();
                Ok(Ast::Literal(value))
            },
            Token::Lbrace => {
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
            },
            Token::Ampersand => {
                self.advance();
                let rhs = try!(self.expr(Token::Ampersand.lbp()));
                Ok(Ast::Expref(Box::new(rhs)))
            },
            Token::Filter => self.parse_filter(Ast::CurrentNode),
            ref tok @ _ => return Err(self.err(&format!("Unexpected nud token: {}",
                                                        tok.token_name()))),
        }
    }

    fn led(&mut self, left: Ast, rbp: &usize) -> ParseResult {
        match self.token {
            Token::Dot => {
                if self.stream.peek() == Some(&Token::Star) {
                    self.advance();
                    self.advance();
                    self.parse_wildcard_values(left)
                } else {
                    let rhs = try!(self.parse_dot(Token::Dot.lbp()));
                    Ok(Ast::Subexpr(Box::new(left), Box::new(rhs)))
                }
            },
            Token::Lbracket => {
                try!(self.expect("Number|Colon|Star"));
                match self.token {
                    Token::Number {.. } | Token::Colon => {
                        Ok(Ast::Subexpr(Box::new(left),
                                        Box::new(try!(self.parse_array_index()))))
                    },
                    _ => self.parse_wildcard_index(left)
                }
            },
            Token::Flatten => self.parse_flatten(left),
            Token::Or => {
                self.advance();
                let rhs = try!(self.expr(Token::Or.lbp()));
                Ok(Ast::Or(Box::new(left), Box::new(rhs)))
            },
            Token::Pipe => {
                self.advance();
                let rhs = try!(self.expr(Token::Pipe.lbp()));
                Ok(Ast::Subexpr(Box::new(left), Box::new(rhs)))
            },
            Token::Lparen => {
                match left {
                    Ast::Identifier(v) => {
                        self.advance();
                        Ok(Ast::Function(v, try!(self.parse_list(Token::Rparen))))
                    },
                    _ => Err(self.err("Functions must be preceded by an identifier"))
                }
            },
            Token::Filter => self.parse_filter(left),
            Token::Eq => self.parse_comparator(Comparator::Eq, left),
            Token::Ne => self.parse_comparator(Comparator::Ne, left),
            Token::Gt => self.parse_comparator(Comparator::Gt, left),
            Token::Gte => self.parse_comparator(Comparator::Gte, left),
            Token::Lt => self.parse_comparator(Comparator::Lt, left),
            Token::Lte => self.parse_comparator(Comparator::Lte, left),
            _ => Err(self.err(&format!("Unexpected led token: {}",
                                       self.token.token_name()))),
        }
    }

    /// Ensures that a Token is one of the pipe separated token names
    /// provided as the edible argument (e.g., "Identifier|Eof").
    fn validate(&self, token: &Token, edible: &str) -> Result<(), ParseError> {
        let token_name = token.token_name();
        if edible.contains(&token_name) {
            Ok(())
        } else {
            Err(self.err(&format!("Expected {}, found {}", edible, token_name)))
        }
    }

    /// Ensures that the next token in the token stream is one of the pipe
    /// separated token names provided as the edible argument (e.g.,
    /// "Identifier|Eof").
    fn expect(&mut self, edible: &str) -> Result<(), ParseError> {
        self.advance();
        self.validate(&self.token, edible)
    }

    /// Advances the cursor position, skipping any whitespace encountered.
    fn advance(&mut self) {
        loop {
            self.pos += self.token.span();
            self.token = self.stream.next().unwrap_or(Token::Eof);
            if !self.token.is_whitespace() {
                break;
            }
        }
    }

    /// Returns a formatted ParseError with the given message.
    fn err(&self, msg: &str) -> ParseError {
        let hint_msg = match self.token.clone() {
            Token::Unknown { hint, .. } => hint,
            _ => "".to_string()
        };
        ParseError::new(&self.expr, self.pos, msg, &hint_msg)
    }

    /// Generates a formatted parse error for an out of place token.
    fn token_err(&self) -> ParseError {
        self.err(&format!("Unexpected token: {}", self.token.token_name()))
    }

    fn parse_kvp(&mut self) -> Result<KeyValuePair, ParseError> {
        match self.token.clone() {
            Token::Identifier { value, .. } => {
                try!(self.expect("Colon"));
                self.advance();
                Ok(KeyValuePair {
                    key: Ast::Literal(Json::String(value)),
                    value: try!(self.expr(0))
                })
            },
            _ => Err(self.err("Expected Identifier to start key value pair"))
        }
    }

    /// Parses a filter token into an ArrayProjection that filters the right
    /// side of the projection using a Condition node. If the Condition node
    /// returns a truthy value, then the value is yielded by the projection.
    fn parse_filter(&mut self, lhs: Ast) -> ParseResult {
        self.advance();
        // Parse the LHS of the condition node.
        let condition_lhs = try!(self.expr(0));
        // Eat the closing bracket.
        try!(self.validate(&self.token, "Rbracket"));
        self.advance();
        Ok(Ast::ArrayProjection(
            Box::new(Ast::Condition(Box::new(condition_lhs), Box::new(lhs))),
            Box::new(try!(self.projection_rhs(Token::Filter.lbp())))
        ))
    }

    fn parse_flatten(&mut self, lhs: Ast) -> ParseResult {
        let rhs = try!(self.projection_rhs(Token::Flatten.lbp()));
        Ok(Ast::ArrayProjection(
            Box::new(Ast::Flatten(Box::new(lhs))),
            Box::new(rhs)
        ))
    }

    /// Parses a comparator token into a Comparison (e.g., foo == bar)
    fn parse_comparator(&mut self, cmp: Comparator, lhs: Ast) -> ParseResult {
        let lbp = self.token.lbp();
        self.advance();
        let rhs = try!(self.expr(lbp));
        Ok(Ast::Comparison(cmp, Box::new(lhs), Box::new(rhs)))
    }

    /// Parses the right hand side of a dot expression.
    fn parse_dot(&mut self, lbp: usize) -> ParseResult {
        try!(self.expect("Identifier|Star|Lbrace|Lbracket|Ampersand|Filter"));
        match self.token {
            Token::Lbracket => { self.advance(); self.parse_multi_list() },
            _ => self.expr(lbp)
        }
    }

    /// Parses the right hand side of a projection, using the given LBP to
    /// determine when to stop consuming tokens.
    fn projection_rhs(&mut self, lbp: usize) -> ParseResult {
        if self.token.lbp() < 10 {
            return Ok(Ast::CurrentNode);
        }
        match self.token {
            Token::Dot      => self.parse_dot(lbp),
            Token::Lbracket => self.expr(lbp),
            Token::Filter   => self.expr(lbp),
            _               => Err(self.token_err())
        }
    }

    /// Creates a projection for "[*]"
    fn parse_wildcard_index(&mut self, lhs: Ast) -> ParseResult {
        try!(self.expect("Rbracket"));
        self.advance();
        let rhs = try!(self.projection_rhs(Token::Star.lbp()));
        Ok(Ast::ArrayProjection(Box::new(lhs), Box::new(rhs)))
    }

    /// Creates a projection for "*"
    fn parse_wildcard_values(&mut self, lhs: Ast) -> ParseResult {
        let rhs = try!(self.projection_rhs(Token::Star.lbp()));
        Ok(Ast::ObjectProjection(Box::new(lhs), Box::new(rhs)))
    }

    /// Parses [0], [::-1], [0:-1], [0:1], etc...
    fn parse_array_index(&mut self) -> ParseResult {
        let mut parts = [None, None, None];
        let mut pos = 0;
        loop {
            match self.token {
                Token::Colon if pos >= 2 => {
                    return Err(self.err("Too many colons in slice expr"));
                },
                Token::Colon => {
                    pos += 1;
                    try!(self.expect("Number|Colon|Rbracket"));
                },
                Token::Number { value, .. } => {
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
    fn parse_multi_list(&mut self) -> ParseResult {
        Ok(Ast::MultiList(try!(self.parse_list(Token::Rbracket))))
    }

    /// Parse a comma separated list of expressions until a closing token.
    ///
    /// This function is used for functions and multi-list parsing. Note
    /// that this function allows empty lists. This is fine when parsing
    /// multi-list expressions because "[]" is tokenized as Token::Flatten.
    ///
    /// Examples: [foo, bar], foo(bar), foo(), foo(baz, bar)
    fn parse_list(&mut self, closing: Token) -> Result<Vec<Ast>, ParseError> {
        let mut nodes = vec![];
        while self.token != closing {
            nodes.push(try!(self.expr(0)));
            if self.token == Token::Comma {
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
    use ast::{Ast, Comparator, KeyValuePair};
    use self::rustc_serialize::json::Json;

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
                               bident(&"b")));
    }

    #[test] fn ensures_nud_token_is_valid_test() {
        let result = parse(",");
        assert!(result.is_err());
        assert!(result.err().unwrap().msg.contains("Unexpected nud token: Comma"));
    }

    #[test] fn multi_list_test() {
        let l = Ast::MultiList(vec![ident(&"a"), ident(&"b")]);
        assert_eq!(parse("[a, b]").unwrap(), l);
    }

    #[test] fn multi_list_unclosed() {
        let result = parse("[a, b");
        assert!(result.is_err());
        assert!(result.err().unwrap().msg.contains("Unexpected nud token"));
    }

    #[test] fn multi_list_unclosed_after_comma() {
        let result = parse("[a,");
        assert!(result.is_err());
        assert!(result.err().unwrap().msg.contains("Unexpected nud token"));
    }

    #[test] fn parse_error_includes_lexer_hints_test() {
        let result = parse(" \"foo");
        assert!(result.is_err());
        assert_eq!(result.err().unwrap().msg,
                   "Parse error at line 0, col 1; Unexpected nud token: Unknown\n \"foo\n ^\n\
                   Hint: Unclosed \" delimiter".to_string())
    }

    #[test] fn parse_error_on_column_zero_test() {
        let result = parse("]");
        assert!(result.is_err());
        assert_eq!(result.err().unwrap().msg,
                   "Parse error at line 0, col 0; Unexpected nud token: Rbracket\n\
                   ]\n^\n".to_string());
    }

    #[test] fn parse_error_injected_before_eof_test() {
        let result = parse("`\"foo\"` ||\n\n ]\n....]\n.");
        assert!(result.is_err());
        assert_eq!(result.err().unwrap().msg,
                   "Parse error at line 2, col 1; Unexpected nud token: Rbracket\n\
                   `\"foo\"` ||\n\n ]\n ^\n".to_string());
    }

    #[test] fn can_parse_with_leading_whitespace_tokens_test() {
        assert_eq!(parse("\n\n`\"foo\"`").unwrap(),
                   Ast::Literal(Json::String("foo".to_string())))
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
                                        bident(&"a")));
    }

    #[test] fn parses_revese_slice_test() {
        assert_eq!(parse("[::-1].a").unwrap(),
                   Ast::ArrayProjection(Box::new(Ast::Slice(None, None, Some(-1))),
                                        bident(&"a")));
    }

    #[test] fn parses_or_test() {
        let result = Ast::Or(bident(&"a"), bident(&"b"));
        assert_eq!(parse("a || b").unwrap(), result);
    }

    #[test] fn parses_pipe_test() {
        let result = Ast::Subexpr(bident(&"a"), bident(&"b"));
        assert_eq!(parse("a | b").unwrap(), result);
    }

    #[test] fn parses_literal_token_test() {
        assert_eq!(parse("`\"foo\"`").unwrap(),
                   Ast::Literal(Json::String("foo".to_string())))
    }

    #[test] fn parses_multi_hash() {
        let result = Ast::MultiHash(vec![
            KeyValuePair {
                key: Ast::Literal(Json::String("foo".to_string())),
                value: ident(&"bar")
            },
            KeyValuePair {
                key: Ast::Literal(Json::String("baz".to_string())),
                value: ident(&"bam")
            }
        ]);
        assert_eq!(parse("{foo: bar, baz: bam}").unwrap(), result);
    }

    #[test] fn parses_functions() {
        let r = Ast::Function("length".to_string(), vec![ident(&"a")]);
        assert_eq!(parse("length(a)").unwrap(), r);
    }

    #[test] fn parses_functions_with_no_args() {
        let r = Ast::Function("length".to_string(), vec![]);
        assert_eq!(parse("length()").unwrap(), r);
    }

    #[test] fn ensures_functions_cannot_start_with_quoted_identifier() {
        let result = parse("\"foo\"(baz, bar)");
        assert!(result.is_err());
        assert_eq!(result.err().unwrap().msg,
                   "Parse error at line 0, col 5; Quoted strings can't \
                   be a function name\n\
                   \"foo\"(baz, bar)\n     ^\n".to_string());
    }

    #[test] fn parses_expref() {
        let result = Ast::Expref(bident(&"foo"));
        assert_eq!(parse("&foo").unwrap(), result);
    }

    #[test] fn parses_comparisons() {
        let result = Ast::Comparison(Comparator::Eq, bident(&"foo"), bident(&"bar"));
        assert_eq!(parse("foo == bar").unwrap(), result);
    }

    #[test] fn parses_filters() {
        let comp = Ast::Comparison(Comparator::Eq, bident(&"foo"), bident(&"bar"));
        let proj = Ast::ArrayProjection(
            Box::new(Ast::Condition(
                Box::new(comp),
                Box::new(Ast::CurrentNode)
            )),
            bident(&"bar")
        );
        assert_eq!(parse("[?foo == bar].bar").unwrap(), proj);
    }

    #[test] fn ensures_filter_has_closing_rbracket() {
        let result = parse("[?foo == bar | baz");
        assert!(result.is_err());
        assert_eq!(result.err().unwrap().msg,
                   "Parse error at line 0, col 17; Expected Rbracket, found Eof\n\
                   [?foo == bar | baz\n                 ^\n".to_string());
    }

    #[test] fn parses_wildcard_array() {
        let ast = Ast::ArrayProjection(
            Box::new(Ast::Identifier("foo".to_string())),
            Box::new(Ast::Identifier("bar".to_string())));
        assert_eq!(ast, parse("foo[*].bar").unwrap());
    }

    #[test] fn parses_wildcard_object() {
        let ast = Ast::ObjectProjection(
            Box::new(Ast::Identifier("foo".to_string())),
            Box::new(Ast::Identifier("bar".to_string())));
        assert_eq!(ast, parse("foo.*.bar").unwrap());
    }

    fn bident(name: &str) -> Box<Ast> {
        Box::new(ident(name))
    }

    fn ident(name: &str) -> Ast {
        Ast::Identifier(name.to_string())
    }
}
