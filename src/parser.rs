extern crate rustc_serialize;

pub use self::Ast::*;

use lexer::Lexer;
use lexer::Token;
use self::rustc_serialize::json::{Json};

use std::iter::Peekable;

/// Parses a JMESPath expression into an AST
pub fn parse(expr: &str) -> Result<Ast, ParseError> {
    Parser::new(expr).parse()
}

/// Represents the abstract syntax tree of a JMESPath expression.
#[derive(Clone, PartialEq, Debug)]
pub enum Ast {
    Comparison(Comparator, Box<Ast>, Box<Ast>),
    CurrentNode,
    Expref(Box<Ast>),
    Flatten(Box<Ast>),
    Function(char, Vec<(Box<Ast>, Box<Ast>)>),
    Identifier(String),
    Index(i32),
    Literal(Box<Json>),
    MultiList(Vec<Box<Ast>>),
    MultiHash(Vec<Vec<(char, Box<Ast>)>>),
    Projection(ProjectionNode),
    Slice(i32, i32, i32),
    Subexpr(Box<Ast>, Box<Ast>),
    WildcardIndex,
    WildcardValues,
}

/// The different projection types.
#[derive(Clone, PartialEq, Debug)]
pub enum ProjectionNode {
    ArrayProjection(Box<Ast>, Box<Ast>),
    ObjectProjection(Box<Ast>, Box<Ast>)
}

/// Comparators (i.e., less than, greater than, etc.)
#[derive(Clone, PartialEq, Debug)]
pub enum Comparator { Eq, Lt, Le, Ne, Ge, Gt }

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
        // After parsing the expression, we should have reached the end of the stream.
        if token.is_some() && token.unwrap() != Token::Eof {
            return self.err("Did not reach the end of the token stream".as_ref());
        }
        result
    }

    /// Ensures that the next token in the token stream is one of the pipe separated
    /// token named provided as the edible argument (e.g., "Identifier|Eof").
    fn expect(&mut self, edible: &str) -> Result<Ast, ParseError> {
        self.advance();
        // Get the string name of the token.
        let token_name = self.token.token_to_string();
        if edible.contains(&token_name) {
            return Ok(CurrentNode);
        }
        let message = format!("Expected one of the following tokens: {:?}", edible);
        self.err(&message)
    }

    /// Advances the cursor position, skipping any whitespace encountered.
    #[inline]
    fn advance(&mut self) {
        self.pos += self.token.size();
        loop {
            let tok = self.stream.next();
            match tok {
                None => break,
                Some(Token::Whitespace) => self.pos += self.token.size(),
                _ => {
                    self.token = tok.unwrap();
                    break
                }
            }
        }
    }

    /// Main parse function of the Pratt parser that parses while RBP < LBP
    pub fn expr(&mut self, rbp: usize) -> Result<Ast, ParseError> {
        // Parse the NUD token.
        let mut left = match self.token.clone() {
            Token::At               => self.nud_at(),
            Token::Identifier(s, _) => self.nud_identifier(s),
            Token::Star             => self.nud_star(),
            Token::Lbracket         => self.nud_lbracket(),
            Token::Flatten          => self.nud_flatten(),
            // Token::Literal(_, _)    => self.nud_literal(),
            // Token::Ampersand        => self.nud_ampersand(),
            // Token::Lbrace           => self.nud_lbrace(),
            // Token::Filter           => self.nud_filter(),
            _ => { return self.err(&"Unexpected NUD token"); }
        };

        // Parse any LED tokens with a higher binding power.
        while rbp < self.token.lbp() {
            left = match self.token {
                Token::Dot      => self.led_dot(left.unwrap()),
                Token::Lbracket => self.led_lbracket(left.unwrap()),
                Token::Flatten  => self.led_flatten(left.unwrap()),
                _ => {
                    self.err(&"Unexpected LED token");
                    break;
                }
            };
        }

        left
    }

    /// Returns a formatted ParseError with the given message.
    fn err(&self, msg: &str) -> Result<Ast, ParseError> {
        // Find each new line and create a formatted error message.
        let mut line = 0;
        let mut col = self.pos;
        Err(ParseError {
            msg: format!("Error at {:?} token, {}: {}",
                         self.token, self.pos, msg),
            col: line,
            line: col
        })
    }

    /// Examples: "@"
    fn nud_at(&mut self) -> Result<Ast, ParseError> {
        self.advance();
        Ok(CurrentNode)
    }

    /// Examples: "Foo"
    fn nud_identifier(&mut self, s: String) -> Result<Ast, ParseError> {
        self.advance();
        Ok(Identifier(s))
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
                self.parse_wildcard_index()
            },
            _ => self.parse_multi_list()
        }
    }

    /// Examples: foo[*], foo[0], foo[:-1], etc.
    fn led_lbracket(&mut self, lhs: Ast) -> Result<Ast, ParseError> {
        try!(self.expect("Number|Colon|Star"));
        match self.token {
            Token::Number(_, _) | Token::Colon => {
                let rhs = try!(self.parse_wildcard_index());
                Ok(Subexpr(Box::new(lhs), Box::new(rhs)))
            },
            _ => self.parse_wildcard_index()
        }
    }

    /// Examples: "*" (e.g., "* | *" would be a pipe containing two nud stars)
    fn nud_star(&mut self) -> Result<Ast, ParseError> {
        self.advance();
        self.parse_wildcard_values(CurrentNode)
    }

    /// Examples: "[]". Turns it into a LED flatten (i.e., "@[]").
    fn nud_flatten(&mut self) -> Result<Ast, ParseError> {
        self.led_flatten(CurrentNode)
    }

    /// Creates a Projection AST node for a flatten token.
    fn led_flatten(&mut self, lhs: Ast) -> Result<Ast, ParseError> {
        let rhs = try!(self.projection_rhs(Token::Flatten.lbp()));
        Ok(Projection(
            ProjectionNode::ArrayProjection(
                Box::new(Flatten(Box::new(lhs))),
                Box::new(rhs)
            )
        ))
    }

    fn led_dot(&mut self, left: Ast) -> Result<Ast, ParseError> {
        let rhs = try!(self.parse_dot(Token::Dot.lbp()));
        Ok(Ast::Subexpr(Box::new(left), Box::new(rhs)))
    }

    /// Parses the right hand side of a dot expression.
    fn parse_dot(&mut self, lbp: usize) -> Result<Ast, ParseError> {
        try!(self.expect("Identifier|Star|Lbrace|Lbracket|Ampersand|Filter"));
        match self.token {
            Token::Lbracket => {
                self.advance();
                self.parse_multi_list()
            },
            _ => self.expr(lbp)
        }
    }

    /// Parses the right hand side of a projection, using the given LBP to determine
    /// when to stop consuming tokens.
    fn projection_rhs(&mut self, lbp: usize) -> Result<Ast, ParseError> {
        let lbp = self.token.lbp();
        match self.token {
            Token::Dot      => self.parse_dot(lbp),
            Token::Lbracket => self.expr(lbp),
            Token::Filter   => self.expr(lbp),
            _ if lbp < 10   => Ok(CurrentNode),
            _               => self.err("Syntax error found in projection")
        }
    }

    /// Creates a projection for "[*]"
    fn parse_wildcard_index(&mut self) -> Result<Ast, ParseError> {
        try!(self.expect("Rbracket"));
        let lhs = Box::new(CurrentNode);
        let rhs = try!(self.projection_rhs(Token::Star.lbp()));
        Ok(Projection(ProjectionNode::ArrayProjection(lhs, Box::new(rhs))))
    }

    /// Creates a projection for "*"
    fn parse_wildcard_values(&mut self, lhs: Ast) -> Result<Ast, ParseError> {
        let rhs = try!(self.projection_rhs(Token::Star.lbp()));
        Ok(Projection(
            ProjectionNode::ObjectProjection(Box::new(lhs), Box::new(rhs)))
        )
    }

    /// @todo
    fn parse_array_index(&mut self) -> Result<Ast, ParseError> {
        self.advance();
        Ok(CurrentNode)
    }

    /// @todo
    fn parse_multi_list(&mut self) -> Result<Ast, ParseError> {
        self.advance();
        Ok(CurrentNode)
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test] fn indentifier_test() {
        assert_eq!(parse("foo").unwrap(), Identifier("foo".to_string()));
    }

    #[test] fn current_node_test() {
        assert_eq!(parse("@").unwrap(), CurrentNode);
    }

    #[test] fn wildcard_values_test() {
        assert_eq!(parse("*").unwrap(), WildcardValues);
    }

    #[test] fn dot_test() {
        assert!(parse("@.b").unwrap() == Subexpr(Box::new(CurrentNode),
                                                 Box::new(Identifier("b".to_string()))));
    }

    #[test] fn ensures_nud_token_is_valid_test() {

    }
}
