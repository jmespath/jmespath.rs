//! Module for parsing JMESPath expressions into an AST.

extern crate rustc_serialize;

use std::iter::Peekable;
use self::rustc_serialize::json::Json;
use std::collections::VecDeque;

use ast::{Ast, Comparator, KeyValuePair};
use lexer::{Lexer, Token};

/// An alias for computations that can return an `Ast` or `ParseError`.
pub type ParseResult = Result<Ast, ParseError>;
type ParseStep = Result<(), ParseError>;

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

enum State {
    Nud(usize),
    Led(usize)
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
    /// Operand queue containing AST nodes.
    output_queue: VecDeque<Ast>,
    /// Operator stack containing tokens.
    operator_stack: Vec<Token>,
    /// Stack of led RBP values to parse.
    state_stack: Vec<State>
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
            operator_stack: vec!(),
            output_queue: VecDeque::new(),
            state_stack: vec!()
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

    fn expr(&mut self, rbp: usize) -> ParseResult {
        self.state_stack.push(State::Nud(0));
        while self.token != Token::Eof {
            match self.state_stack.last() {
                Some(&State::Nud(rbp)) => {
                    self.state_stack.pop();
                    self.nud();
                    self.state_stack.push(State::Led(rbp));
                },
                Some(&State::Led(rbp)) => {
                    if (rbp < self.token.lbp()) {
                        self.led();
                    } else {
                        self.state_stack.pop();
                    }
                },
                None => break
            }
        }
        while !self.operator_stack.is_empty() {
            try!(self.pop_token());
        }
        match self.output_queue.pop_back() {
            Some(ast) => Ok(ast),
            None => Err(self.err(&"Unexpected end of token stream"))
        }
    }

    fn nud(&mut self) -> ParseStep {
        match self.token.clone() {
            Token::At => {
                self.advance();
                self.output_queue.push_front(Ast::CurrentNode);
                Ok(())
            },
            Token::Identifier { value, .. } => {
                self.advance();
                self.output_queue.push_front(Ast::Identifier(value));
                Ok(())
            },
            Token::QuotedIdentifier { value, .. } => {
                self.advance();
                match self.token {
                    Token::Lparen => Err(self.err(&"Quoted strings can't be function names")),
                    _ => {
                        self.output_queue.push_front(Ast::Identifier(value));
                        Ok(())
                    }
                }
            },
            Token::Literal { value, .. } => {
                self.advance();
                self.output_queue.push_front(Ast::Literal(value));
                Ok(())
            },
            ref tok @ _ => Err(self.err(&format!("Unexpected nud token: {}",
                                                 tok.token_name()))),
        }
    }

    fn led(&mut self) -> ParseStep  {
        match self.token {
            Token::Dot => {
                if self.stream.peek() == Some(&Token::Star) {
                    self.advance();
                    self.advance();
                    try!(self.operator(Token::Star));
                } else {
                    self.advance();
                    self.state_stack.push(State::Nud(Token::Dot.lbp()));
                    try!(self.operator(Token::Dot));
                }
                Ok(())
            },
            Token::Or => {
                self.advance();
                self.state_stack.push(State::Nud(Token::Or.lbp()));
                try!(self.operator(Token::Or));
                Ok(())
            },
            Token::Pipe => {
                self.advance();
                self.state_stack.push(State::Nud(Token::Pipe.lbp()));
                try!(self.operator(Token::Pipe));
                Ok(())
            },
            _ => Err(self.err(&format!("Unexpected led token: {}",
                              self.token.token_name()))),
        }
    }

    fn operator(&mut self, token: Token) -> ParseStep {
        loop {
            // Pop things from the top of the operator stack that have a higher precedence.
            match self.last_operator_lbp() {
                // Use <= for left-associative, and < for right associative.
                Some(rbp) if token.lbp() <= rbp => self.pop_token(),
                _ => {
                    self.operator_stack.push(token);
                    return Ok(());
                }
            };
        }
    }

    fn last_operator_lbp(&self) -> Option<usize> {
        match self.operator_stack.last() {
            Some(ref top) => Some(top.lbp()),
            None => None
        }
    }

    fn pop_token(&mut self) -> ParseStep {
        match self.operator_stack.pop().unwrap() {
            Token::Dot => {
                let rhs = self.output_queue.pop_front().unwrap();
                let lhs = self.output_queue.pop_front().unwrap();
                self.output_queue.push_front(Ast::Subexpr(Box::new(lhs), Box::new(rhs)));
                Ok(())
            },
            Token::Or => {
                let rhs = self.output_queue.pop_front().unwrap();
                let lhs = self.output_queue.pop_front().unwrap();
                self.output_queue.push_front(Ast::Or(Box::new(lhs), Box::new(rhs)));
                Ok(())
            },
            Token::Pipe => {
                let rhs = self.output_queue.pop_front().unwrap();
                let lhs = self.output_queue.pop_front().unwrap();
                self.output_queue.push_front(Ast::Subexpr(Box::new(lhs), Box::new(rhs)));
                Ok(())
            },
            _ => Err(self.err(&"Unexpected led token"))
        }
    }

    /// Ensures that a Token is one of the pipe separated token names
    /// provided as the edible argument (e.g., "Identifier|Eof").
    fn validate(&self, token: &Token, edible: &str) -> ParseStep {
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
    fn expect(&mut self, edible: &str) -> ParseStep {
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
}

#[cfg(test)]
mod test {
    extern crate rustc_serialize;
    use self::rustc_serialize::json::Json;
    use super::*;
    use ast::{Ast, Comparator, KeyValuePair};

    #[test] fn test_parse_nud() {
        let ast = parse("foo").unwrap();
        assert_eq!(ast, Ast::Identifier("foo".to_string()));
    }

    #[test] fn test_parse_subexpr() {
        let ast = parse("foo.bar.baz").unwrap();
        assert_eq!(ast, Ast::Subexpr(
            Box::new(Ast::Subexpr(Box::new(Ast::Identifier("foo".to_string())),
                         Box::new(Ast::Identifier("bar".to_string())))),
            Box::new(Ast::Identifier("baz".to_string()))));
    }

    #[test] fn test_parse_or() {
        let ast = parse("foo || bar").unwrap();
        assert_eq!(ast, Ast::Or(Box::new(Ast::Identifier("foo".to_string())),
                                Box::new(Ast::Identifier("bar".to_string()))));
    }

    #[test] fn test_parse_or_and_subexpr_with_precedence() {
        let ast = parse("foo.baz || bar.bam").unwrap();
        let expected = Ast::Or(
            Box::new(Ast::Subexpr(Box::new(Ast::Identifier("foo".to_string())),
                                  Box::new(Ast::Identifier("baz".to_string())))),
            Box::new(Ast::Subexpr(Box::new(Ast::Identifier("bar".to_string())),
                                  Box::new(Ast::Identifier("bam".to_string())))));
        assert_eq!(ast, expected);
    }

    #[test] fn test_parse_or_and_pipe_with_precedence() {
        let ast = parse("foo || bar | baz").unwrap();
        let expected = Ast::Subexpr(
            Box::new(Ast::Or(Box::new(Ast::Identifier("foo".to_string())),
                             Box::new(Ast::Identifier("bar".to_string())))),
            Box::new(Ast::Identifier("baz".to_string()))
        );
        assert_eq!(ast, expected);
    }
}
