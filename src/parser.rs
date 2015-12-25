//! Module for parsing JMESPath expressions into an AST.
use std::fmt;
use std::collections::VecDeque;
use std::rc::Rc;

use super::variable::Variable;
use super::ast::{Ast, KeyValuePair, Comparator};
use super::lexer::{tokenize, Token, TokenTuple};

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
    fn new(expr: &str, pos: usize, msg: String) -> ParseError {
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
        ParseError {
            msg: format!("Parse error at line {}, col {}; {}\n{}", line, col, msg, buff),
            line: line,
            col: col
        }
    }

    fn inject_err_pointer(string_buffer: &mut String, col: usize) {
        let span = (0..col).map(|_| ' ').collect::<String>();
        string_buffer.push_str(&span);
        string_buffer.push_str(&"^");
    }
}

impl fmt::Display for ParseError {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(fmt, "{}", self.msg)
    }
}

/// Encapsulates parser state to keep parsers stateless.
pub struct Parser {
    /// Parsed tokens
    token_queue: VecDeque<TokenTuple>,
    /// Shared EOF token
    eof_token: Token,
    /// Expression being parsed
    expr: String,
    /// The current character offset in the expression
    pos: usize,
}

impl Parser {
    pub fn new(expr: &str) -> Parser {
        Parser {
            token_queue: tokenize(expr),
            eof_token: Token::Eof,
            pos: 0,
            expr: expr.to_string(),
        }
    }

    /// Parses the expression into result containing an AST or ParseError.
    pub fn parse(&mut self) -> ParseResult {
        self.expr(0)
            .and_then(|result| {
                // After parsing the expr, we should reach the end of the stream.
                match self.peek(0) {
                    &Token::Eof => Ok(result),
                    _ => Err(self.err(None, &"Did not reach token stream EOF"))
                }
            })
    }

    #[inline]
    pub fn advance(&mut self) -> Token {
        match self.token_queue.pop_front() {
            Some((pos, tok)) => {
                self.pos = pos;
                tok
            },
            None => Token::Eof
        }
    }

    #[inline]
    pub fn peek(&self, lookahead: usize) -> &Token {
        match self.token_queue.get(lookahead) {
            Some(&(_, ref t)) => t,
            None => &self.eof_token
        }
    }

    /// Returns a formatted ParseError with the given message.
    pub fn err(&self, current_token: Option<&Token>, error_msg: &str) -> ParseError {
        let mut buff = error_msg.to_string();
        match current_token {
            Some(&Token::Error { ref msg, .. }) => {
                buff.push_str(&format!(" -- {}", msg))
            },
            Some(ref t) => buff.push_str(&format!(" -- found {:?}", t)),
            _ => ()
        }
        ParseError::new(&self.expr, self.pos, buff)
    }

    /// Main parse function of the Pratt parser that parses while RBP < LBP
    fn expr(&mut self, rbp: usize) -> ParseResult {
        let mut left = self.nud();
        while rbp < self.peek(0).lbp() {
            left = self.led(try!(left));
        }
        left
    }

    fn nud(&mut self) -> ParseResult {
        match self.advance() {
            Token::At => Ok(Ast::CurrentNode),
            Token::Identifier(value) => Ok(Ast::Identifier(value)),
            Token::QuotedIdentifier(value) => {
                match self.peek(0) {
                    &Token::Lparen => {
                        Err(self.err(Some(&Token::Lparen),
                                     &"Quoted strings can't be a function name"))
                    },
                    _ => Ok(Ast::Identifier(value))
                }
            },
            Token::Star => self.parse_wildcard_values(Ast::CurrentNode),
            Token::Literal(value) => Ok(Ast::Literal(value)),
            Token::Lbracket => {
                match self.peek(0) {
                    &Token::Number(_) | &Token::Colon => self.parse_index(),
                    &Token::Star if self.peek(1) == &Token::Rbracket => {
                        self.advance();
                        self.parse_wildcard_index(Ast::CurrentNode)
                    },
                    _ => self.parse_multi_list()
                }
            },
            Token::Flatten => self.parse_flatten(Ast::CurrentNode),
            Token::Lbrace => {
                let mut pairs = vec![];
                loop {
                    // Requires at least on key value pair.
                    pairs.push(try!(self.parse_kvp()));
                    match self.advance() {
                        // Terminal condition is the Rbrace token
                        Token::Rbrace => break,
                        // Skip commas as they are used to delineate kvps
                        Token::Comma => continue,
                        ref t @ _ => return Err(self.err(Some(t), "Expected '}' or ','"))
                    }
                }
                Ok(Ast::MultiHash(pairs))
            },
            Token::Ampersand => {
                let rhs = try!(self.expr(Token::Ampersand.lbp()));
                Ok(Ast::Expref(Box::new(rhs)))
            },
            Token::Not => Ok(Ast::Not(Box::new(try!(self.expr(Token::Not.lbp()))))),
            Token::Filter => self.parse_filter(Ast::CurrentNode),
            Token::Lparen => {
                let result = try!(self.expr(0));
                match self.advance() {
                    Token::Rparen => Ok(result),
                    ref t @ _ => Err(self.err(Some(t), "Expected ')' to close '('"))
                }
            },
            ref tok @ _ => Err(self.err(Some(tok), &"Unexpected nud token"))
        }
    }

    fn led(&mut self, left: Ast) -> ParseResult {
        match self.advance() {
            Token::Dot => {
                if self.peek(0) == &Token::Star {
                    // Skip the star and parse the rhs
                    self.advance();
                    self.parse_wildcard_values(left)
                } else {
                    let rhs = try!(self.parse_dot(Token::Dot.lbp()));
                    Ok(Ast::Subexpr(Box::new(left), Box::new(rhs)))
                }
            },
            Token::Lbracket => {
                match match self.peek(0) {
                    &Token::Number(_) | &Token::Colon => true,
                    &Token::Star => false,
                    t @ _ => return Err(self.err(Some(t), "Expected number, ':', or '*'"))
                } {
                    true => {
                        Ok(Ast::Subexpr(Box::new(left),
                                        Box::new(try!(self.parse_index()))))
                    },
                    false => {
                        self.advance();
                        self.parse_wildcard_index(left)
                    }
                }
            },
            Token::Or => {
                let rhs = try!(self.expr(Token::Or.lbp()));
                Ok(Ast::Or(Box::new(left), Box::new(rhs)))
            },
            Token::And => {
                let rhs = try!(self.expr(Token::And.lbp()));
                Ok(Ast::And(Box::new(left), Box::new(rhs)))
            },
            Token::Pipe => {
                let rhs = try!(self.expr(Token::Pipe.lbp()));
                Ok(Ast::Subexpr(Box::new(left), Box::new(rhs)))
            },
            Token::Lparen => {
                match left {
                    Ast::Identifier(v) => {
                        Ok(Ast::Function(v, try!(self.parse_list(Token::Rparen))))
                    },
                    _ => panic!("Implement parens")
                }
            },
            Token::Flatten => self.parse_flatten(left),
            Token::Filter => self.parse_filter(left),
            Token::Eq => self.parse_comparator(Comparator::Eq, left),
            Token::Ne => self.parse_comparator(Comparator::Ne, left),
            Token::Gt => self.parse_comparator(Comparator::Gt, left),
            Token::Gte => self.parse_comparator(Comparator::Gte, left),
            Token::Lt => self.parse_comparator(Comparator::Lt, left),
            Token::Lte => self.parse_comparator(Comparator::Lte, left),
            ref t @ _ => Err(self.err(Some(t), "Unexpected led token")),
        }
    }

    fn parse_kvp(&mut self) -> Result<KeyValuePair, ParseError> {
        match self.advance() {
            Token::Identifier(value) | Token::QuotedIdentifier(value) => {
                if self.peek(0) == &Token::Colon {
                    self.advance();
                    Ok(KeyValuePair {
                        key: Ast::Literal(Rc::new(Variable::String(value))),
                        value: try!(self.expr(0))
                    })
                } else {
                    Err(self.err(Some(self.peek(0)), &"Expected ':' to follow key"))
                }
            },
            ref t @ _ => Err(self.err(Some(t), &"Expected Identifier to start key value pair"))
        }
    }

    /// Parses a filter token into a Projection that filters the right
    /// side of the projection using a Condition node. If the Condition node
    /// returns a truthy value, then the value is yielded by the projection.
    fn parse_filter(&mut self, lhs: Ast) -> ParseResult {
        // Parse the LHS of the condition node.
        let condition_lhs = try!(self.expr(0));
        // Eat the closing bracket.
        if self.advance() != Token::Rbracket {
            Err(self.err(None, &"Expected ']'"))
        } else {
            let condition_rhs = Box::new(try!(self.projection_rhs(Token::Filter.lbp())));
            Ok(Ast::Projection(
                Box::new(lhs),
                Box::new(Ast::Condition(Box::new(condition_lhs), condition_rhs))))
        }
    }

    fn parse_flatten(&mut self, lhs: Ast) -> ParseResult {
        let rhs = try!(self.projection_rhs(Token::Flatten.lbp()));
        Ok(Ast::Projection(Box::new(Ast::Flatten(Box::new(lhs))), Box::new(rhs)))
    }

    /// Parses a comparator token into a Comparison (e.g., foo == bar)
    fn parse_comparator(&mut self, cmp: Comparator, lhs: Ast) -> ParseResult {
        let rhs = try!(self.expr(Token::Eq.lbp()));
        Ok(Ast::Comparison(cmp, Box::new(lhs), Box::new(rhs)))
    }

    /// Parses the right hand side of a dot expression.
    fn parse_dot(&mut self, lbp: usize) -> ParseResult {
        match match self.peek(0) {
            &Token::Lbracket => true,
            &Token::Identifier(_) | &Token::QuotedIdentifier(_) | &Token::Star | &Token::Lbrace
                | &Token::Ampersand | &Token::Filter => false,
            _ => return Err(self.err(None, &"Expected identifier, '*', '{', '[', '&', or '[?'"))
        } {
            true => {
                self.advance();
                self.parse_multi_list()
            },
            false => self.expr(lbp)
        }
    }

    /// Parses the right hand side of a projection, using the given LBP to
    /// determine when to stop consuming tokens.
    fn projection_rhs(&mut self, lbp: usize) -> ParseResult {
        match match self.peek(0) {
            &Token::Dot => true,
            &Token::Lbracket | &Token::Filter => false,
            p @ _ if p.lbp() < 10 => return Ok(Ast::CurrentNode),
            _ => return Err(self.err(None, &"Expected '.', '[', or '[?'"))
        } {
            true => {
                self.advance();
                self.parse_dot(lbp)
            },
            false => self.expr(lbp)
        }
    }

    /// Creates a projection for "[*]"
    fn parse_wildcard_index(&mut self, lhs: Ast) -> ParseResult {
        match self.advance() {
            Token::Rbracket => {
                let rhs = try!(self.projection_rhs(Token::Star.lbp()));
                Ok(Ast::Projection(Box::new(lhs), Box::new(rhs)))
            },
            ref t @ _ => Err(self.err(Some(t), &"Expected ']' for wildcard index"))
        }
    }

    /// Creates a projection for "*"
    fn parse_wildcard_values(&mut self, lhs: Ast) -> ParseResult {
        let rhs = try!(self.projection_rhs(Token::Star.lbp()));
        Ok(Ast::Projection(
            Box::new(Ast::ObjectValues(Box::new(lhs))),
            Box::new(rhs)))
    }

    /// Parses [0], [::-1], [0:-1], [0:1], etc...
    fn parse_index(&mut self) -> ParseResult {
        let mut parts = [None, None, None];
        let mut pos = 0;
        loop {
            match self.advance() {
                Token::Number(value) => {
                    parts[pos] = Some(value);
                    match self.peek(0) {
                        &Token::Colon | &Token::Rbracket => (),
                        t @ _ => return Err(self.err(Some(t), "Expected ':', or ']'"))
                    };
                },
                Token::Rbracket => break,
                Token::Colon if pos >= 2 => {
                    return Err(self.err(None, "Too many colons in slice expr"));
                },
                Token::Colon => {
                    pos += 1;
                    match self.peek(0) {
                        &Token::Number(_) | &Token::Colon | &Token::Rbracket => continue,
                        _ => return Err(self.err(None, "Expected number, ':', or ']'"))
                    };
                },
                ref t @ _ => return Err(self.err(Some(t), "Expected number, ':', or ']'")),
            }
        }

        if pos == 0 {
            // No colons were found, so this is a simple index extraction.
            Ok(Ast::Index(parts[0].unwrap()))
        } else {
            // Sliced array from start (e.g., [2:])
            let lhs = Ast::Slice(parts[0], parts[1], parts[2].unwrap_or(1));
            let rhs = try!(self.projection_rhs(Token::Star.lbp()));
            Ok(Ast::Projection(Box::new(lhs), Box::new(rhs)))
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
        while self.peek(0) != &closing {
            nodes.push(try!(self.expr(0)));
            // Skip commas
            if self.peek(0) == &Token::Comma {
                self.advance();
                if self.peek(0) == &closing {
                    return Err(self.err(Some(self.peek(0)), "token cannot be directly after ','"));
                }
            }
        }
        self.advance();
        Ok(nodes)
    }
}
