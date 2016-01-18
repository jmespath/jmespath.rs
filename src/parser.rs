//! Module for parsing JMESPath expressions into an AST.
//!
//! This JMESPath parser implementation uses a variation of the Pratt parser,
//! or top down operator precedence parser:
//! http://hall.org.ua/halls/wizzard/pdf/Vaughan.Pratt.TDOP.pdf
//!
//! In order to prevent stack overflows with moderately large expressions,
//! instead of using recursion, we use a trampoline technique and an explicitly
//! managed stack that is stored in the heap. Expressions that require
//! recursion each have their own `ThunkParser` that is pushed onto the
//! `thunks` stack of the parser. When the thunk is popped from the stack,
//! it is sent the current LHS node so that it can continue its parsing.

use std::collections::VecDeque;
use std::rc::Rc;

use super::{Error, ErrorReason};
use super::variable::Variable;
use super::ast::{Ast, KeyValuePair, Comparator};
use super::lexer::{tokenize, Token, TokenTuple};

/// Result of parsing an expression.
pub type ParseResult = Result<Ast, Error>;

/// Parses a JMESPath expression into an AST
pub fn parse(expr: &str) -> ParseResult {
    Parser::new(expr).and_then(|mut p| p.parse())
}

/// Result of sending a token to a state machine parser.
type SendResult = Result<Trampoline, Error>;

/// Pushing to a state maching can return a node or push a new state.
enum Trampoline {
    Value(Ast),
    Thunk(Box<ThunkParser>)
}

/// Represents a pending parser that needs an additional value.
trait ThunkParser {
    /// Sends an AST node into the parser, completing or continuing it
    fn send(self: Box<Self>, parser: &mut Parser, node: Ast) -> SendResult;

    /// Get the left binding power of the parser.
    fn lbp(&self) -> usize;
}

/// Parses the RHS of a Subexpr AST node.
struct SubexpressionParser {
    lbp: usize,
    offset: usize,
    lhs: Ast,
}

impl ThunkParser for SubexpressionParser {
    fn send(self: Box<Self>, _parser: &mut Parser, node: Ast) -> SendResult {
        Ok(Trampoline::Value(Ast::Subexpr {
            offset: self.offset,
            lhs: Box::new(self.lhs),
            rhs: Box::new(node)
        }))
    }

    fn lbp(&self) -> usize {
        self.lbp
    }
}

/// Parses the RHS of a slice projection.
struct SliceProjectionParser {
    offset: usize,
    start: Option<i32>,
    stop: Option<i32>,
    step: i32
}

impl ThunkParser for SliceProjectionParser {
    fn send(self: Box<Self>, _parser: &mut Parser, node: Ast) -> SendResult {
        Ok(Trampoline::Value(Ast::Projection {
            offset: self.offset,
            lhs: Box::new(Ast::Slice {
                offset: self.offset,
                start: self.start,
                stop: self.stop,
                step: self.step
            }),
            rhs: Box::new(node)
        }))
    }

    fn lbp(&self) -> usize {
        Token::Star.lbp()
    }
}

/// Parses a filter Projection that filters the right side of the
/// projection using a Condition node. If the Condition node returns
/// a truthy value, then the value is yielded by the projection.
struct FilterProjectionParser {
    offset: usize,
    lhs: Ast,
    predicate: Option<Ast>,
}

impl ThunkParser for FilterProjectionParser {
    fn send(self: Box<Self>, parser: &mut Parser, node: Ast) -> SendResult {
        let thunk_parser = *self;
        match thunk_parser.predicate {
            None => {
                // After receiving the parsed predicate, parse the projection.
                match parser.advance() {
                    // Ensure the ']' was closed
                    Token::Rbracket => {
                        parser.projection_rhs(Box::new(FilterProjectionParser {
                            offset: thunk_parser.offset,
                            lhs: thunk_parser.lhs,
                            predicate: Some(node)
                        }))
                    },
                    ref t @ _ => Err(parser.err(t, &"Expected ']'", false))
                }
            },
            Some(predicate) => {
                Ok(Trampoline::Value(Ast::Projection {
                    offset: thunk_parser.offset,
                    lhs: Box::new(thunk_parser.lhs),
                    rhs: Box::new(Ast::Condition {
                        offset: thunk_parser.offset,
                        predicate: Box::new(predicate),
                        then: Box::new(node)
                   })
               }))
            }
        }
    }

    fn lbp(&self) -> usize {
        match self.predicate {
            None => 0,
            Some(_) => Token::Filter.lbp()
        }
    }
}

/// Parses the comparison and RHS of a comparison (e.g., foo [> bar]), and
/// creates an Ast::Comparison node holding the LHS, RHS, and comparator.
struct ComparisonParser {
    offset: usize,
    cmp: Comparator,
    lhs: Ast
}

impl ThunkParser for ComparisonParser {
    fn send(self: Box<Self>, _parser: &mut Parser, node: Ast) -> SendResult {
        let thunk_parser = *self;
        Ok(Trampoline::Value(Ast::Comparison {
            offset: thunk_parser.offset,
            comparator: thunk_parser.cmp,
            lhs: Box::new(thunk_parser.lhs),
            rhs: Box::new(node)
        }))
    }

    fn lbp(&self) -> usize {
        match self.cmp {
            Comparator::Eq => Token::Eq.lbp(),
            Comparator::Ne => Token::Ne.lbp(),
            Comparator::Lt => Token::Lt.lbp(),
            Comparator::Lte => Token::Lte.lbp(),
            Comparator::Gt => Token::Gt.lbp(),
            Comparator::Gte => Token::Gte.lbp(),
        }
    }
}

/// Parses a multi-select-list AST node until an Rbracket token is found.
struct MultiListParser {
    offset: usize,
    elements: Vec<Ast>
}

impl ThunkParser for MultiListParser {
    fn send(mut self: Box<Self>, parser: &mut Parser, node: Ast) -> SendResult {
        self.elements.push(node);
        if try!(push_list_value(parser, Token::Rbracket)) {
            Ok(Trampoline::Value(Ast::MultiList {
                offset: self.offset,
                elements: self.elements
            }))
        } else {
            Ok(Trampoline::Thunk(self))
        }
    }

    fn lbp(&self) -> usize {
        0
    }
}

/// Parses a an Ast::Function node until an Rparen token is found.
struct FunctionParser {
    name: String,
    offset: usize,
    args: Vec<Ast>,
}

impl ThunkParser for FunctionParser {
    fn send(self: Box<Self>, parser: &mut Parser, node: Ast) -> SendResult {
        let mut thunk_parser = *self;
        thunk_parser.args.push(node);
        if try!(push_list_value(parser, Token::Rparen)) {
            Ok(Trampoline::Value(Ast::Function {
                offset: thunk_parser.offset,
                name: thunk_parser.name,
                args: thunk_parser.args
            }))
        } else {
            Ok(Trampoline::Thunk(Box::new(thunk_parser)))
        }
    }

    fn lbp(&self) -> usize {
        0
    }
}

/// Parses an Ast::MultiHash node until an Rbrace. Key value pairs are all
/// pushed onto a single Vec. We then treat each odd element as a key and even
/// element as a value to build the KeyValuePair AST nodes.
struct MultiHashParser {
    offset: usize,
    elements: VecDeque<Ast>,
}

impl ThunkParser for MultiHashParser {
    fn send(self: Box<Self>, parser: &mut Parser, node: Ast) -> SendResult {
        let mut thunk_parser = *self;
        thunk_parser.elements.push_back(node);
        match parser.advance() {
            Token::Rbrace => thunk_parser.close_parser(),
            Token::Comma => Self::with_key(parser, thunk_parser.offset, thunk_parser.elements),
            ref t @ _ => Err(parser.err(t, "Expected '}' or ','", false))
        }
    }

    fn lbp(&self) -> usize {
        0
    }
}

impl MultiHashParser {
    /// Creates a new MultiHashParser with an added key from the parser.
    fn with_key(parser: &mut Parser, offset: usize, mut elements: VecDeque<Ast>) -> SendResult {
        // Ensure the key is valid
        let (key_offset, key_name) = try!(match parser.advance_with_pos() {
            (p @ _, Token::Identifier(v)) => Ok((p, v)),
            (p @ _, Token::QuotedIdentifier(v)) => Ok((p, v)),
            (_, ref t @ _) => Err(parser.err(t, &"Invalid key value pair", false))
        });
        // The key is represented as a literal value and interpreted at runtime.
        elements.push_back(Ast::Literal {
            offset: key_offset,
            value: Rc::new(Variable::String(key_name))
        });
        // Ensure that the key is followed by ":"
        match parser.advance() {
            Token::Colon =>  {
                Ok(Trampoline::Thunk(Box::new(MultiHashParser {
                    offset: offset,
                    elements: elements
                })))
            },
            ref t @ _ => Err(parser.err(t, &"Expected ':' to follow key", true))
        }
    }

    /// Terminal condition is met so return the Ast node.
    fn close_parser(mut self) -> SendResult {
        let mut key_value_pairs: Vec<KeyValuePair> = Vec::new();
        while !self.elements.is_empty() {
            key_value_pairs.push(KeyValuePair {
                key: self.elements.pop_front().unwrap(),
                value: self.elements.pop_front().unwrap()
            });
        }
        Ok(Trampoline::Value(Ast::MultiHash {
            offset: self.offset,
            elements: key_value_pairs
        }))
    }
}

/// Parses the RHS of an Or expression to creat an Ast::Or node.
struct OrParser {
    offset: usize,
    lhs: Ast
}

impl ThunkParser for OrParser {
    fn send(self: Box<Self>, _parser: &mut Parser, node: Ast) -> SendResult {
        Ok(Trampoline::Value(Ast::Or {
            offset: self.offset,
            lhs: Box::new(self.lhs),
            rhs: Box::new(node)
        }))
    }

    fn lbp(&self) -> usize {
        Token::Or.lbp()
    }
}

/// Parses the RHS of an And expression to creat an Ast::And node.
struct AndParser {
    offset: usize,
    lhs: Ast
}

impl ThunkParser for AndParser {
    fn send(self: Box<Self>, _parser: &mut Parser, node: Ast) -> SendResult {
        Ok(Trampoline::Value(Ast::And {
            offset: self.offset,
            lhs: Box::new(self.lhs),
            rhs: Box::new(node)
        }))
    }

    fn lbp(&self) -> usize {
        Token::And.lbp()
    }
}

/// Parses the contents of a not expression to create an Ast::Not node.
struct NotParser {
    offset: usize
}

impl ThunkParser for NotParser {
    fn send(self: Box<Self>, _parser: &mut Parser, node: Ast) -> SendResult {
        Ok(Trampoline::Value(Ast::Not {
            offset: self.offset,
            node: Box::new(node)
        }))
    }

    fn lbp(&self) -> usize {
        Token::Not.lbp()
    }
}

/// Parses an expression reference.
struct ExprefParser {
    offset: usize
}

impl ThunkParser for ExprefParser {
    fn send(self: Box<Self>, _parser: &mut Parser, node: Ast) -> SendResult {
        Ok(Trampoline::Value(Ast::Expref {
            offset: self.offset,
            ast: Box::new(node)
        }))
    }

    fn lbp(&self) -> usize {
        Token::Ampersand.lbp()
    }
}

/// Parses a precedence parenthesis.
struct PrecedenceParenParser;

impl ThunkParser for PrecedenceParenParser {
    fn send(self: Box<Self>, parser: &mut Parser, node: Ast) -> SendResult {
        match parser.advance() {
            Token::Rparen => Ok(Trampoline::Value(node)),
            ref t @ _ => Err(parser.err(t, "Expected ')' to close '('", false))
        }
    }

    fn lbp(&self) -> usize {
        0
    }
}

/// Parses the RHS of a wildcard index projection (e.g., foo.*.bar.baz)
struct WildcardValuesParser {
    offset: usize,
    lhs: Ast
}

impl ThunkParser for WildcardValuesParser {
    fn send(self: Box<Self>, _parser: &mut Parser, node: Ast) -> SendResult {
        Ok(Trampoline::Value(Ast::Projection {
            offset: self.offset,
            lhs: Box::new(Ast::ObjectValues {
                offset: self.offset,
                node: Box::new(self.lhs)
            }),
            rhs: Box::new(node)
        }))
    }

    fn lbp(&self) -> usize {
        Token::Star.lbp()
    }
}

/// Parses the RHS of a wildcard index projection (e.g., foo[*].bar.baz)
struct WildcardIndexParser {
    offset: usize,
    lhs: Ast
}

impl ThunkParser for WildcardIndexParser {
    fn send(self: Box<Self>, _parser: &mut Parser, node: Ast) -> SendResult {
        let thunk_parser = *self;
        Ok(Trampoline::Value(Ast::Projection {
            offset: thunk_parser.offset,
            lhs:Box::new(thunk_parser.lhs),
            rhs: Box::new(node)
        }))
    }

    fn lbp(&self) -> usize {
        Token::Star.lbp()
    }
}

/// Parses the RHS of a flatten projection.
struct FlattenProjectionParser {
    offset: usize,
    lhs: Ast
}

impl ThunkParser for FlattenProjectionParser {
    fn send(self: Box<Self>, _parser: &mut Parser, node: Ast) -> SendResult {
        Ok(Trampoline::Value(Ast::Projection {
            offset: self.offset,
            lhs: Box::new(Ast::Flatten {
                offset: self.offset,
                node: Box::new(self.lhs)
            }),
            rhs: Box::new(node)
        }))
    }

    fn lbp(&self) -> usize {
        Token::Flatten.lbp()
    }
}

/// Parses the first thunk. If it returns another thunk, returns a new
/// ThenParser that wraps the new thunk and the "then" pending thunk.
/// When a value is received, it is sent to the pending "then" thunk.
struct ThenParser {
    first: Box<ThunkParser>,
    then: Box<ThunkParser>,
}

impl ThunkParser for ThenParser {
    fn send(self: Box<Self>, parser: &mut Parser, node: Ast) -> SendResult {
        let thunk_parser = *self;
        match try!(thunk_parser.first.send(parser, node)) {
            Trampoline::Value(result) => thunk_parser.then.send(parser, result),
            Trampoline::Thunk(thunk) => {
                Ok(Trampoline::Thunk(Box::new(ThenParser {
                    first: thunk,
                    then: thunk_parser.then
                })))
            }
        }
    }

    fn lbp(&self) -> usize {
        self.first.lbp()
    }
}

fn push_list_value(parser: &mut Parser, closing_token: Token) -> Result<bool, Error> {
    if parser.peek(0) == &Token::Comma {
        parser.advance();
        if parser.peek(0) == &closing_token {
            return Err(parser.err(&closing_token, "invalid token after ','", true));
        }
    }
    if parser.peek(0) == &closing_token {
        parser.advance();
        Ok(true)
    } else {
        Ok(false)
    }
}

struct Parser<'a> {
    /// Parsed tokens
    token_queue: VecDeque<TokenTuple>,
    /// Shared EOF token
    eof_token: Token,
    /// Expression being parsed
    expr: &'a str,
    /// The current character offset in the expression
    offset: usize,
    /// Stack of pending parsers to provide AST nodes.
    thunks: Vec<Box<ThunkParser>>
}

impl<'a> Parser<'a> {
    fn new(expr: &'a str) -> Result<Parser<'a>, Error> {
        Ok(Parser {
            token_queue: try!(tokenize(expr)),
            eof_token: Token::Eof,
            offset: 0,
            expr: expr,
            thunks: vec![]
        })
    }

    fn parse(&mut self) -> ParseResult {
        let result = try!(self.expr());

        // After parsing the expr, we should reach the end of the stream.
        match self.peek(0) {
            &Token::Eof => Ok(result),
            t @ _ => Err(self.err(t, &"Did not parse the complete expression", true))
        }
    }

    #[inline]
    fn advance(&mut self) -> Token {
        self.advance_with_pos().1
    }

    #[inline]
    fn advance_with_pos(&mut self) -> (usize, Token) {
        match self.token_queue.pop_front() {
            Some((pos, tok)) => {
                self.offset = pos;
                (pos, tok)
            },
            None => (self.offset, Token::Eof)
        }
    }

    #[inline]
    fn peek(&self, lookahead: usize) -> &Token {
        match self.token_queue.get(lookahead) {
            Some(&(_, ref t)) => t,
            None => &self.eof_token
        }
    }

    /// Returns a formatted error with the given message.
    fn err(&self, current_token: &Token, error_msg: &str, is_peek: bool) -> Error {
        let mut actual_pos = self.offset;
        let mut buff = error_msg.to_string();
        buff.push_str(&format!(" -- found {:?}", current_token));
        if is_peek {
            if let Some(&(p, _)) = self.token_queue.get(0) {
                actual_pos = p;
            }
        }
        Error::new(&self.expr, actual_pos, ErrorReason::Parse(buff))
    }

    fn expr(&mut self) -> ParseResult {
        let mut rbp = 0;
        'outer: loop {
            match try!(self.nud()) {
                Trampoline::Thunk(thunk) => {
                    // Parsing nud token pushed a thunk, so keep parsing nud tokens.
                    rbp = thunk.lbp();
                    self.thunks.push(thunk);
                },
                Trampoline::Value(mut lhs) => {
                    // Parsing nud returned a value, so parse led until rbp >= lbp
                    'inner: loop {
                        while rbp < self.peek(0).lbp() {
                            lhs = match try!(self.led(lhs)) {
                                Trampoline::Value(node) => node,
                                Trampoline::Thunk(thunk) => {
                                    rbp = thunk.lbp();
                                    self.thunks.push(thunk);
                                    continue 'outer;
                                }
                            };
                        }
                        // Done with lbp, so continue parsing any previous thunks.
                        match self.thunks.pop() {
                            // No thunks are left, so we have our result.
                            None => return Ok(lhs),
                            Some(thunk) => {
                                match try!(thunk.send(self, lhs)) {
                                    // Sending a value returned a value, so it means we will
                                    // continue parsing led tokens at the rbp of the next thunk.
                                    Trampoline::Value(node) => {
                                        lhs = node;
                                        rbp = self.thunks.last().map(|t| t.lbp()).unwrap_or(0);
                                        continue 'inner;
                                    },
                                    Trampoline::Thunk(thunk) => {
                                        // Sending a value returned a thunk, so store the thunk
                                        // in the stack and parse a nud token.
                                        rbp = thunk.lbp();
                                        self.thunks.push(thunk);
                                        continue 'outer;
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    #[inline]
    fn nud(&mut self) -> SendResult {
        let (offset, token) = self.advance_with_pos();
        match token {
            Token::Identifier(value) => {
                Ok(Trampoline::Value(Ast::Field {
                    name: value,
                    offset: offset
                }))
            },
            Token::QuotedIdentifier(value) => {
                match self.peek(0) {
                    &Token::Lparen => {
                        Err(self.err(
                            &Token::Lparen, &"Quoted strings can't be a function name", true))
                    },
                    _ => {
                        Ok(Trampoline::Value(Ast::Field {
                            name: value,
                            offset: offset
                        }))
                    }
                }
            },
            Token::Literal(value) => {
                Ok(Trampoline::Value(Ast::Literal {
                    value: value,
                    offset: offset
                }))
            },
            Token::Lbracket => {
                match self.peek(0) {
                    &Token::Number(_) | &Token::Colon => self.parse_index_expression(),
                    &Token::Star if self.peek(1) == &Token::Rbracket => {
                        self.advance();
                        self.parse_wildcard_index(Ast::Identity { offset: offset })
                    },
                    _ => self.parse_multi_list()
                }
            },
            Token::Lbrace => MultiHashParser::with_key(self, offset, VecDeque::new()),
            Token::At => Ok(Trampoline::Value(Ast::Identity { offset: offset })),
            Token::Flatten => self.parse_flatten(Ast::Identity { offset: offset }),
            Token::Star => self.parse_wildcard_values(Ast::Identity { offset: offset }),
            Token::Ampersand => Ok(Trampoline::Thunk(Box::new(ExprefParser { offset: offset }))),
            Token::Not => Ok(Trampoline::Thunk(Box::new(NotParser { offset: offset }))),
            Token::Filter => self.parse_filter(Ast::Identity { offset: offset }),
            Token::Lparen => Ok(Trampoline::Thunk(Box::new(PrecedenceParenParser))),
            ref t @ _ => Err(self.err(t, &"Unexpected nud token", false))
        }
    }

    #[inline]
    fn led(&mut self, left: Ast) -> SendResult {
        let (offset, token) = self.advance_with_pos();
        match token {
            Token::Dot => {
                if self.peek(0) == &Token::Star {
                    // Skip the star and parse the RHS of the expresson.
                    self.advance();
                    self.parse_wildcard_values(left)
                } else {
                    self.parse_dot_rhs(Box::new(SubexpressionParser {
                        lbp: Token::Dot.lbp(),
                        offset: offset,
                        lhs: left
                    }))
                }
            },
            Token::Pipe => {
                Ok(Trampoline::Thunk(Box::new(SubexpressionParser {
                    lbp: Token::Pipe.lbp(),
                    offset: offset,
                    lhs: left
                })))
            },
            Token::Lbracket => self.parse_led_lbracket(offset, left),
            Token::Or => Ok(Trampoline::Thunk(Box::new(OrParser { offset: offset, lhs: left }))),
            Token::And => Ok(Trampoline::Thunk(Box::new(AndParser { offset: offset, lhs: left }))),
            Token::Lparen => self.parse_function(left, offset),
            Token::Filter => self.parse_filter(left),
            Token::Flatten => self.parse_flatten(left),
            Token::Eq => self.parse_comparator(Comparator::Eq, left),
            Token::Ne => self.parse_comparator(Comparator::Ne, left),
            Token::Gt => self.parse_comparator(Comparator::Gt, left),
            Token::Gte => self.parse_comparator(Comparator::Gte, left),
            Token::Lt => self.parse_comparator(Comparator::Lt, left),
            Token::Lte => self.parse_comparator(Comparator::Lte, left),
            ref t @ _ => Err(self.err(t, "Unexpected led token", false)),
        }
    }

    #[inline]
    fn parse_function(&mut self, lhs: Ast, offset: usize) -> SendResult {
        match lhs {
            Ast::Field { name, .. } => {
                // If no arguments are present, then no need to trampoline.
                if self.peek(0) == &Token::Rparen {
                    self.advance();
                    Ok(Trampoline::Value(Ast::Function {
                        offset: offset,
                        name: name,
                        args: Vec::new()
                    }))
                } else {
                    Ok(Trampoline::Thunk(Box::new(FunctionParser {
                        offset: offset,
                        name: name,
                        args: vec![],
                    })))
                }
            },
            _ => Err(self.err(&Token::Lparen, &"Invalid start of function", false))
        }
    }

    #[inline]
    fn parse_filter(&mut self, lhs: Ast) -> SendResult {
        Ok(Trampoline::Thunk(Box::new(FilterProjectionParser {
            offset: self.offset,
            lhs: lhs,
            predicate: None
        })))
    }

    #[inline]
    fn parse_comparator(&mut self, cmp: Comparator, lhs: Ast) -> SendResult {
        Ok(Trampoline::Thunk(Box::new(ComparisonParser {
            offset: self.offset,
            cmp: cmp,
            lhs: lhs
        })))
    }

    #[inline]
    fn parse_flatten(&mut self, lhs: Ast) -> SendResult {
        let offset = self.offset;
        self.projection_rhs(Box::new(FlattenProjectionParser {
            offset: offset,
            lhs: lhs
        }))
    }

    #[inline]
    fn parse_wildcard_values(&mut self, lhs: Ast) -> SendResult {
        let offset = self.offset;
        self.projection_rhs(Box::new(WildcardValuesParser {
            offset: offset,
            lhs: lhs
        }))
    }

    #[inline]
    fn parse_wildcard_index(&mut self, lhs: Ast) -> SendResult {
        let offset = self.offset;
        match self.advance() {
            Token::Rbracket => {
                self.projection_rhs(Box::new(WildcardIndexParser {
                    offset: offset,
                    lhs: lhs
                }))
            },
            ref t @ _ => Err(self.err(t, &"Expected ']' for wildcard index", false))
        }
    }

    /// Parses the right hand side of a projection, using the given LBP to
    /// determine when to stop consuming tokens.
    #[inline]
    fn projection_rhs(&mut self, then: Box<ThunkParser>) -> SendResult {
        match match self.peek(0) {
            &Token::Dot => 0,
            &Token::Lbracket | &Token::Filter => 1,
            ref t @ _ if t.lbp() < 10 => 2,
            ref t @ _ => return Err(self.err(t, &"Expected '.', '[', or '[?'", true))
        } {
            0 => {
                self.advance();
                self.parse_dot_rhs(then)
            },
            1 => Ok(Trampoline::Thunk(then)),
            _ => {
                let offset = self.offset;
                then.send(self, Ast::Identity { offset: offset })
            }
        }
    }

    /// Parses the right hand side of a dot expression.
    #[inline]
    fn parse_dot_rhs(&mut self, then: Box<ThunkParser>) -> SendResult {
        match match self.peek(0) {
            &Token::Lbracket => true,
            &Token::Identifier(_) | &Token::QuotedIdentifier(_) | &Token::Star | &Token::Lbrace
                | &Token::Ampersand => false,
            t @ _ => {
                return Err(self.err(t, &"Expected identifier, '*', '{', '[', '&', or '[?'", true))
            }
        } {
            true => {
                self.advance();
                self.parse_multi_list()
            },
            false => Ok(Trampoline::Thunk(then))
        }
    }

    // Parses foo[0], foo[::-1], foo[*], foo.[a, b, c], etc...
    #[inline]
    fn parse_led_lbracket(&mut self, offset: usize, lhs: Ast) -> SendResult {
        match match self.peek(0) {
            &Token::Number(_) | &Token::Colon => true,
            &Token::Star => false,
            t @ _ => return Err(self.err(t, "Expected number, ':', or '*'", true))
        } {
            false => {
                self.advance();
                self.parse_wildcard_index(lhs)
            },
            true => {
                match try!(self.parse_index_expression()) {
                    // The parsed value was an index, so return the subexpr.
                    Trampoline::Value(node) => Ok(Trampoline::Value(Ast::Subexpr {
                        offset: offset,
                        lhs: Box::new(lhs),
                        rhs: Box::new(node)
                    })),
                    // The parsed value is a projection, so wrap it when done.
                    Trampoline::Thunk(thunk) => {
                        Ok(Trampoline::Thunk(Box::new(ThenParser {
                            first: thunk,
                            then: Box::new(SubexpressionParser {
                                lbp: Token::Lbracket.lbp(),
                                offset: offset,
                                lhs: lhs
                            })
                        })))
                    }
                }
            }
        }
    }

    /// Parses [0], [::-1], [0:-1], [0:1], etc...
    #[inline]
    fn parse_index_expression(&mut self) -> SendResult {
        let mut parts = [None, None, None];
        let mut pos = 0;
        loop {
            match self.advance() {
                Token::Number(value) => {
                    parts[pos] = Some(value);
                    match self.peek(0) {
                        &Token::Colon | &Token::Rbracket => (),
                        t @ _ => return Err(self.err(t, "Expected ':', or ']'", true))
                    };
                },
                Token::Rbracket => break,
                Token::Colon if pos >= 2 => {
                    return Err(self.err(&Token::Colon, "Too many colons in slice expr", false));
                },
                Token::Colon => {
                    pos += 1;
                    match self.peek(0) {
                        &Token::Number(_) | &Token::Colon | &Token::Rbracket => continue,
                        ref t @ _ => return Err(self.err(t, "Expected number, ':', or ']'", true))
                    };
                },
                ref t @ _ => return Err(self.err(t, "Expected number, ':', or ']'", false)),
            }
        }

        if pos == 0 {
            // No colons were found, so this is a simple index extraction.
            Ok(Trampoline::Value(Ast::Index {
                offset: self.offset,
                idx: parts[0].unwrap()
            }))
        } else {
            // Sliced array from start (e.g., [2:])
            let offset = self.offset;
            self.projection_rhs(
                Box::new(SliceProjectionParser {
                    offset: offset,
                    start: parts[0],
                    stop: parts[1],
                    step: parts[2].unwrap_or(1)
                })
            )
        }
    }

    #[inline]
    fn parse_multi_list(&mut self) -> SendResult {
        Ok(Trampoline::Thunk(Box::new(MultiListParser {
            offset: self.offset,
            elements: vec![]
        })))
    }
}

#[cfg(test)]
mod test {
    use super::ComparisonParser;
    use ast::{Ast, Comparator};
    use lexer::Token;

    #[test]
    fn gets_comparator_lbp() {
        use super::ThunkParser;
        let node = Ast::Identity { offset: 0 };
        let p = ComparisonParser { offset: 0, cmp: Comparator::Eq, lhs: node.clone() };
        assert_eq!(Token::Eq.lbp(), p.lbp());
        let p = ComparisonParser { offset: 0, cmp: Comparator::Gt, lhs: node.clone() };
        assert_eq!(Token::Gt.lbp(), p.lbp());
        let p = ComparisonParser { offset: 0, cmp: Comparator::Lt, lhs: node.clone() };
        assert_eq!(Token::Lt.lbp(), p.lbp());
        let p = ComparisonParser { offset: 0, cmp: Comparator::Ne, lhs: node.clone() };
        assert_eq!(Token::Ne.lbp(), p.lbp());
    }
}
