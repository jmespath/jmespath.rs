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

use super::{Error, ErrorReason};
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
    Thunk(ThunkParser),
}

enum ThunkParser {
    Subexpression {
        lbp: usize,
        offset: usize,
        lhs: Box<Ast>,
    },
    SliceProjection {
        offset: usize,
        start: Option<i32>,
        stop: Option<i32>,
        step: i32,
    },
    FilterProjection {
        offset: usize,
        lhs: Box<Ast>,
        predicate: Option<Box<Ast>>,
        lbp: usize,
    },
    Comparison {
        offset: usize,
        cmp: Comparator,
        lhs: Box<Ast>,
    },
    MultiList {
        offset: usize,
        elements: Vec<Ast>,
    },
    MultiHash {
        offset: usize,
        key: Option<String>,
        elements: Vec<KeyValuePair>,
    },
    Function {
        name: String,
        offset: usize,
        args: Vec<Ast>,
    },
    Or {
        offset: usize,
        lhs: Box<Ast>,
    },
    And {
        offset: usize,
        lhs: Box<Ast>,
    },
    Not {
        offset: usize,
    },
    Expref {
        offset: usize,
    },
    PrecedenceParen,
    WildcardIndex {
        offset: usize,
        lhs: Box<Ast>,
    },
    WildcardValues {
        offset: usize,
        lhs: Box<Ast>,
    },
    Flatten {
        offset: usize,
        lhs: Box<Ast>,
    },
    Then {
        first: Box<ThunkParser>,
        then: Box<ThunkParser>,
    },
}

impl ThunkParser {
    /// Sends an AST node into the parser, completing or continuing it
    fn send(self, parser: &mut Parser, node: Ast) -> SendResult {
        match self {
            ThunkParser::Subexpression {offset, lhs, ..} => {
                Ok(Trampoline::Value(Ast::Subexpr {
                    offset: offset,
                    lhs: lhs,
                    rhs: Box::new(node),
                }))
            },
            ThunkParser::SliceProjection {offset, start, stop, step} => {
                Ok(Trampoline::Value(Ast::Projection {
                    offset: offset,
                    lhs: Box::new(Ast::Slice {
                        offset: offset,
                        start: start,
                        stop: stop,
                        step: step
                    }),
                    rhs: Box::new(node),
                }))
            },
            ThunkParser::FilterProjection {offset, lhs, predicate, ..} => {
                match predicate {
                    None => {
                        // After receiving the parsed predicate, parse the projection.
                        match parser.advance() {
                            // Ensure the ']' was closed
                            Token::Rbracket => {
                                parser.projection_rhs(ThunkParser::FilterProjection {
                                    offset: offset,
                                    lhs: lhs,
                                    predicate: Some(Box::new(node)),
                                    lbp: Token::Star.lbp(),
                                })
                            },
                            ref t => Err(parser.err(t, &"Expected ']'", false))
                        }
                    },
                    Some(predicate) => {
                        Ok(Trampoline::Value(Ast::Projection {
                            offset: offset,
                            lhs: lhs,
                            rhs: Box::new(Ast::Condition {
                                offset: offset,
                                predicate: predicate,
                                then: Box::new(node),
                           })
                       }))
                    }
                }
            },
            ThunkParser::Comparison {offset, cmp, lhs} => {
                Ok(Trampoline::Value(Ast::Comparison {
                    offset: offset,
                    comparator: cmp,
                    lhs: lhs,
                    rhs: Box::new(node),
                }))
            },
            ThunkParser::MultiList {offset, mut elements} => {
                elements.push(node);
                if try!(push_list_value(parser, Token::Rbracket)) {
                    Ok(Trampoline::Value(Ast::MultiList {
                        offset: offset,
                        elements: elements,
                    }))
                } else {
                    Ok(Trampoline::Thunk(ThunkParser::MultiList {
                        offset: offset,
                        elements: elements,
                    }))
                }
            },
            ThunkParser::MultiHash {offset, mut key, mut elements} => {
                elements.push(KeyValuePair {
                    key: key.take().unwrap(),
                    value: node,
                });
                match parser.advance() {
                    Token::Rbrace => {
                        Ok(Trampoline::Value(Ast::MultiHash {
                            offset: offset,
                            elements: elements
                        }))
                    },
                    Token::Comma => ThunkParser::hash_with_key(parser, offset, elements),
                    ref t => Err(parser.err(t, "Expected '}' or ','", false))
                }
            },
            ThunkParser::Function {name, offset, mut args} => {
                args.push(node);
                if try!(push_list_value(parser, Token::Rparen)) {
                    Ok(Trampoline::Value(Ast::Function {offset: offset, name: name, args: args}))
                } else {
                    Ok(Trampoline::Thunk(ThunkParser::Function {
                        name: name,
                        offset: offset,
                        args: args,
                    }))
                }
            },
            ThunkParser::Or {offset, lhs} => {
                Ok(Trampoline::Value(Ast::Or {
                    offset: offset,
                    lhs: lhs,
                    rhs: Box::new(node),
                }))
            },
            ThunkParser::And {offset, lhs} => {
                Ok(Trampoline::Value(Ast::And {
                    offset: offset,
                    lhs: lhs,
                    rhs: Box::new(node),
                }))
            },
            ThunkParser::Not {offset} => {
                Ok(Trampoline::Value(Ast::Not {
                    offset: offset,
                    node: Box::new(node),
                }))
            },
            ThunkParser::Expref {offset} => {
                Ok(Trampoline::Value(Ast::Expref {
                    offset: offset,
                    ast: Box::new(node),
                }))
            },
            ThunkParser::PrecedenceParen => {
                match parser.advance() {
                    Token::Rparen => Ok(Trampoline::Value(node)),
                    ref t => Err(parser.err(t, "Expected ')' to close '('", false))
                }
            },
            ThunkParser::WildcardIndex {offset, lhs} => {
                Ok(Trampoline::Value(Ast::Projection {
                    offset: offset,
                    lhs: lhs,
                    rhs: Box::new(node),
                }))
            },
            ThunkParser::WildcardValues {offset, lhs} => {
                Ok(Trampoline::Value(Ast::Projection {
                    offset: offset,
                    lhs: Box::new(Ast::ObjectValues {
                        offset: offset,
                        node: lhs,
                    }),
                    rhs: Box::new(node),
                }))
            },
            ThunkParser::Flatten {offset, lhs} => {
                Ok(Trampoline::Value(Ast::Projection {
                    offset: offset,
                    lhs: Box::new(Ast::Flatten {
                        offset: offset,
                        node: lhs,
                    }),
                    rhs: Box::new(node),
                }))
            },
            ThunkParser::Then {first, then} => {
                match try!(first.send(parser, node)) {
                    Trampoline::Value(result) => then.send(parser, result),
                    Trampoline::Thunk(thunk) => {
                        Ok(Trampoline::Thunk(ThunkParser::Then {
                            first: Box::new(thunk),
                            then: then,
                        }))
                    }
                }
            },
        }
    }

    /// Get the left binding power of the parser.
    fn lbp(&self) -> usize {
        match *self {
            ThunkParser::Subexpression { lbp, .. } => lbp,
            ThunkParser::SliceProjection {..} => Token::Star.lbp(),
            ThunkParser::FilterProjection {lbp, ..} => lbp,
            ThunkParser::Comparison {..} => Token::Eq.lbp(),
            ThunkParser::MultiList {..} => 0,
            ThunkParser::MultiHash {..} => 0,
            ThunkParser::Function {..} => 0,
            ThunkParser::Or {..} => Token::Or.lbp(),
            ThunkParser::And {..} => Token::And.lbp(),
            ThunkParser::Not {..} => Token::Not.lbp(),
            ThunkParser::Expref {..} => Token::Ampersand.lbp(),
            ThunkParser::PrecedenceParen {..} => 0,
            ThunkParser::WildcardIndex {..} => Token::Star.lbp(),
            ThunkParser::WildcardValues {..} => Token::Star.lbp(),
            ThunkParser::Flatten {..} => Token::Flatten.lbp(),
            ThunkParser::Then {ref first, ..} => first.lbp(),
        }
    }

    /// Creates a new MultiHashParser with an added key from the parser.
    fn hash_with_key(parser: &mut Parser, offset: usize, elements: Vec<KeyValuePair>)
            -> SendResult {
        // Ensure the key is valid
        let key_name = try!(match parser.advance() {
            Token::Identifier(v) => Ok(v),
            Token::QuotedIdentifier(v) => Ok(v),
            ref t => Err(parser.err(t, &"Invalid key value pair", false))
        });
        // Ensure that the key is followed by ":"
        match parser.advance() {
            Token::Colon =>  {
                Ok(Trampoline::Thunk(ThunkParser::MultiHash {
                    key: Some(key_name),
                    offset: offset,
                    elements: elements
                }))
            },
            ref t => Err(parser.err(t, &"Expected ':' to follow key", true))
        }
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
    thunks: Vec<ThunkParser>,
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
        match *self.peek(0) {
            Token::Eof => Ok(result),
            ref t => Err(self.err(t, &"Did not parse the complete expression", true))
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
        let mut buff = error_msg.to_owned();
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
                                        rbp = self.thunks.last().map_or(0, |t| t.lbp());
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
                match *self.peek(0) {
                    Token::Lparen => {
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
                    value: *value,
                    offset: offset
                }))
            },
            Token::Lbracket => {
                match *self.peek(0) {
                    Token::Number(_) | Token::Colon => self.parse_index_expression(),
                    Token::Star if self.peek(1) == &Token::Rbracket => {
                        self.advance();
                        self.parse_wildcard_index(Ast::Identity { offset: offset })
                    },
                    _ => self.parse_multi_list()
                }
            },
            Token::Lbrace => ThunkParser::hash_with_key(self, offset, Vec::new()),
            Token::At => Ok(Trampoline::Value(Ast::Identity { offset: offset })),
            Token::Flatten => self.parse_flatten(Ast::Identity { offset: offset }),
            Token::Star => self.parse_wildcard_values(Ast::Identity { offset: offset }),
            Token::Ampersand => Ok(Trampoline::Thunk(ThunkParser::Expref { offset: offset })),
            Token::Not => Ok(Trampoline::Thunk(ThunkParser::Not { offset: offset })),
            Token::Filter => self.parse_filter(Ast::Identity { offset: offset }),
            Token::Lparen => Ok(Trampoline::Thunk(ThunkParser::PrecedenceParen)),
            ref t => Err(self.err(t, &"Unexpected nud token", false))
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
                    self.parse_dot_rhs(ThunkParser::Subexpression {
                        lbp: Token::Dot.lbp(),
                        offset: offset,
                        lhs: Box::new(left),
                    })
                }
            },
            Token::Pipe => {
                Ok(Trampoline::Thunk(ThunkParser::Subexpression {
                    lbp: Token::Pipe.lbp(),
                    offset: offset,
                    lhs: Box::new(left),
                }))
            },
            Token::Lbracket => self.parse_led_lbracket(offset, left),
            Token::Or => {
                Ok(Trampoline::Thunk(ThunkParser::Or {
                    offset: offset,
                    lhs: Box::new(left),
                }))
            },
            Token::And => {
                Ok(Trampoline::Thunk(ThunkParser::And {
                    offset: offset,
                    lhs: Box::new(left),
                }))
            },
            Token::Lparen => self.parse_function(left, offset),
            Token::Filter => self.parse_filter(left),
            Token::Flatten => self.parse_flatten(left),
            Token::Eq | Token::Ne | Token::Gt | Token::Gte | Token::Lt | Token::Lte => {
                self.parse_comparator(Comparator::from(token), left)
            },
            ref t => Err(self.err(t, "Unexpected led token", false)),
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
                    Ok(Trampoline::Thunk(ThunkParser::Function {
                        offset: offset,
                        name: name,
                        args: vec![],
                    }))
                }
            },
            _ => Err(self.err(&Token::Lparen, &"Invalid start of function", false))
        }
    }

    #[inline]
    fn parse_filter(&mut self, lhs: Ast) -> SendResult {
        Ok(Trampoline::Thunk(ThunkParser::FilterProjection {
            offset: self.offset,
            lhs: Box::new(lhs),
            predicate: None,
            lbp: 0,
        }))
    }

    #[inline]
    fn parse_comparator(&mut self, cmp: Comparator, lhs: Ast) -> SendResult {
        Ok(Trampoline::Thunk(ThunkParser::Comparison {
            offset: self.offset,
            cmp: cmp,
            lhs: Box::new(lhs),
        }))
    }

    #[inline]
    fn parse_flatten(&mut self, lhs: Ast) -> SendResult {
        let offset = self.offset;
        self.projection_rhs(ThunkParser::Flatten {
            offset: offset,
            lhs: Box::new(lhs),
        })
    }

    #[inline]
    fn parse_wildcard_values(&mut self, lhs: Ast) -> SendResult {
        let offset = self.offset;
        self.projection_rhs(ThunkParser::WildcardValues {
            offset: offset,
            lhs: Box::new(lhs),
        })
    }

    #[inline]
    fn parse_wildcard_index(&mut self, lhs: Ast) -> SendResult {
        let offset = self.offset;
        match self.advance() {
            Token::Rbracket => {
                self.projection_rhs(ThunkParser::WildcardIndex {
                    offset: offset,
                    lhs: Box::new(lhs),
                })
            },
            ref t => Err(self.err(t, &"Expected ']' for wildcard index", false))
        }
    }

    /// Parses the right hand side of a projection, using the given LBP to
    /// determine when to stop consuming tokens.
    #[inline]
    fn projection_rhs(&mut self, then: ThunkParser) -> SendResult {
        match match *self.peek(0) {
            Token::Dot => 0,
            Token::Lbracket | Token::Filter => 1,
            ref t if t.lbp() < 10 => 2,
            ref t => return Err(self.err(t, &"Expected '.', '[', or '[?'", true))
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
    fn parse_dot_rhs(&mut self, then: ThunkParser) -> SendResult {
        let is_next_lbracket = match *self.peek(0) {
            Token::Lbracket => true,
            Token::Identifier(_) | Token::QuotedIdentifier(_) | Token::Star | Token::Lbrace
                | Token::Ampersand => false,
            ref t => {
                return Err(self.err(t, &"Expected identifier, '*', '{', '[', '&', or '[?'", true))
            }
        };
        if is_next_lbracket {
            self.advance();
            self.parse_multi_list()
        } else {
            Ok(Trampoline::Thunk(then))
        }
    }

    // Parses foo[0], foo[::-1], foo[*], foo.[a, b, c], etc...
    #[inline]
    fn parse_led_lbracket(&mut self, offset: usize, lhs: Ast) -> SendResult {
        let is_next_star = match *self.peek(0) {
            Token::Star => true,
            Token::Number(_) | Token::Colon => false,
            ref t => return Err(self.err(t, "Expected number, ':', or '*'", true))
        };
        if is_next_star {
            self.advance();
            self.parse_wildcard_index(lhs)
        } else {
            match try!(self.parse_index_expression()) {
                // The parsed value was an index, so return the subexpr.
                Trampoline::Value(node) => Ok(Trampoline::Value(Ast::Subexpr {
                    offset: offset,
                    lhs: Box::new(lhs),
                    rhs: Box::new(node),
                })),
                // The parsed value is a projection, so wrap it when done.
                Trampoline::Thunk(thunk) => {
                    Ok(Trampoline::Thunk(ThunkParser::Then {
                        first: Box::new(thunk),
                        then: Box::new(ThunkParser::Subexpression {
                            lbp: Token::Lbracket.lbp(),
                            offset: offset,
                            lhs: Box::new(lhs),
                        })
                    }))
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
                    match *self.peek(0) {
                        Token::Colon | Token::Rbracket => (),
                        ref t => return Err(self.err(t, "Expected ':', or ']'", true))
                    };
                },
                Token::Rbracket => break,
                Token::Colon if pos >= 2 => {
                    return Err(self.err(&Token::Colon, "Too many colons in slice expr", false));
                },
                Token::Colon => {
                    pos += 1;
                    match *self.peek(0) {
                        Token::Number(_) | Token::Colon | Token::Rbracket => continue,
                        ref t => return Err(self.err(t, "Expected number, ':', or ']'", true))
                    };
                },
                ref t => return Err(self.err(t, "Expected number, ':', or ']'", false)),
            }
        }

        if pos == 0 {
            // No colons were found, so this is a simple index extraction.
            Ok(Trampoline::Value(Ast::Index {
                offset: self.offset,
                idx: parts[0].unwrap(),
            }))
        } else {
            // Sliced array from start (e.g., [2:])
            let offset = self.offset;
            self.projection_rhs(ThunkParser::SliceProjection {
                offset: offset,
                start: parts[0],
                stop: parts[1],
                step: parts[2].unwrap_or(1)
            })
        }
    }

    #[inline]
    fn parse_multi_list(&mut self) -> SendResult {
        Ok(Trampoline::Thunk(ThunkParser::MultiList {
            offset: self.offset,
            elements: vec![]
        }))
    }
}
