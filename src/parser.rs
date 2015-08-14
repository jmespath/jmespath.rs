//! Module for parsing JMESPath expressions into an AST.

extern crate rustc_serialize;

use std::iter::Peekable;

use ast::{Ast, Comparator};
use lexer::{Lexer, Token};

/// An alias for computations that can return an `Ast` or `ParseError`.
pub type ParseResult = Result<Ast, ParseError>;
type ParseStep = Result<Token, ParseError>;

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

/// Operators are pushed onto the operator stack.
#[derive(Debug, PartialEq)]
enum Operator {
    Basic(Token),
    Function(String, Vec<Ast>),
    MultiList(Vec<Ast>),
    ArrayProjection,
    SliceProjection(Option<i32>, Option<i32>, Option<i32>)
}

impl Operator {
    /// Returns true if the current operator has a precedence < operator.
    /// This function takes operator associativity into account. Left
    /// associative operators check with <, while right associative check
    /// with <=.
    #[inline]
    pub fn has_lower_precedence(&self, op: &Operator) -> bool {
        if self.is_right_associative() {
            self.precedence() < op.precedence()
        } else {
            self.precedence() <= op.precedence()
        }
    }

    /// Determines if the operator is right associative (e.g., projections).
    #[inline]
    pub fn is_right_associative(&self) -> bool {
        match self {
            &Operator::Basic(ref p) if p == &Token::Star => true,
            &Operator::Basic(ref p) if p == &Token::Filter => true,
            &Operator::ArrayProjection => true,
            &Operator::SliceProjection(_, _, _) => true,
            _ => false
        }
    }

    /// Retrieves the precedence of an operator.
    #[inline]
    pub fn precedence(&self) -> usize {
        match self {
            &Operator::Basic(ref p) => p.lbp(),
            &Operator::Function(_, _) => 0,
            &Operator::ArrayProjection => Token::Star.lbp(),
            &Operator::SliceProjection(_, _, _) => Token::Star.lbp(),
            &Operator::MultiList(_) => Token::Lparen.lbp()
        }
    }

    #[inline]
    pub fn is_binary(&self) -> bool {
        match self {
            &Operator::Basic(ref p) if p == &Token::Ampersand => false,
            &Operator::Basic(ref p) if p == &Token::Not => false,
            _ => true
        }
    }

    // Returns true if the token closes the passed in token.
    pub fn closes(&self, token: &Token) -> bool {
        match self {
            &Operator::Basic(ref p) if p == &Token::Lparen && token == &Token::Rparen => true,
            &Operator::Basic(ref p) if p == &Token::Lbrace && token == &Token::Rbrace => true,
            &Operator::Function(_, _) if token == &Token::Rparen => true,
            &Operator::MultiList(_) if token == &Token::Rbracket => true,
            _ => false
        }
    }

    // Returns true if the token supports commas.
    pub fn supports_comma(&self) -> bool {
        match self {
            &Operator::MultiList(_) | &Operator::Function(_, _) => true,
            _ => false
        }
    }
}

/// Parse state tracks whether we are parsing nud or led and precedence.
/// Parse states are pushed onto the parse_state stack.
#[derive(Debug, PartialEq)]
enum State {
    Nud(usize),
    Led(usize)
}

/// JMESPath parser. Returns an Ast
pub struct Parser<'a> {
    /// Token stream
    stream: Peekable<Lexer<'a>>,
    /// Expression being parsed
    expr: String,
    /// The current character offset in the expression
    pos: usize,
    /// Operand queue containing AST nodes.
    output_stack: Vec<Ast>,
    /// Operator stack containing operator states.
    operator_stack: Vec<Operator>,
    /// Stack of led RBP values to parse.
    state_stack: Vec<State>
}

impl<'a> Parser<'a> {
    // Constructs a new lexer using the given expression string.
    pub fn new(expr: &'a str) -> Parser<'a> {
        Parser {
            stream: Lexer::new(expr).peekable(),
            expr: expr.to_string(),
            pos: 0,
            operator_stack: vec!(),
            output_stack: vec!(),
            state_stack: vec!()
        }
    }

    /// Parses the expression into result containing an AST or ParseError.
    pub fn parse(&mut self) -> ParseResult {
        let result = try!(self.expr());
        // After parsing the expr, we should reach the end of the stream.
        match self.stream.next() {
            None | Some((_, Token::Eof)) => Ok(result),
            token @ _ => Err(self.err(&token.unwrap().1, &"Did not reach token stream EOF"))
        }
    }

    #[inline]
    fn expr(&mut self) -> ParseResult {
        self.state_stack.push(State::Nud(0));
        let mut token = self.advance();
        while token != Token::Eof {
            match self.state_stack.last() {
                Some(&State::Nud(rbp)) => {
                    self.state_stack.pop();
                    token = try!(self.nud(token));
                    self.state_stack.push(State::Led(rbp));
                },
                Some(&State::Led(rbp)) => {
                    if rbp < token.lbp() {
                        token = try!(self.led(token));
                    } else {
                        self.state_stack.pop();
                        if token == Token::Rparen {
                            token = try!(self.close_paren());
                        } else if token == Token::Rbracket {
                            token = try!(self.close_multi_list());
                        } else if token == Token::Comma {
                            token = try!(self.parse_comma());
                            self.state_stack.push(State::Nud(0));
                        }
                    }
                },
                None => break
            }
        }
        // Pop and process any remaining operators on the stack.
        while !self.operator_stack.is_empty() {
            token = try!(self.pop_token(token));
        }
        if self.output_stack.len() != 1 {
            Err(self.err(&token, &format!("Multiple values left on output stack: {:?}",
                                          self.output_stack)))
        } else {
            Ok(self.output_stack.pop().unwrap())
        }
    }

    #[inline]
    fn nud(&mut self, token: Token) -> ParseStep {
        // First match tokens that do not need to be copied.
        match token {
            Token::Identifier(value) => {
                self.output_stack.push(Ast::Identifier(value));
                Ok(self.advance())
            },
            Token::Literal(value) => {
                self.output_stack.push(Ast::Literal(value));
                Ok(self.advance())
            },
            Token::QuotedIdentifier(ref value) => {
                match self.advance() {
                    Token::Lparen =>
                        Err(self.err(&token, &"Quoted strings can't be function names")),
                    next_token @ _ => {
                        self.output_stack.push(Ast::Identifier(value.clone()));
                        Ok(next_token)
                    }
                }
            },
            Token::At => {
                self.output_stack.push(Ast::CurrentNode);
                Ok(self.advance())
            },
            Token::Star => {
                self.output_stack.push(Ast::CurrentNode);
                let next_token = self.advance();
                self.projection_rhs(next_token, Operator::Basic(Token::Star))
            },
            Token::Flatten => {
                self.output_stack.push(Ast::CurrentNode);
                let next_token = self.advance();
                self.projection_rhs(next_token, Operator::Basic(Token::Flatten))
            },
            Token::Filter => {
                self.output_stack.push(Ast::CurrentNode);
                let next_token = self.advance();
                self.projection_rhs(next_token, Operator::Basic(Token::Filter))
            },
            Token::Lbrace => {
                let next_token = self.advance();
                self.operator(next_token, Operator::MultiList(vec!()))
            },
            Token::Ampersand => {
                let next_token = self.advance();
                self.operator(next_token, Operator::Basic(Token::Ampersand))
            },
            Token::Lbracket => self.parse_lbracket(true),
            ref tok @ _ => Err(self.err(tok, &format!("Unexpected nud token: {}",
                                                      tok.token_name()))),
        }
    }

    #[inline]
    fn led(&mut self, token: Token) -> ParseStep {
        // More easily advance and push a basic operator.
        macro_rules! next_op {
            ($x:expr) => {{
                let next_token = self.advance();
                self.operator(next_token, Operator::Basic($x))
            }};
        }
        match token {
            Token::Dot => {
                match self.stream.peek() {
                    Some(&(_, Token::Star)) => {
                        self.advance();
                        let next_token = self.advance();
                        self.projection_rhs(next_token, Operator::Basic(Token::Star))
                    },
                    _ => self.parse_dot(Operator::Basic(Token::Dot))
                }
            },
            Token::Flatten => {
                let next_token = self.advance();
                self.projection_rhs(next_token, Operator::Basic(Token::Flatten))
            },
            Token::Lbracket => self.parse_lbracket(false),
            Token::Or => next_op!(Token::Or),
            Token::Pipe => next_op!(Token::Pipe),
            Token::Lt => next_op!(Token::Lt),
            Token::Lte => next_op!(Token::Lte),
            Token::Gt => next_op!(Token::Gt),
            Token::Gte => next_op!(Token::Gte),
            Token::Eq => next_op!(Token::Eq),
            Token::Ne => next_op!(Token::Ne),
            Token::Lparen => {
                match self.output_stack.pop() {
                    // A "(" preceded by an identifier means that it is a function call.
                    Some(Ast::Identifier(fn_name)) => self.open_function(fn_name),
                    // TODO: Implement parenthesis as a precedence mechanism. This will require
                    // a new JEP to be added into JMESPath
                    _ => Err(self.err(&token, &format!("Unexpected parenthesis"))),
                }
            },
            _ => Err(self.err(&token, &format!("Unexpected led token: {}", token.token_name()))),
        }
    }

    #[inline]
    fn open_function(&mut self, fn_name: String) -> ParseStep {
        match self.advance() {
            Token::Rparen => {
                self.output_stack.push(Ast::Function(fn_name, vec!()));
                Ok(self.advance())
            },
            next_token @ _ => self.operator(next_token, Operator::Function(fn_name, vec!()))
        }
    }

    #[inline]
    fn parse_lbracket(&mut self, is_nud: bool) -> ParseStep {
        // Skip the bracket "["
        let token = self.advance();
        match self.stream.peek() {
            Some(&(_, Token::Rbracket)) => {
                match token {
                    Token::Number(value) => {
                        if is_nud {
                            self.output_stack.push(Ast::Index(value));
                        } else {
                            let lhs = self.output_stack.pop().unwrap();
                            self.output_stack.push(
                                Ast::Subexpr(Box::new(lhs), Box::new(Ast::Index(value))));
                        }
                        // Skip the Rbracket token.
                        self.advance();
                        Ok(self.advance())
                    },
                    Token::Star => {
                        if is_nud {
                            self.output_stack.push(Ast::CurrentNode);
                        }
                        // Skip Rbracket
                        self.advance();
                        let next_token = self.advance();
                        self.projection_rhs(next_token, Operator::ArrayProjection)
                    },
                    Token::Colon => {
                        if is_nud {
                            self.output_stack.push(Ast::CurrentNode);
                        }
                        // Skip Rbracket
                        self.advance();
                        let next_token = self.advance();
                        self.projection_rhs(
                            next_token, Operator::SliceProjection(None, None, None))
                    },
                    _ => Err(self.err(&token, "Expected number, ':', or '*'")),
                }
            },
            _ => self.operator(token, Operator::MultiList(vec!()))
        }
    }

    #[inline]
    fn operator(&mut self, mut token: Token, operator: Operator) -> ParseStep {
        self.state_stack.push(State::Nud(operator.precedence()));
        // Pop things from the top of the operator stack that have a higher precedence.
        while self.is_last_gt(&operator) {
            token = try!(self.pop_token(token))
        }
        self.operator_stack.push(operator);
        Ok(token)
    }

    #[inline]
    fn is_last_gt(&self, op: &Operator) -> bool {
        match self.operator_stack.last() {
            Some(operator) if op.has_lower_precedence(operator) => true,
            _ => false
        }
    }

    #[inline]
    fn is_last_closing(&self, token: &Token) -> bool {
        match self.operator_stack.last() {
            Some(operator) if operator.closes(token) => true,
            _ => false
        }
    }

    #[inline]
    fn does_last_support_comma(&self) -> bool {
        match self.operator_stack.last() {
            Some(operator) if operator.supports_comma() => true,
            _ => false
        }
    }

    #[inline]
    fn close_paren(&mut self) -> ParseStep {
        loop {
            if self.is_last_closing(&Token::Rparen) {
                match self.operator_stack.pop().unwrap() {
                    Operator::Function(name, mut args) => {
                        args.push(self.output_stack.pop().unwrap());
                        self.output_stack.push(Ast::Function(name, args));
                    },
                    _ => panic!() // TODO: Implement simple precedence parens.
                };
                return Ok(self.advance());
            } else if self.operator_stack.is_empty() {
                return Err(ParseError::new(&self.expr, self.pos,
                                           "Unclosed parenthesis", &"".to_string()));
            } else {
                try!(self.pop_token(Token::Rparen));
            }
        }
    }

    #[inline]
    fn close_multi_list(&mut self) -> ParseStep {
        loop {
            if self.is_last_closing(&Token::Rbracket) {
                match self.operator_stack.pop().unwrap() {
                    Operator::MultiList(mut args) => {
                        args.push(self.output_stack.pop().unwrap());
                        self.output_stack.push(Ast::MultiList(args));
                    },
                    _ => return Err(ParseError::new(&self.expr, self.pos,
                                                    "Misplaced \"]\"", &"".to_string()))
                };
                return Ok(self.advance());
            } else if self.operator_stack.is_empty() {
                return Err(ParseError::new(&self.expr, self.pos,
                                           "Unclosed \"]\"", &"".to_string()));
            } else {
                try!(self.pop_token(Token::Rbracket));
            }
        }
    }

    #[inline]
    fn parse_comma(&mut self) -> ParseStep {
        loop {
            if self.does_last_support_comma() {
                match self.operator_stack.pop().unwrap() {
                    Operator::Function(fn_name, mut args) => {
                        args.push(self.output_stack.pop().unwrap());
                        self.operator_stack.push(Operator::Function(fn_name, args));
                    },
                    Operator::MultiList(mut args) => {
                        args.push(self.output_stack.pop().unwrap());
                        self.operator_stack.push(Operator::MultiList(args));
                    },
                    _ => panic!() // TODO: Implement simple precedence parens.
                };
                return Ok(self.advance());
            } else if self.operator_stack.is_empty() {
                return Err(ParseError::new(&self.expr, self.pos,
                                           "Misplaced comma", &"".to_string()));
            } else {
                try!(self.pop_token(Token::Comma));
            }
        }
    }

    #[inline]
    fn pop_token(&mut self, token: Token) -> ParseStep {
        let operator = self.operator_stack.pop().unwrap();
        if operator.is_binary() {
            let rhs = self.output_stack.pop().unwrap();
            let lhs = self.output_stack.pop().unwrap();
            match operator {
                Operator::Basic(tok) => try!(self.pop_basic_binary(tok, lhs, rhs)),
                Operator::ArrayProjection => self.output_stack.push(
                    Ast::Projection(Box::new(lhs), Box::new(rhs))),
                Operator::Function(fn_name, _) => panic!(),
                Operator::MultiList(_) => panic!("Not implemented yet"),
                Operator::SliceProjection(start, step, stop) => panic!(),
            };
        } else {
            let output = self.output_stack.pop().unwrap();
            match operator {
                Operator::Basic(ref tok) if tok == &Token::Ampersand =>
                    self.output_stack.push(Ast::Expref(Box::new(output))),
                _ => return Err(self.err(&token, &"Unexpected unary operator"))
            }
        }
        Ok(token)
    }

    #[inline]
    fn pop_basic_binary(&mut self, tok: Token, lhs: Ast, rhs: Ast) -> Result<(), ParseError> {
        match tok {
            Token::Dot => self.output_stack.push(
                Ast::Subexpr(Box::new(lhs), Box::new(rhs))),
            Token::Or => self.output_stack.push(
                Ast::Or(Box::new(lhs), Box::new(rhs))),
            Token::Pipe => self.output_stack.push(
                Ast::Subexpr(Box::new(lhs), Box::new(rhs))),
            Token::Star => self.output_stack.push(
                Ast::Projection(Box::new(Ast::ObjectValues(Box::new(lhs))),
                                Box::new(rhs))),
            Token::Flatten => self.output_stack.push(
                Ast::Projection(Box::new(Ast::Flatten(Box::new(lhs))),
                                Box::new(rhs))),
            Token::Eq => self.output_stack.push(
                Ast::Comparison(Comparator::Eq, Box::new(lhs), Box::new(rhs))),
            Token::Ne => self.output_stack.push(
                Ast::Comparison(Comparator::Ne, Box::new(lhs), Box::new(rhs))),
            Token::Gt => self.output_stack.push(
                Ast::Comparison(Comparator::Gt, Box::new(lhs), Box::new(rhs))),
            Token::Gte => self.output_stack.push(
                Ast::Comparison(Comparator::Gte, Box::new(lhs), Box::new(rhs))),
            Token::Lt => self.output_stack.push(
                Ast::Comparison(Comparator::Lt, Box::new(lhs), Box::new(rhs))),
            Token::Lte => self.output_stack.push(
                Ast::Comparison(Comparator::Lte, Box::new(lhs), Box::new(rhs))),
            _ => return Err(self.err(&tok, &"Unexpected binary operator"))
        };
        Ok(())
    }

    /// Advances the cursor position
    #[inline]
    fn advance(&mut self) -> Token {
        match self.stream.next() {
            Some((pos, tok)) => { self.pos = pos; tok },
            None => Token::Eof
        }
    }

    #[inline]
    fn projection_rhs(&mut self, token: Token, parent_operator: Operator) -> ParseStep {
        match token {
            // Skip the dot token and parse with a dot precedence (e.g.., foo.*.bar)
            Token::Dot => self.parse_dot(parent_operator),
            // Multilist and filter are valid tokens that have a precedence >= 10
            Token::Lbracket | Token::Filter => self.operator(token, parent_operator),
            // Precedence < 10 are just parsed as. E.g., * | baz
            _ if token.lbp() < 10 => {
                self.output_stack.push(Ast::CurrentNode);
                self.operator(token, parent_operator)
            },
            _ => Err(self.token_err(&token))
        }
    }

    #[inline]
    fn parse_dot(&mut self, parent_operator: Operator) -> ParseStep {
        let token = self.advance();
        match token {
            Token::Lbracket => {
                // Parse a multi-list
                let next_token = self.advance();
                self.operator(next_token, Operator::MultiList(vec!()))
            },
            Token::Identifier(_)
                | Token::Star
                | Token::Lbrace
                | Token::Ampersand
                | Token::Filter => self.operator(token, parent_operator),
            _ => Err(self.err(&token, &format!("Expected identifier, '*', '{{', '[', '@', \
                                               or '[?', found {}", token.token_name())))
        }
    }

    /// Returns a formatted ParseError with the given message.
    fn err(&self, current_token: &Token, msg: &str) -> ParseError {
        let hint_msg = match current_token {
            &Token::Unknown { ref hint, .. } => hint.clone(),
            _ => "".to_string()
        };
        ParseError::new(&self.expr, self.pos, msg, &hint_msg)
    }

    /// Generates a formatted parse error for an out of place token.
    fn token_err(&self, current_token: &Token) -> ParseError {
        self.err(current_token,
                 &format!("Unexpected token: {}", current_token.token_name()))
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use ast::Ast;

    #[test] fn test_parse_nud() {
        let ast = parse("foo").unwrap();
        assert_eq!("Identifier(\"foo\")", format!("{:?}", ast));
    }

    #[test] fn test_parse_subexpr() {
        let ast = parse("foo.bar.baz").unwrap();
        assert_eq!("Subexpr(Subexpr(Identifier(\"foo\"), Identifier(\"bar\")), \
                            Identifier(\"baz\"))",
                   format!("{:?}", ast));
    }

    #[test] fn test_parse_or() {
        let ast = parse("foo || bar").unwrap();
        assert_eq!("Or(Identifier(\"foo\"), Identifier(\"bar\"))", format!("{:?}", ast));
    }

    #[test] fn test_parse_or_and_subexpr_with_precedence() {
        let ast = parse("foo.baz || bar.bam").unwrap();
        assert_eq!("Or(Subexpr(Identifier(\"foo\"), Identifier(\"baz\")), \
                       Subexpr(Identifier(\"bar\"), Identifier(\"bam\")))",
                   format!("{:?}", ast));
    }

    #[test] fn test_parse_or_and_pipe_with_precedence() {
        let ast = parse("foo || bar | baz").unwrap();
        assert_eq!("Subexpr(Or(Identifier(\"foo\"), Identifier(\"bar\")), \
                            Identifier(\"baz\"))", format!("{:?}", ast));
    }

    #[test] fn test_comparator() {
        let ast = parse("foo.bar == baz || bam").unwrap();
        assert_eq!(
            "Comparison(Eq, Subexpr(Identifier(\"foo\"), Identifier(\"bar\")), \
                                    Or(Identifier(\"baz\"), Identifier(\"bam\")))",
            format!("{:?}", ast));
    }

    #[test] fn test_parse_wildcard_values() {
        let ast = parse("foo.*.baz").unwrap();
        assert_eq!("Projection(ObjectValues(Identifier(\"foo\")), Identifier(\"baz\"))",
                   format!("{:?}", ast));
    }

    #[test] fn test_parse_nud_wildcard_values() {
        let ast = parse("*.baz").unwrap();
        assert_eq!("Projection(ObjectValues(CurrentNode), Identifier(\"baz\"))",
                   format!("{:?}", ast));
    }

    #[test] fn test_parse_nud_wildcard_values_with_no_rhs() {
        let ast = parse("* | baz").unwrap();
        assert_eq!("Subexpr(Projection(ObjectValues(CurrentNode), CurrentNode), \
                            Identifier(\"baz\"))",
                   format!("{:?}", ast));
    }

    #[test] fn test_parse_flatten() {
        let ast = parse("foo[].baz").unwrap();
        assert_eq!("Projection(Flatten(Identifier(\"foo\")), Identifier(\"baz\"))",
                   format!("{:?}", ast));
    }

    #[test] fn test_parse_nud_flatten() {
        let ast = parse("[].baz").unwrap();
        assert_eq!("Projection(Flatten(CurrentNode), Identifier(\"baz\"))",
                   format!("{:?}", ast));
    }

    #[test] fn test_parse_wildcard_index() {
        let ast = parse("foo[*].baz").unwrap();
        assert_eq!("Projection(Identifier(\"foo\"), Identifier(\"baz\"))",
                   format!("{:?}", ast));
    }

    #[test] fn test_parse_number() {
        let ast = parse("foo[0]").unwrap();
        assert_eq!("Subexpr(Identifier(\"foo\"), Index(0))", format!("{:?}", ast));
    }

    #[test] fn test_parse_number_with_subexpr() {
        let ast = parse("foo[0].bar").unwrap();
        assert_eq!("Subexpr(Subexpr(Identifier(\"foo\"), Index(0)), Identifier(\"bar\"))",
                   format!("{:?}", ast));
    }

    #[test] fn test_parse_number_in_projection() {
        let ast = parse("foo.*[0]").unwrap();
        assert_eq!("Projection(ObjectValues(Identifier(\"foo\")), Index(0))",
                   format!("{:?}", ast));
    }

    #[test] fn test_parse_complex_expression() {
        let ast = parse("foo.*.bar[*][0].baz || bam | boo").unwrap();
        assert_eq!("Subexpr(Or(Projection(ObjectValues(Identifier(\"foo\")), \
                                Projection(Identifier(\"bar\"), \
                                           Subexpr(Index(0), Identifier(\"baz\")))), \
                       Identifier(\"bam\")), Identifier(\"boo\"))",
                   format!("{:?}", ast));
    }

    #[test] fn test_parse_expression_reference() {
        let ast = parse("&foo.bar | [0]").unwrap();
        assert_eq!("Expref(Subexpr(Subexpr(Identifier(\"foo\"), Identifier(\"bar\")), Index(0)))",
                   format!("{:?}", ast));
    }

    #[test] fn test_parse_empty_functions() {
        let ast = parse("foo()").unwrap();
        assert_eq!("Function(\"foo\", [])", format!("{:?}", ast));
    }

    #[test] fn test_parse_functions_at_end() {
        let ast = parse("foo(bar)").unwrap();
        assert_eq!("Function(\"foo\", [Identifier(\"bar\")])", format!("{:?}", ast));
    }

    #[test] fn test_parse_functions_with_multiple_args() {
        let ast = parse("foo(bar, baz.boo, bam || qux)").unwrap();
        assert_eq!("Function(\"foo\", [Identifier(\"bar\"), \
                                       Subexpr(Identifier(\"baz\"), Identifier(\"boo\")), \
                                       Or(Identifier(\"bam\"), Identifier(\"qux\"))])",
                   format!("{:?}", ast));
    }

    #[test] fn test_parse_multi_list() {
        let ast = parse("foo.[bar, baz]").unwrap();
        assert_eq!("", format!("{:?}", ast));
    }
}
