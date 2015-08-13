//! Module for parsing JMESPath expressions into an AST.

extern crate rustc_serialize;

use std::iter::Peekable;

use ast::{Ast, Comparator};
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

/// Operators are pushed onto the operator stack.
#[derive(Debug, PartialEq)]
enum Operator {
    Basic(Token),
    Function(String),
    ArrayProjection,
    SliceProjection(Option<i32>, Option<i32>, Option<i32>),
    OpenParen,
    OpenBracket,
    OpenBrace,
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
            &Operator::Function(_) => Token::Lparen.lbp(),
            &Operator::ArrayProjection => Token::Star.lbp(),
            &Operator::SliceProjection(_, _, _) => Token::Star.lbp(),
            &Operator::OpenParen => Token::Lparen.lbp(),
            &Operator::OpenBracket => Token::Lbracket.lbp(),
            &Operator::OpenBrace => Token::Lbracket.lbp(),
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

    pub fn terminates(&self, token: &Token) -> bool {
        match self {
            &Operator::OpenParen if token == &Token::Rparen => true,
            &Operator::OpenBracket if token == &Token::Rbracket => true,
            &Operator::OpenBrace if token == &Token::Rbrace => true,
            &Operator::Function(_) if token == &Token::Rparen => true,
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
    /// The current token
    token: Token,
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
        let mut lexer = Lexer::new(expr);
        let tok0 = lexer.next().unwrap_or((0, Token::Eof));
        Parser {
            stream: lexer.peekable(),
            expr: expr.to_string(),
            pos: tok0.0,
            token: tok0.1,
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
            _ => Err(self.err(&"Did not reach token stream EOF"))
        }
    }

    #[inline]
    fn expr(&mut self) -> ParseResult {
        self.state_stack.push(State::Nud(0));
        while self.token != Token::Eof {
            match self.state_stack.last() {
                Some(&State::Nud(rbp)) => {
                    self.state_stack.pop();
                    try!(self.nud());
                    self.state_stack.push(State::Led(rbp));
                },
                Some(&State::Led(rbp)) => {
                    if rbp < self.token.lbp() {
                        try!(self.led());
                    } else {
                        self.state_stack.pop();
                    }
                },
                None => break
            }
        }
        // Pop and process any remaining operators on the stack.
        while !self.operator_stack.is_empty() {
            try!(self.pop_token());
        }
        if self.output_stack.len() != 1 {
            Err(self.err(&"Unexpected end of token stream"))
        } else {
            Ok(self.output_stack.pop().unwrap())
        }
    }

    #[inline]
    fn nud(&mut self) -> ParseStep {
        // First match tokens that do not need to be copied.
        match self.token {
            Token::At => {
                self.advance();
                self.output_stack.push(Ast::CurrentNode);
                Ok(())
            },
            Token::Star => {
                self.advance();
                self.output_stack.push(Ast::CurrentNode);
                self.projection_rhs(Operator::Basic(Token::Star))
            },
            Token::Flatten => {
                self.advance();
                self.output_stack.push(Ast::CurrentNode);
                self.projection_rhs(Operator::Basic(Token::Flatten))
            },
            Token::Filter => {
                self.advance();
                self.output_stack.push(Ast::CurrentNode);
                self.projection_rhs(Operator::Basic(Token::Filter))
            },
            Token::Lbracket => self.parse_lbracket(true),
            Token::Lbrace => {
                self.advance();
                self.output_stack.push(Ast::CurrentNode);
                panic!();
            },
            Token::Ampersand => {
                self.advance();
                self.operator(Operator::Basic(Token::Ampersand))
            },
            _ => {
                // Now match tokens that must be copied.
                let token = self.token.clone();
                self.advance();
                match token {
                    Token::Identifier(value) => {
                        self.output_stack.push(Ast::Identifier(value));
                        Ok(())
                    },
                    Token::QuotedIdentifier(value) => {
                        match self.token {
                            Token::Lparen => Err(self.err(&"Quoted strings can't be function names")),
                            _ => {
                                self.output_stack.push(Ast::Identifier(value));
                                Ok(())
                            }
                        }
                    },
                    Token::Literal(value) => {
                        self.output_stack.push(Ast::Literal(value));
                        Ok(())
                    },
                    ref tok @ _ => Err(self.err(&format!("Unexpected nud token: {}",
                                                         tok.token_name()))),
                }
            }
        }
    }

    #[inline]
    fn led(&mut self) -> ParseStep {
        match self.token {
            Token::Dot => {
                match self.stream.peek() {
                    Some(&(_, Token::Star)) => {
                        self.advance();
                        self.advance();
                        self.projection_rhs(Operator::Basic(Token::Star))
                    },
                    _ => self.parse_dot(Operator::Basic(Token::Dot))
                }
            },
            Token::Flatten => {
                self.advance();
                self.projection_rhs(Operator::Basic(Token::Flatten))
            },
            Token::Lbracket => self.parse_lbracket(false),
            Token::Or => { self.advance(); self.operator(Operator::Basic(Token::Or)) },
            Token::Pipe => { self.advance(); self.operator(Operator::Basic(Token::Pipe)) },
            Token::Lt => { self.advance(); self.operator(Operator::Basic(Token::Lt)) },
            Token::Lte => { self.advance(); self.operator(Operator::Basic(Token::Lte)) },
            Token::Gt => { self.advance(); self.operator(Operator::Basic(Token::Gt)) },
            Token::Gte => { self.advance(); self.operator(Operator::Basic(Token::Gte)) },
            Token::Eq => { self.advance(); self.operator(Operator::Basic(Token::Eq)) },
            Token::Ne => { self.advance(); self.operator(Operator::Basic(Token::Ne)) },
            _ => Err(self.err(&format!("Unexpected led token: {}",
                              self.token.token_name()))),
        }
    }

    #[inline]
    fn parse_lbracket(&mut self, is_nud: bool) -> ParseStep {
        self.advance();
        match self.stream.peek() {
            Some(&(_, Token::Rbracket)) => {
                match self.token {
                    Token::Number(value) => {
                        self.advance();
                        self.advance();
                        if is_nud {
                            self.output_stack.push(Ast::Index(value));
                        } else {
                            let lhs = self.output_stack.pop().unwrap();
                            self.output_stack.push(
                                Ast::Subexpr(Box::new(lhs), Box::new(Ast::Index(value))));
                        }
                        Ok(())
                    },
                    Token::Star => {
                        self.advance();
                        self.advance();
                        if is_nud {
                            self.output_stack.push(Ast::CurrentNode);
                        }
                        self.projection_rhs(Operator::ArrayProjection)
                    },
                    Token::Colon => {
                        self.advance();
                        self.advance();
                        if is_nud {
                            self.output_stack.push(Ast::CurrentNode);
                        }
                        self.projection_rhs(Operator::SliceProjection(None, None, None))
                    },
                    _ => Err(self.err("Expected number, ':', or '*'")),
                }
            },
            _ => panic!()
        }
    }

    #[inline]
    fn operator(&mut self, operator: Operator) -> ParseStep {
        self.state_stack.push(State::Nud(operator.precedence()));
        // Pop things from the top of the operator stack that have a higher precedence.
        while self.is_last_gt(&operator) {
            try!(self.pop_token())
        }
        self.operator_stack.push(operator);
        Ok(())
    }

    #[inline]
    fn is_last_gt(&self, op: &Operator) -> bool {
        match self.operator_stack.last() {
            Some(operator) if op.has_lower_precedence(operator) => true,
            _ => false
        }
    }

    #[inline]
    fn pop_token(&mut self) -> ParseStep {
        let operator = self.operator_stack.pop().unwrap();
        if operator.is_binary() {
            let rhs = self.output_stack.pop().unwrap();
            let lhs = self.output_stack.pop().unwrap();
            self.popped_binary(operator, lhs, rhs)
        } else {
            let output = self.output_stack.pop().unwrap();
            self.popped_unary(operator, output)
        }
    }

    #[inline]
    fn popped_binary(&mut self, operator: Operator, lhs: Ast, rhs: Ast) -> ParseStep {
        match operator {
            Operator::Basic(token) => {
                match token {
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
                    _ => return Err(self.err(&"Unexpected binary operator"))
                }
            },
            Operator::ArrayProjection => self.output_stack.push(
                Ast::Projection(Box::new(lhs), Box::new(rhs))),
            Operator::Function(fn_name) => panic!(),
            Operator::SliceProjection(start, step, stop) => panic!(),
            Operator::OpenParen => panic!(),
            Operator::OpenBrace => panic!(),
            Operator::OpenBracket => panic!(),
        };
        Ok(())
    }

    #[inline]
    fn popped_unary(&mut self, operator: Operator, output: Ast) -> ParseStep {
        match operator {
            Operator::Basic(ref token) if token == &Token::Ampersand =>
                self.output_stack.push(Ast::Expref(Box::new(output))),
            _ => return Err(self.err(&"Unexpected unary operator"))
        };
        Ok(())
    }

    /// Advances the cursor position
    #[inline]
    fn advance(&mut self) {
        self.stream.next().map(|(pos, tok)| {
            self.pos = pos;
            self.token = tok;
        });
    }

    #[inline]
    fn projection_rhs(&mut self, parent_operator: Operator) -> ParseStep {
        match self.token {
            // Skip the dot token and parse with a dot precedence (e.g.., foo.*.bar)
            Token::Dot => self.parse_dot(parent_operator),
            // Multilist and filter are valid tokens that have a precedence >= 10
            Token::Lbracket | Token::Filter => self.operator(parent_operator),
            // Precedence < 10 are just parsed as. E.g., * | baz
            _ if self.token.lbp() < 10 => {
                self.output_stack.push(Ast::CurrentNode);
                self.operator(parent_operator)
            },
            _ => Err(self.token_err())
        }
    }

    #[inline]
    fn parse_dot(&mut self, parent_operator: Operator) -> ParseStep {
        self.advance();
        match self.token {
            Token::Lbracket => {
                self.advance();
                panic!(); // self.parse_multi_list()
            },
            Token::Identifier(_)
            | Token::Star
            | Token::Lbrace
            | Token::Ampersand
            | Token::Filter => self.operator(parent_operator),
            _ => Err(self.err(&format!("Expected Identifier, '*', '{{', '[', '@', or '[?',\
                                       found {}", self.token.token_name())))
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
}
