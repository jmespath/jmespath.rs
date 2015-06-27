//! Compiles JMESPath expressions.

extern crate rustc_serialize;

use std::ops::Index;
use std::io::Cursor;
use std::collections::BTreeMap;
use self::rustc_serialize::json::Json;

use ast::{Ast, Comparator, KeyValuePair};
use vm::Opcode;

#[derive(Clone, PartialEq, Debug)]
pub struct ConstantPool<'a> {
    constants: Vec<&'a Json>
}

impl<'a> ConstantPool<'a> {
    pub fn new() -> ConstantPool<'a> {
        ConstantPool {
            constants: vec!()
        }
    }

    /// Get a constant from the pool and return the index.
    ///
    /// This will insert a new constant if it is not in the pool.
    pub fn get(&mut self, json: &'a Json) -> usize {
        for (k, v) in self.constants.iter().enumerate() {
            if *v == json {
                return k;
            }
        }
        self.constants.push(json);
        self.constants.len() - 1
    }
}

/// Retrieve a constant from the pool by index
impl<'c> Index<usize> for ConstantPool<'c> {
    type Output = Json;

    fn index<'d>(&'d self, index: usize) -> &'d Json {
        self.constants[index]
    }
}

pub fn compile_opcodes(ast: &Ast) -> Vec<Opcode> {
    let mut opcodes = compile_with_offset(&ast, 0);
    opcodes.push(Opcode::Halt);
    opcodes
}

fn compile_with_offset(ast: &Ast, offset: usize) -> Vec<Opcode> {
    let mut opcodes: Vec<Opcode> = Vec::new();
    match *ast {
        Ast::CurrentNode => opcodes.push(Opcode::Load(0)),
        Ast::Identifier(ref j) => opcodes.push(Opcode::Field(j.clone())),
        Ast::Index(i) => {
            if i < 0 {
                opcodes.push(Opcode::NegativeIndex((i.abs() - 1) as usize));
            } else {
                opcodes.push(Opcode::Index(i as usize));
            }
        },
        Ast::Or(ref lhs, ref rhs) => {
            opcodes = merge_opcodes(opcodes, compile_with_offset(&*lhs, offset));
            opcodes.push(Opcode::Truthy);
            let next_offset = opcodes.len() + 1;
            let right = compile_with_offset(&*rhs, next_offset);
            opcodes.push(Opcode::Brt(next_offset + right.len()));
            opcodes = merge_opcodes(opcodes, right);
        },
        Ast::Subexpr(ref lhs, ref rhs) => {
            opcodes = merge_opcodes(opcodes, compile_with_offset(&*lhs, offset));
            opcodes = merge_opcodes(opcodes, compile_with_offset(&*rhs, offset));
        },
        Ast::Comparison(ref cmp, ref lhs, ref rhs) => {
            opcodes = merge_opcodes(opcodes, compile_with_offset(&*lhs, offset));
            opcodes = merge_opcodes(opcodes, compile_with_offset(&*rhs, offset));
            opcodes.push(match cmp {
                &Comparator::Lt => Opcode::Lt,
                &Comparator::Lte => Opcode::Lte,
                &Comparator::Gt => Opcode::Gt,
                &Comparator::Gte => Opcode::Gte,
                &Comparator::Eq => Opcode::Eq,
                &Comparator::Ne => Opcode::Ne,
            });
        },
        Ast::Condition(ref lhs, ref rhs) => {
            opcodes = merge_opcodes(opcodes, compile_with_offset(&*lhs, offset));
            opcodes.push(Opcode::PushTrue);
            opcodes.push(Opcode::Eq);
            let next_offset = opcodes.len() + 1;
            let right = compile_with_offset(&*rhs, next_offset);
            opcodes.push(Opcode::Brf(next_offset + right.len() + 1));
            opcodes = merge_opcodes(opcodes, right);
            let next_offset = opcodes.len() + 2;
            opcodes.push(Opcode::Br(next_offset));
            opcodes.push(Opcode::PushNull);
        },
        Ast::Literal(ref json) => {
            // Perform optimizations for pushing true, false, and null
            match json {
                &Json::Boolean(true) => opcodes.push(Opcode::PushTrue),
                &Json::Boolean(false) => opcodes.push(Opcode::PushFalse),
                &Json::Null => opcodes.push(Opcode::PushNull),
                _ => opcodes.push(Opcode::Push(json.clone()))
            }
        },
        _ => panic!("not implemented yet!")
    };
    opcodes
}

fn merge_opcodes(mut a: Vec<Opcode>, b: Vec<Opcode>) -> Vec<Opcode> {
    for opcode in b {
        a.push(opcode);
    }
    a
}

#[cfg(test)]
mod test {
    extern crate rustc_serialize;
    use self::rustc_serialize::json::Json;
    use super::*;
    use ast::{Ast, Comparator};
    use vm::Opcode;

    #[test] fn add_to_constant_pool() {
        let b1 = Json::Boolean(true);
        let b2 = Json::Boolean(false);
        let mut pool = ConstantPool::new();
        assert_eq!(0, pool.get(&b1));
        assert_eq!(0, pool.get(&b1));
        assert_eq!(1, pool.get(&b2));
        assert_eq!(1, pool.get(&b2));
        assert_eq!(b1, pool[0]);
    }

    #[test] fn assembles_identifiers() {
        let ast = Ast::Identifier("foo".to_owned());
        let opcodes = compile_opcodes(&ast);
        assert_eq!(vec![Opcode::Field("foo".to_owned()), Opcode::Halt], opcodes);
    }

    #[test] fn assembles_positive_index() {
        let ast = Ast::Index(1);
        let opcodes = compile_opcodes(&ast);
        assert_eq!(vec![Opcode::Index(1), Opcode::Halt], opcodes);
    }

    #[test] fn assembles_negative_index() {
        let ast = Ast::Index(-2);
        let opcodes = compile_opcodes(&ast);
        assert_eq!(vec![Opcode::NegativeIndex(1), Opcode::Halt], opcodes);
    }

    #[test] fn assembles_or_expression() {
        let ast = Ast::Or(
            Box::new(Ast::Identifier("foo".to_owned())),
            Box::new(Ast::Identifier("bar".to_owned())));
        let opcodes = compile_opcodes(&ast);
        assert_eq!(vec![Opcode::Field("foo".to_owned()),
                        Opcode::Truthy,
                        Opcode::Brt(4),
                        Opcode::Field("bar".to_owned()),
                        Opcode::Halt],
                   opcodes);
    }

    #[test] fn assembles_current_node() {
        let ast = Ast::CurrentNode;
        let opcodes = compile_opcodes(&ast);
        assert_eq!(vec![Opcode::Load(0), Opcode::Halt], opcodes);
    }

    #[test] fn assembles_eq_comparison() {
        let tests = vec![(Comparator::Lt, Opcode::Lt),
                         (Comparator::Lte, Opcode::Lte),
                         (Comparator::Gt, Opcode::Gt),
                         (Comparator::Gte, Opcode::Gte),
                         (Comparator::Eq, Opcode::Eq),
                         (Comparator::Ne, Opcode::Ne)];
        for (cmp, op) in tests {
            let ast = Ast::Comparison(
                cmp,
                Box::new(Ast::Identifier("foo".to_string())),
                Box::new(Ast::Identifier("bar".to_string())));
            let opcodes = compile_opcodes(&ast);
            assert_eq!(vec![Opcode::Field("foo".to_string()),
                            Opcode::Field("bar".to_string()),
                            op,
                            Opcode::Halt], opcodes);
        }
    }

    #[test] fn assembles_conditions() {
        let ast = Ast::Condition(
            Box::new(Ast::Literal(Json::Boolean(true))),
            Box::new(Ast::Identifier("bar".to_owned())));
        let opcodes = compile_opcodes(&ast);
        assert_eq!(vec![Opcode::PushTrue,
                        Opcode::PushTrue,
                        Opcode::Eq,
                        Opcode::Brf(6),
                        Opcode::Field("bar".to_owned()),
                        Opcode::Br(7),
                        Opcode::PushNull,
                        Opcode::Halt],
                   opcodes);
    }
}
