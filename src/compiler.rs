//! Compiles JMESPath expressions.

extern crate rustc_serialize;

use std::io::Cursor;
use std::collections::BTreeMap;
use self::rustc_serialize::json::Json;

use ast::{Ast, Comparator, KeyValuePair};
use vm::Opcode;

pub fn compile_opcodes(ast: &Ast) -> Vec<Opcode> {
    let mut opcodes = compile_opcodes_with_offset(&ast, 0);
    opcodes.push(Opcode::Halt);
    opcodes
}

fn compile_opcodes_with_offset(ast: &Ast, offset: usize) -> Vec<Opcode> {
    let mut opcodes: Vec<Opcode> = Vec::new();
    match *ast {
        Ast::Identifier(ref j) => {
            opcodes.push(Opcode::Field(j.clone()))
        },
        Ast::Index(i) => {
            if i < 0 {
                opcodes.push(Opcode::NegativeIndex((i.abs() - 1) as usize))
            } else {
                opcodes.push(Opcode::Index(i as usize))
            }
        },
        Ast::Or(ref lhs, ref rhs) => {
            opcodes = merge_opcodes(opcodes, compile_opcodes_with_offset(&*lhs, offset));
            opcodes.push(Opcode::Truthy);
            let next_offset = opcodes.len() + 1;
            let right = compile_opcodes_with_offset(&*rhs, next_offset);
            opcodes.push(Opcode::Brt(next_offset + right.len()));
            opcodes = merge_opcodes(opcodes, right)
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
    use ast::Ast;
    use vm::Opcode;

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
}
