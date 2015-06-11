//! Compiles JMESPath expressions.

extern crate rustc_serialize;

use std::io::Cursor;
use std::collections::BTreeMap;
use self::rustc_serialize::json::Json;

use ast::{Ast, Comparator, KeyValuePair};
use vm::Opcode;

pub fn compile_opcodes(ast: &Ast) -> Vec<Opcode> {
    compile_opcodes_with_offset(&ast, 0)
}

fn compile_opcodes_with_offset(ast: &Ast, offset: usize) -> Vec<Opcode> {
    let mut opcodes = vec![];
    match *ast {
        Ast::Identifier(ref j) => {
            opcodes.push(Opcode::Field(j.clone()))
        }
        _ => panic!("not implemented yet!")
    };
    opcodes
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
        assert_eq!(vec![Opcode::Field("foo".to_owned())], opcodes);
    }
}
