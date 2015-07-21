//! Compiles JMESPath expressions.

extern crate rustc_serialize;

use self::rustc_serialize::json::Json;

use ast::{Ast, Comparator, KeyValuePair};
use vm::Opcode;

pub fn compile_opcodes(ast: &Ast) -> Vec<Opcode> {
    let mut opcodes = compile_with_offset(&ast, 0);
    opcodes.push(Opcode::Halt);
    opcodes
}

fn compile_with_offset(ast: &Ast, offset: usize) -> Vec<Opcode> {
    match *ast {
        Ast::CurrentNode => vec![Opcode::PushCurrent],
        Ast::Identifier(ref j) => vec![Opcode::Field(j.clone())],
        Ast::Index(i) => {
            if i < 0 {
                vec![Opcode::NegativeIndex((i.abs() - 1) as usize)]
            } else {
                vec![Opcode::Index(i as usize)]
            }
        },
        Ast::Or(ref lhs, ref rhs) => {
            let mut opcodes = compile_with_offset(&*lhs, offset);
            opcodes.push(Opcode::Truthy);
            let next_offset = opcodes.len() + 1;
            let right = compile_with_offset(&*rhs, next_offset);
            opcodes.push(Opcode::Brt(next_offset + right.len()));
            merge_opcodes(opcodes, right)
        },
        Ast::Subexpr(ref lhs, ref rhs) => {
            let mut opcodes = compile_with_offset(&*lhs, offset);
            merge_opcodes(opcodes, compile_with_offset(&*rhs, offset))
        },
        Ast::Comparison(ref cmp, ref lhs, ref rhs) => {
            let mut opcodes = compile_with_offset(&*lhs, offset);
            opcodes = merge_opcodes(opcodes, compile_with_offset(&*rhs, offset));
            opcodes.push(match cmp {
                &Comparator::Lt => Opcode::Lt,
                &Comparator::Lte => Opcode::Lte,
                &Comparator::Gt => Opcode::Gt,
                &Comparator::Gte => Opcode::Gte,
                &Comparator::Eq => Opcode::Eq,
                &Comparator::Ne => Opcode::Ne,
            });
            opcodes
        },
        Ast::Condition(ref lhs, ref rhs) => {
            let mut opcodes = compile_with_offset(&*lhs, offset);
            opcodes.push(Opcode::PushTrue);
            opcodes.push(Opcode::Eq);
            let next_offset = opcodes.len() + 1;
            let right = compile_with_offset(&*rhs, next_offset);
            opcodes.push(Opcode::Brf(next_offset + right.len() + 1));
            opcodes = merge_opcodes(opcodes, right);
            let next_offset = opcodes.len() + 2;
            opcodes.push(Opcode::Br(next_offset));
            opcodes.push(Opcode::PushNull);
            opcodes
        },
        Ast::Literal(ref json) => {
            // Perform optimizations for pushing true, false, and null
            match json {
                &Json::Boolean(true) => vec![Opcode::PushTrue],
                &Json::Boolean(false) => vec![Opcode::PushFalse],
                &Json::Null => vec![Opcode::PushNull],
                _ => vec![Opcode::Push(json.clone())]
            }
        },
        Ast::ObjectProjection(ref lhs, ref rhs) => {
            let mut opcodes = compile_with_offset(&*lhs, offset);
            opcodes.push(Opcode::ObjectValues);
            let relative_offset = offset + opcodes.len();
            create_projection(opcodes, relative_offset, rhs)
        },
        Ast::ArrayProjection(ref lhs, ref rhs) => {
            let mut opcodes = compile_with_offset(&*lhs, offset);
            let relative_offset = offset + opcodes.len();
            create_projection(opcodes, relative_offset, rhs)
        },
        ref a @ _ => panic!(format!("not implemented yet: {:?}", a))
    }
}

fn create_projection(mut opcodes: Vec<Opcode>, offset: usize, rhs: &Box<Ast>) -> Vec<Opcode> {
    let rhs = compile_with_offset(&*rhs, offset + 3);
    opcodes.push(Opcode::Projection(offset + rhs.len() + 3));
    opcodes.push(Opcode::Next);
    opcodes = merge_opcodes(opcodes, rhs);
    opcodes.push(Opcode::Br(offset + 1));
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
        assert_eq!(vec![Opcode::PushCurrent, Opcode::Halt], opcodes);
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

    #[test] fn assembles_array_projections() {
        let ast = Ast::ArrayProjection(
            Box::new(Ast::Identifier("foo".to_string())),
            Box::new(Ast::Identifier("bar".to_string())));
        let opcodes = compile_opcodes(&ast);
        assert_eq!(vec![Opcode::Field("foo".to_string()),
                        Opcode::Projection(5),
                        Opcode::Next,
                        Opcode::Field("bar".to_string()),
                        Opcode::Br(2),
                        Opcode::Halt],
                   opcodes);
    }

    #[test] fn assembles_object_projections() {
        let ast = Ast::ObjectProjection(
            Box::new(Ast::Identifier("foo".to_string())),
            Box::new(Ast::Identifier("bar".to_string())));
        let opcodes = compile_opcodes(&ast);
        assert_eq!(vec![Opcode::Field("foo".to_string()),
                        Opcode::ObjectValues,
                        Opcode::Projection(6),
                        Opcode::Next,
                        Opcode::Field("bar".to_string()),
                        Opcode::Br(3),
                        Opcode::Halt],
                   opcodes);
    }
}
