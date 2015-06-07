//! Executes compiled JMESPath bytecode instructions.

extern crate rustc_serialize;

use self::rustc_serialize::json::Json;

use ast::{Ast, Comparator, KeyValuePair};

#[derive(Clone, PartialEq, Debug)]
pub enum Opcode {
    // Pops N operands from stack and calls a built-in function by name.
    Call(u8, String),
    // Pops two elements from the stack and pushes true/false.
    Cmp(Comparator),
    // Duplicates the top of the stack
    Dup,
    // Pops TOS and iterates over each element if it is an array. If it
    // is not an array, then jumps to the given address.
    Each(usize),
    // Pops TOS and pushes the <operand> key value of TOS onto the stack.
    // If TOS is not an "object", null is pushed onto the stack.
    Field(String),
    // Pops TOS and pushes the <operand> index value of TOS onto the stack.
    // If TOS is not an "array", null is pushed onto the stack.
    Index(usize),
    // Pops TOS and pushes the <operand> index from the end of the length of
    // of TOS onto the stack. If TOS is not an "array", null is pushed onto
    /// the stack.
    NegativeIndex(usize),
    // Pops two elements, T1 and T2 where T1 is a value and T2 is an
    // "array". Pushes T1 onto T2 and pushes T2 back onto the stack.
    InjectIdx(usize),
    // Pops two elements, T1 and T2 where T1 is a value and T2 is an
    // "object". Adds T1 at the given operand key onto T2 and pushes T2
    // back onto the stack.
    InjectKey(String),
    // Unconditional jump to an address.
    Jump(usize),
    // Pops the TOS and jumps if 0 or false
    Jumpz(usize),
    // Pops the call stack
    Ret(usize),
    // Pops the TOS
    Pop,
    // Pushes a value onto the stack
    Push(Json),
    // Pops TOS and pushes true/false if the value is truthy.
    Truthy,
    // Pops TOS and pushes the type of the popped value.
    Type
}

pub type Program = Vec<Opcode>;

/// JMESPath VM
pub struct Vm<'a> {
    /// The compiled program.
    opcodes: &'a Program,
    /// The opcode index.
    index: usize,
    /// The VM stack consisting of JSON typed values.
    stack: Vec<Json>
}

impl<'a> Vm<'a> {
    /// Creates a new VM using the given program and data.
    pub fn new(opcodes: &'a Vec<Opcode>, data: Json) -> Vm<'a> {
        Vm {
            opcodes: opcodes,
            stack: vec![data],
            index: 0
        }
    }

    pub fn run(&mut self) -> Result<Json, String> {
        macro_rules! tos {
            () => {{
                self.stack.pop().unwrap_or(Json::Null)
            }};
        }
        while self.index < self.opcodes.len() {
            match &self.opcodes[self.index] {
                &Opcode::Push(ref j) => {
                    self.stack.push(j.clone());
                },
                &Opcode::Pop => {
                    self.stack.pop();
                },
                &Opcode::Dup => {
                    if self.stack.is_empty() {
                        self.stack.push(Json::Null);
                    } else {
                        let tos = self.stack.pop().unwrap();
                        self.stack.push(tos.clone());
                        self.stack.push(tos);
                    }
                },
                &Opcode::Field(ref f) => {
                    match tos!().find(f) {
                        Some(j) => self.stack.push(j.clone()),
                        _ => self.stack.push(Json::Null)
                    };
                },
                &Opcode::Index(i) => {
                    let tos = tos!();
                    self.stack.push(tos.as_array()
                        .and_then(|a| a.len().checked_sub(i + 1))
                        .and_then(|_| Some(tos[i].clone()))
                        .unwrap_or(Json::Null));
                },
                &Opcode::NegativeIndex(i) => {
                    let tos = tos!();
                    self.stack.push(tos.as_array()
                        .and_then(|a| a.len().checked_sub(i + 1))
                        .and_then(|i| Some(tos[i].clone()))
                        .unwrap_or(Json::Null));
                },
                &Opcode::Truthy => {
                    let tos = tos!();
                    self.stack.push(Json::Boolean(match tos {
                        Json::Boolean(b) if b == false => false,
                        Json::String(ref s) if s.len() == 0 => false,
                        Json::Array(ref a) if a.is_empty() => false,
                        Json::Object(ref o) if o.is_empty() => false,
                        Json::Null => false,
                        _ => true
                    }));
                },
                &Opcode::Type => {
                    let tos = tos!();
                    self.stack.push(match tos {
                        Json::Boolean(_) => Json::String("boolean".to_string()),
                        Json::String(_) => Json::String("string".to_string()),
                        Json::I64(_) | Json::U64(_) | Json::F64(_) => Json::String("number".to_string()),
                        Json::Array(_) => Json::String("array".to_string()),
                        Json::Object(_) => Json::String("object".to_string()),
                        Json::Null => Json::String("null".to_string()),
                    });
                }
                _ => panic!("Not implemented yet!")
            }
            self.index += 1;
        }

        Ok(self.stack.pop().unwrap_or(Json::Null))
    }
}

#[cfg(test)]
mod test {
    extern crate rustc_serialize;
    use super::{Opcode, Vm};
    use self::rustc_serialize::json::Json;

    #[test] fn truthy_test() {
        let opcodes = vec![Opcode::Truthy];
        let tests = vec![("\"foo\"", true), ("\"\"", false),
                         ("[1]", true), ("[]", false),
                         ("{\"foo\": 1}", true), ("{}", false),
                         ("true", true), ("false", false),
                         ("null", false), ("1", true)];
        for (js, result) in tests {
            let mut vm = Vm::new(&opcodes, Json::from_str(js).unwrap());
            assert_eq!(Json::Boolean(result), vm.run().unwrap());
        }
    }

    #[test] fn pushes_and_pops() {
        let opcodes = vec![Opcode::Pop, Opcode::Push(Json::String("foo".to_string()))];
        let mut vm = Vm::new(&opcodes, Json::Null);
        assert_eq!(Json::String("foo".to_string()), vm.run().unwrap());
    }

    #[test] fn dups_tos() {
        let opcodes = vec![Opcode::Dup, Opcode::Pop];
        let mut vm = Vm::new(&opcodes, Json::I64(1));
        assert_eq!(Json::I64(1), vm.run().unwrap());
    }

    #[test] fn dups_null() {
        let opcodes = vec![Opcode::Pop, Opcode::Dup];
        let mut vm = Vm::new(&opcodes, Json::I64(1));
        assert_eq!(Json::Null, vm.run().unwrap());
    }

    #[test] fn extracts_fields() {
        let opcodes = vec![Opcode::Field("a".to_string())];
        let mut vm = Vm::new(&opcodes, Json::from_str("{\"a\": 1}").unwrap());
        assert_eq!(Json::U64(1), vm.run().unwrap());
    }

    #[test] fn pushes_null_when_extracting_missing_field() {
        let opcodes = vec![Opcode::Field("a".to_string())];
        let mut vm = Vm::new(&opcodes, Json::from_str("{\"b\": 1}").unwrap());
        assert_eq!(Json::Null, vm.run().unwrap());
    }

    #[test] fn pushes_null_when_extracting_field_from_non_object() {
        let opcodes = vec![Opcode::Field("a".to_string())];
        let mut vm = Vm::new(&opcodes, Json::I64(1));
        assert_eq!(Json::Null, vm.run().unwrap());
    }

    #[test] fn extracts_indices() {
        let js = Json::from_str("[0, 1]").unwrap();
        let tests = vec![(Opcode::Index(0), Json::U64(0)),
                         (Opcode::Index(1), Json::U64(1)),
                         (Opcode::Index(2), Json::Null),
                         (Opcode::Index(3), Json::Null)];
        for (op, result) in tests {
            let opcodes = vec![op];
            let mut vm = Vm::new(&opcodes, js.clone());
            assert_eq!(result, vm.run().unwrap());
        }
    }

    #[test] fn extracts_negative_indices() {
        let js = Json::from_str("[0, 1]").unwrap();
        let tests = vec![(Opcode::NegativeIndex(0), Json::U64(1)),
                         (Opcode::NegativeIndex(1), Json::U64(0)),
                         (Opcode::NegativeIndex(2), Json::Null),
                         (Opcode::NegativeIndex(3), Json::Null)];
        for (op, result) in tests {
            let opcodes = vec![op];
            let mut vm = Vm::new(&opcodes, js.clone());
            assert_eq!(result, vm.run().unwrap());
        }
    }

    #[test] fn pushes_type_on_stack() {
        let js = Json::from_str("[0, 1]").unwrap();
        let opcodes = vec![Opcode::Type];
        let tests = vec![(Json::String("a".to_string()), Json::String("string".to_string())),
                         (Json::Array(vec![]), Json::String("array".to_string())),
                         (Json::from_str("{}").unwrap(), Json::String("object".to_string())),
                         (Json::I64(1), Json::String("number".to_string())),
                         (Json::Null, Json::String("null".to_string())),
                         (Json::Boolean(true), Json::String("boolean".to_string()))];
        for (js, result) in tests {
            let mut vm = Vm::new(&opcodes, js);
            assert_eq!(result, vm.run().unwrap());
        }
    }
}
