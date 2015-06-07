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
    Index(i64),
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

    pub fn run(&mut self) -> Json {
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
                    let idx = if i < 0 { 0 } else { i as usize };
                    match tos!() {
                        a @ Json::Array(_) => self.stack.push(a[idx].clone()),
                        _ => self.stack.push(Json::Null)
                    };
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
                }
                _ => panic!("Not implemented yet!")
            }
            self.index += 1;
        }

        self.stack.pop().unwrap_or(Json::Null)
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
            assert_eq!(Json::Boolean(result), vm.run());
        }
    }
}
