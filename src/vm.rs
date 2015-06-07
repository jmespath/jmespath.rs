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
    // Pops two elements, T1 and T2 where T1 is a value and T2 is an
    // "array". Pushes T1 onto T2 and pushes T2 back onto the stack.
    Insert(usize),
    // Unconditional jump to an address.
    Jump(usize),
    // Pops the TOS and jumps if 0 or false
    Jumpz(usize),
    // Pops two elements, T1 and T2 where T1 is a value and T2 is an
    // "object". Adds T1 at the given operand key onto T2 and pushes T2
    // back onto the stack.
    Key(String),
    // Pops the call stack
    Ret(usize),
    // Pops the TOS
    Pop,
    // Pushes a value onto the stack
    Push,
    // Pops TOS and pushes true/false if the value is truthy.
    Truthy,
    // Pops TOS and pushes the type of the popped value.
    Type
}

/// JMESPath VM
pub struct Vm<'a, 'b> {
    /// The compiled program.
    opcodes: &'a Vec<Opcode>,
    /// The opcode index.
    index: usize,
    /// The VM stack consisting of JSON typed values.
    stack: Vec<&'b Json>
}

impl<'a, 'b> Vm<'a, 'b> {
    /// Creates a new VM using the given program and data.
    pub fn new(opcodes: &'a Vec<Opcode>, data: &'b Json) -> Vm<'a, 'b> {
        Vm {
            opcodes: opcodes,
            stack: vec![data],
            index: 0
        }
    }

    pub fn run(&mut self) {

    }
}
