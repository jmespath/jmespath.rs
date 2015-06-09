//! Executes compiled JMESPath bytecode instructions.

extern crate rustc_serialize;

use self::rustc_serialize::json::Json;

use ast::{Ast, Comparator, KeyValuePair};

pub type Program = Vec<Opcode>;

#[derive(Clone, PartialEq, Debug)]
pub enum Opcode {
    // Unconditional branch to an address.
    Br(usize),
    // Pops the TOS and branches is false
    Brf(usize),
    // Pops the TOS and branches if true
    Brt(usize),
    // Pops the call stack and jumps to the return position.
    Ret,
    // Pushes a value onto the stack
    Push(Json),
    // Loads a value from the call stack by index.
    Load(usize),
    // Pops TOS and stores it in a call stack index.
    Store(usize),
    // Pops the TOS
    Pop,
    // Halts execution
    Halt,
    // Pops two elements from the stack and pushes true/false if a == b
    Eq,
    // Pops two elements from the stack and pushes true/false if a != b
    Ne,
    // Pops two elements from the stack and pushes true/false if a < b
    Lt,
    // Pops two elements from the stack and pushes true/false if a <= b
    Lte,
    // Pops two elements from the stack and pushes true/false if a > b
    Gt,
    // Pops two elements from the stack and pushes true/false if a >= b
    Gte,
    // Pops N operands from stack and calls a built-in function by name.
    Builtin(u8, String),
    // Pushes a stack frame and branches to the given address.
    Call(u8),
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
    Insert,
    // Pops two elements, T1 and T2 where T1 is a value and T2 is an
    // "object". Adds T1 at the given operand key onto T2 and pushes T2
    // back onto the stack.
    InjectKey(String),
    // Pops TOS and pushes true/false if the value is truthy.
    Truthy,
    // Pops TOS and pushes the type of the popped value.
    Type
}

/// Represents a stack frame consisting of a return address and locals.
struct StackFrame {
    /// The operand position to jump to when Ret is encountered.
    return_address: usize,
    /// A vector of local frame variables.
    locals: Vec<Json>
}

impl StackFrame {
    /// Creates a new empty stack frame with a return address.
    pub fn new(return_address: usize) -> StackFrame {
        StackFrame {
            return_address: return_address,
            locals: vec![]
        }
    }
}

/// JMESPath VM
pub struct Vm<'a> {
    /// The compiled program.
    opcodes: &'a Program,
    /// The opcode index.
    index: usize,
    /// The VM stack consisting of JSON typed values.
    stack: Vec<Json>,
    /// Vector of stack frames.
    frames: Vec<StackFrame>
}

impl<'a> Vm<'a> {
    /// Creates a new VM using the given program and data.
    pub fn new(opcodes: &'a Vec<Opcode>, data: Json) -> Vm<'a> {
        Vm {
            opcodes: opcodes,
            stack: vec![data],
            index: 0,
            frames: vec![StackFrame::new(0)]
        }
    }

    pub fn run(&mut self) -> Result<Json, String> {
        macro_rules! tos {
            () => {{
                self.stack.pop().unwrap_or(Json::Null)
            }};
        }
        macro_rules! stack_cmp {
            ($cmp:ident) => {{
                let (a, b) = (tos!(), tos!());
                self.stack.push(Vm::ensure_both_numbers(a, b)
                    .map(|(a, b)| Json::Boolean(a.$cmp(&b)))
                    .unwrap_or(Json::Boolean(false)));
            }};
        }
        while self.index < self.opcodes.len() {
            match &self.opcodes[self.index] {
                &Opcode::Lt => { stack_cmp!(lt); },
                &Opcode::Lte => { stack_cmp!(le); },
                &Opcode::Gt => { stack_cmp!(gt); },
                &Opcode::Gte => { stack_cmp!(ge); },
                &Opcode::Eq => {
                    let (a, b) = (tos!(), tos!());
                    self.stack.push(Json::Boolean(a == b));
                },
                &Opcode::Ne => {
                    let (a, b) = (tos!(), tos!());
                    self.stack.push(Json::Boolean(a != b));
                },
                &Opcode::Push(ref j) => {
                    self.stack.push(j.clone());
                },
                &Opcode::Pop => {
                    self.stack.pop();
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
                        Json::I64(_) | Json::U64(_) | Json::F64(_) => {
                            Json::String("number".to_string())
                        },
                        Json::Array(_) => Json::String("array".to_string()),
                        Json::Object(_) => Json::String("object".to_string()),
                        Json::Null => Json::String("null".to_string()),
                    });
                },
                &Opcode::Br(address) => {
                    self.index = address;
                    continue;
                },
                &Opcode::Brt(address) => {
                    self.index = try!(self.cond_branch(true, address));
                    continue;
                },
                &Opcode::Brf(address) => {
                    self.index = try!(self.cond_branch(false, address));
                    continue;
                },
                &Opcode::InjectKey(ref k) => {
                    let (new_val, mut coll) = (tos!(), tos!());
                    self.stack.push(coll.as_object_mut()
                        .map(|obj| obj.insert(k.clone(), new_val))
                        .map(|_| coll)
                        .unwrap_or(Json::Null));
                },
                &Opcode::Insert => {
                    let (new_val, mut coll) = (tos!(), tos!());
                    self.stack.push(coll.as_array_mut()
                        .map(|arr| arr.push(new_val))
                        .map(|_| coll)
                        .unwrap_or(Json::Null));
                },
                &Opcode::Halt => break,
                _ => panic!("Not implemented yet!")
            }
            self.index += 1;
        }

        Ok(self.stack.pop().unwrap_or(Json::Null))
    }

    /// Conditionally branch to the given address if TOS == check.
    fn cond_branch(&mut self, check: bool, address: usize) -> Result<usize, String> {
        let tos = self.stack.pop().unwrap_or(Json::Null);
        match tos {
            Json::Boolean(b) if b == check => Ok(address),
            _ => Ok(self.index + 1)
        }
    }

    /// Ensures that both values are numbers and returns their values.
    fn ensure_both_numbers(a: Json, b: Json) -> Option<(f64, f64)> {
        if !a.is_number() || !b.is_number() {
            None
        } else {
            Some((a.as_f64().unwrap(), b.as_f64().unwrap()))
        }
    }
}

#[cfg(test)]
mod test {
    extern crate rustc_serialize;
    use super::{Opcode, Vm};
    use ast::{Comparator};
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

    #[test] fn can_branch() {
        let opcodes = vec![Opcode::Br(2),
                           Opcode::Br(3),
                           Opcode::Br(1),
                           Opcode::Push(Json::Boolean(true))];
        let mut vm = Vm::new(&opcodes, Json::Null);
        assert_eq!(Json::Boolean(true), vm.run().unwrap());
    }

    #[test] fn can_branch_on_false() {
        let opcodes = vec![Opcode::Brf(2),
                           Opcode::Index(0),
                           Opcode::Push(Json::Boolean(true))];
        let mut vm = Vm::new(&opcodes, Json::Boolean(false));
        assert_eq!(Json::Boolean(true), vm.run().unwrap());
    }

    #[test] fn can_branch_on_true() {
        let opcodes = vec![Opcode::Brt(2),
                           Opcode::Index(0),
                           Opcode::Push(Json::Boolean(true))];
        let mut vm = Vm::new(&opcodes, Json::Boolean(true));
        assert_eq!(Json::Boolean(true), vm.run().unwrap());
    }

    #[test] fn can_not_branch_on_false_conditionally() {
        let opcodes = vec![Opcode::Brf(2),
                           Opcode::Halt,
                           Opcode::Push(Json::Boolean(true))];
        let mut vm = Vm::new(&opcodes, Json::Boolean(true));
        assert_eq!(Json::Null, vm.run().unwrap());
    }

    #[test] fn can_not_branch_on_true_conditionally() {
        let opcodes = vec![Opcode::Brt(2),
                           Opcode::Halt,
                           Opcode::Push(Json::Boolean(false))];
        let mut vm = Vm::new(&opcodes, Json::Boolean(false));
        assert_eq!(Json::Null, vm.run().unwrap());
    }

    #[test] fn injects_key_into_valid_object() {
        let opcodes = vec![Opcode::Push(Json::String("bar".to_string())),
                           Opcode::InjectKey("foo".to_string())];
        let mut vm = Vm::new(&opcodes, Json::from_str("{}").unwrap());
        let result = vm.run().unwrap();
        assert_eq!("{\"foo\":\"bar\"}", format!("{}", result));
    }

    #[test] fn pushes_false_when_injecting_key_onto_non_object() {
        let opcodes = vec![Opcode::Push(Json::String("bar".to_string())),
                           Opcode::InjectKey("foo".to_string())];
        let mut vm = Vm::new(&opcodes, Json::from_str("[]").unwrap());
        assert_eq!(Json::Null, vm.run().unwrap());
    }

    #[test] fn inserts_into_valid_array() {
        let opcodes = vec![Opcode::Push(Json::String("bar".to_string())),
                           Opcode::Insert,
                           Opcode::Push(Json::String("baz".to_string())),
                           Opcode::Insert];
        let mut vm = Vm::new(&opcodes, Json::from_str("[]").unwrap());
        let result = vm.run().unwrap();
        assert_eq!("[\"bar\",\"baz\"]", format!("{}", result));
    }

    #[test] fn pushes_false_when_inserting_onto_non_array() {
        let opcodes = vec![Opcode::Push(Json::String("bar".to_string())),
                           Opcode::Insert];
        let mut vm = Vm::new(&opcodes, Json::from_str("{}").unwrap());
        assert_eq!(Json::Null, vm.run().unwrap());
    }

    #[test] fn compares_conditionally() {
        let tests = vec![("[0, 1]", Opcode::Lt, false),
                         ("[0, 1]", Opcode::Lt, false),
                         ("[0, 1]", Opcode::Gt, true),
                         ("[0, 1]", Opcode::Gte, true),
                         ("[0, 1]", Opcode::Eq, false),
                         ("[0, \"a\"]", Opcode::Ne, true),
                         ("[0, \"a\"]", Opcode::Eq, false),
                         ("[\"a\", \"a\"]", Opcode::Eq, true),
                         ("[\"a\", \"b\"]", Opcode::Eq, false),
                         ("[\"a\", \"b\"]", Opcode::Ne, true)];
        for (js, cmp, result) in tests {
            let parsed = Json::from_str(js).unwrap();
            let opcodes = vec![Opcode::Push(parsed[0].clone()),
                               Opcode::Push(parsed[1].clone()),
                               cmp];
            let mut vm = Vm::new(&opcodes, Json::Null);
            assert_eq!(Json::Boolean(result), vm.run().unwrap());
        }
    }
}
