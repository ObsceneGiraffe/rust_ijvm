use crate::{HaltReason, IJVMError, IJVMState, VMResult};
use crate::parse;

use std::{
    io::{self, SeekFrom},
};

/// Push a byte onto stack arguments(byte)
/// byte: A numeric literal, in octal (032 - leading zero), decimal (26 - no leading digits), or hexadecimal (0x1A - leading zero-x) format. Character literals ('M - leading single quote) are also allowed. Compiled to a 1-byte constant.
pub fn bipush(stack: &mut Vec<i32>, code_stream: &mut dyn io::Read) -> VMResult<()> {
    let value = parse::word_i32(code_stream, || IJVMError::ExpectedInstructionArgument)?;
    stack.push(value);
    Ok(())
}

/// Copy top word on stack and push onto stack arguments(N/A)
pub fn dup(stack: &mut Vec<i32>) -> VMResult<()> {
    let value = *stack.last()
        .ok_or_else(|| IJVMError::OperationAttemptedOnEmptyStack)?;
    stack.push(value);
    Ok(())
}

/// Print an error message and halt the simulator arguments(N/A)
pub fn err(_state: &mut IJVMState) -> VMResult<()> {
    println!("Error");
    // state = &mut IJVMState::Halted(HaltReason::ERRInstruction);
    Ok(())
}

/// Unconditional jump arguments(label name)
/// label name: The string name of a label. Compiled to a 2-byte offset.
pub fn goto<T>(code_stream: &mut T) -> VMResult<()> 
    where T: io::Read + io::Seek {
    let offset = parse::offset(code_stream, || IJVMError::MalformedOffset)?;
    code_stream.seek(SeekFrom::Start(offset as u64))?;
    Ok(())
}

/// Halt the simulator arguments(N/A)
pub fn halt(_state: &mut IJVMState) -> VMResult<()> {
    // state = IJVMState::Halted(HaltReason::HALTInstruction);
    Ok(())
}

/// Pop two words from stack; push their sum arguments(N/A)
pub fn iadd(stack: &mut Vec<i32>) -> VMResult<()> {
    let (val_a, val_b) = pop_two(stack)?;
    stack.push(val_a + val_b);
    Ok(())
}

/// Pop two words from stack; push Boolean AND arguments(N/A)
pub fn iand(stack: &mut Vec<i32>) -> VMResult<()> {
    let (val_a, val_b) = pop_two(stack)?;
    let bexp = i32_to_bool(val_a) && i32_to_bool(val_b);
    stack.push(bexp as i32);
    Ok(())
}

/// Pop word from stack and branch if it is zero arguments(label name)
/// label name: The string name of a label. Compiled to a 2-byte offset.
pub fn ifeq<T>(stack: &mut Vec<i32>, mut code_stream: &mut T) -> VMResult<()> 
    where T: io::Read + io::Seek {
    let value = pop_one(stack)?;

    if value == 0 {
        let offset = parse::offset(&mut code_stream, || IJVMError::MalformedOffset)?;
        code_stream.seek(SeekFrom::Start(offset as u64))?;
    }

    Ok(())
}

/// Pop word from stack and branch if it is less than zero arguments(label name)
/// label name: The string name of a label. Compiled to a 2-byte offset.
pub fn iflt<T>(stack: &mut Vec<i32>, mut code_stream: &mut T) -> VMResult<()> 
    where T: io::Read + io::Seek {
    let value = pop_one(stack)?;

    if value < 0 {
        let offset = parse::offset(&mut code_stream, || IJVMError::MalformedOffset)?;
        code_stream.seek(SeekFrom::Start(offset as u64))?;
    }

    Ok(())
}

/// Pop two words from stack and branch if they are equal arguments(label name)
/// label name: The string name of a label. Compiled to a 2-byte offset.
pub fn icmpeq<T>(stack: &mut Vec<i32>, mut code_stream: &mut T) -> VMResult<()> 
    where T: io::Read + io::Seek {
    let (val_a, val_b) = pop_two(stack)?;

    if val_a == val_b {
        let offset = parse::offset(&mut code_stream, || IJVMError::MalformedOffset)?;
        code_stream.seek(SeekFrom::Start(offset as u64))?;
    }

    Ok(())
}

/// Add a constant value to a local variable arguments(variable name, byte)
/// variable name: The string name of a local variable. Compiled to a 1-byte value, indicating an offset into the local variable frame.
/// byte: A numeric literal, in octal (032 - leading zero), decimal (26 - no leading digits), or hexadecimal (0x1A - leading zero-x) format. Character literals ('M - leading single quote) are also allowed. Compiled to a 1-byte constant.
pub fn iinc() -> VMResult<()> {
    unimplemented!();
}

/// Push local variable onto stack arguments(variable name)
/// variable name: The string name of a local variable. Compiled to a 1-byte value, indicating an offset into the local variable frame.
pub fn iload() -> VMResult<()> {
    unimplemented!();
}

/// Reads a character from the keyboard buffer and pushes it onto the stack. If no character is available, 0 is pushed arguments(N/A)
pub fn read_in() -> VMResult<()> {
    unimplemented!();
}

/// Invoke a method, pops object reference and optionally pops arguments from stack. arguments(method name)
/// method name: The string name of a method. When compiled, the address of the method is calculated and put into the constant pool. This operand is then replaced with the 2-byte index (in the constant pool) of the address.
pub fn invokevirtual() -> VMResult<()> {
    unimplemented!();
}

/// Pop two words from stack; push Boolean OR arguments(N/A)
pub fn ior(stack: &mut Vec<i32>) -> VMResult<()> {
    let (val_a, val_b) = pop_two(stack)?;
    let bexp = i32_to_bool(val_a) || i32_to_bool(val_b);
    stack.push(bexp as i32);
    Ok(())
}

/// Return from method with integer value arguments(N/A)
pub fn ireturn() -> VMResult<()> {
    unimplemented!();
}

/// Pop word from stack and store in local variable arguments(variable name)
/// variable name: The string name of a local variable. Compiled to a 1-byte value, indicating an offset into the local variable frame.
pub fn istore() -> VMResult<()> {
    unimplemented!();
}

/// Pop two words from stack; subtract the top word from the second to top word, push the answer; arguments(N/A)
pub fn isub(stack: &mut Vec<i32>) -> VMResult<()> {
    let (val_a, val_b) = pop_two(stack)?;
    stack.push(val_a - val_b);
    Ok(())
}

/// Push constant from constant pool onto stack arguments(constant name)
/// constant name: The string name of a constant. Compiled to a 2-byte index.
pub fn ldcw() -> VMResult<()> {
    unimplemented!();
}

/// Do nothing arguments(N/A)
pub fn nop() -> VMResult<()> {
    unimplemented!();
}

/// Pop word off stack and print it to standard out arguments(N/A)
pub fn write_out(stack: &mut Vec<i32>) -> VMResult<()> {
    let value = pop_one(stack)?;
    print!("{:?}", value);
    Ok(())
}

/// Delete word from top of stack arguments(N/A)
pub fn pop(stack: &mut Vec<i32>) -> VMResult<()> {
    pop_one(stack)?;
    Ok(())
}

/// Swap the two top words on the stack arguments(N/A)
pub fn swap(stack: &mut Vec<i32>) -> VMResult<()> {
    let (val_a, val_b) = pop_two(stack)?;
    stack.push(val_a);
    stack.push(val_b);
    Ok(())
}

/// Prefix instruction; next instruction has a 16-bit index  arguments(N/A)
pub fn wide() -> VMResult<()> {
    unimplemented!();
}

fn pop_one(stack: &mut Vec<i32>) -> VMResult<i32> {
    let val = stack.pop()
        .ok_or_else(|| IJVMError::OperationAttemptedOnEmptyStack)?;
    Ok(val)
}

fn pop_two(stack: &mut Vec<i32>) -> VMResult<(i32, i32)> {
    let val_a = pop_one(stack)?;
    let val_b = pop_one(stack)?;
    Ok((val_a, val_b))
}

fn i32_to_bool(i: i32) -> bool {
    i > 0
}