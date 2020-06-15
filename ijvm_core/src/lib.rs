mod instructions;
mod parse;

#[macro_use] extern crate enum_primitive;
extern crate num;
use num::FromPrimitive;

use std::{
    cmp,
    fmt::{self, Debug, Display},
    fs::File,
    io::{self, Read, Seek, SeekFrom},
    mem::size_of,
    path::Path
};


#[cfg(test)]
mod tests {
    use super::*;
}

type VMResult<T> = Result<T, IJVMError>;

pub type Word = u32; // the basic unit of the ijvm will be an int32
pub const WORD_BYTE_LEN: usize = size_of::<u32>();
pub const OFFSET_BYTE_LEN: usize = size_of::<u16>();
pub const HEADER_BYTE_LEN: usize = WORD_BYTE_LEN;
pub const MAGIC_NUMBER: i32 = 0x1DEADFAD;
const DEFAULT_READ_BUFFER_SIZE: usize = 1000;
const DEFAULT_STACK_SIZE: usize = 100;

// byte: A numeric literal, in octal (032 - leading zero), decimal (26 - no leading digits), or hexadecimal (0x1A - leading zero-x) format. Character literals ('M - leading single quote) are also allowed. Compiled to a 1-byte constant.
// label name: The string name of a label. Compiled to a 2-byte offset.
// variable name: The string name of a local variable. Compiled to a 1-byte value, indicating an offset into the local variable frame.
// method name: The string name of a method. When compiled, the address of the method is calculated and put into the constant pool. This operand is then replaced with the 2-byte index (in the constant pool) of the address.
// constant name: The string name of a constant. Compiled to a 2-byte index.
// N/A: This instruction takes no operands.
enum_from_primitive! {
#[derive(Copy, Clone, Debug, PartialEq)]
pub enum Instruction {
    BIPUSH = 0x10,          // Push a byte onto stack arguments(byte)
    DUP = 0x59,             // Copy top word on stack and push onto stack arguments(N/A)
    ERR = 0xFE,             // Print an error message and halt the simulator arguments(N/A)
    GOTO = 0xA7,            // Unconditional jump arguments(label name)
    HALT = 0xFF,            // Halt the simulator arguments(N/A)
    IADD = 0x60,            // Pop two words from stack; push their sum arguments(N/A)
    IAND = 0x7E,            // Pop two words from stack; push Boolean AND arguments(N/A)
    IFEQ = 0x99,            // Pop word from stack and branch if it is zero arguments(label name)
    IFLT = 0x9B,            // Pop word from stack and branch if it is less than zero arguments(label name)
    ICMPEQ = 0x9F,          // Pop two words from stack and branch if they are equal arguments(label name)
    IINC = 0x84,            // Add a constant value to a local variable arguments(variable name, byte)
    ILOAD = 0x15,           // Push local variable onto stack arguments(variable name)
    IN = 0xFC,              // Reads a character from the keyboard buffer and pushes it onto the stack. If no character is available, 0 is pushed arguments(N/A)
    INVOKEVIRTUAL = 0xB6,   // Invoke a method, pops object reference and optionally pops arguments from stack. arguments(method name)
    IOR = 0xB0,             // Pop two words from stack; push Boolean OR arguments(N/A)
    IRETURN = 0xAC,         // Return from method with integer value arguments(N/A)
    ISTORE = 0x36,          // Pop word from stack and store in local variable arguments(variable name)
    ISUB = 0x64,            // Pop two words from stack; subtract the top word from the second to top word, push the answer; arguments(N/A)
    LDCW = 0x13,            // Push constant from constant pool onto stack arguments(constant name)
    NOP = 0x00,             // Do nothing arguments(N/A)
    OUT = 0xFD,             // Pop word off stack and print it to standard out arguments(N/A)
    POP = 0x57,             // Delete word from top of stack arguments(N/A)
    SWAP = 0x5F,            // Swap the two top words on the stack arguments(N/A)
    WIDE = 0xC4             // Prefix instruction; next instruction has a 16-bit index  arguments(N/A)
}
}

#[derive(Debug, PartialEq)]
pub struct ConstantBlock {
    pub memory_origin: Word,
    pub values: Vec<i32>,
}

#[derive(Debug, PartialEq)]
pub struct CodeBlock {
    pub memory_origin: Word,
    pub bytes: Vec<u8>,
    pub pc: usize,
}

impl Read for CodeBlock {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        let bytes_remaining = self.bytes.len() - self.pc;
        let amt = cmp::min(buf.len(), bytes_remaining);
        let (a, _) = self.bytes.split_at(amt);

        // First check if the amount of bytes we want to read is small:
        // `copy_from_slice` will generally expand to a call to `memcpy`, and
        // for a single byte the overhead is significant.
        if amt == 1 {
            buf[0] = a[0];
        } else {
            buf[..amt].copy_from_slice(a);
        }

        self.pc += amt;
        Ok(amt)
    }
}

impl Seek for CodeBlock {
    fn seek(&mut self, pos: SeekFrom) -> io::Result<u64> {
        let index = match pos {
            SeekFrom::Start(i) => Ok(i),
            SeekFrom::End(i) => validate_bounds(self.bytes.len() as i64 + i),
            SeekFrom::Current(i) => validate_bounds(self.pc as i64 + i),
        }?;

        self.pc = index as usize;
        Ok(index)
    }
}

fn validate_bounds(i: i64) -> io::Result<u64> {
    if i >= 0 {
        Ok(i as u64)
    } else {
        Err(io::Error::new(io::ErrorKind::Other, format!("Index ({:?}) out of bounds: ", i)))
    }
}

#[derive(Debug, PartialEq)]
pub struct Program {
    pub constants: ConstantBlock,
    pub code: CodeBlock
}

#[derive(Copy, Clone, Debug, PartialEq)]
pub enum IJVMError {
    IOError(io::ErrorKind),
    MalformedMIME,                  // the MIME bytes were smaller than [HEADER_BYTE_LEN] bytes
    InvalidMIME,                    // the MIME bytes did not match the IJVM spec
    ProgramDataNotFound,            // no program data was found in the 
    ConstantBlockNotFound,          // the constant block was not found in the program data
    MalformedConstantBlock,         // The contant block is not a multiple of [WORD_BYTE_LEN] bytes in size
    CodeBlockNotFound,              // the code block was not found in the program data
    EmptyCodeBlock,                 // the origin and header of a code were found, but the code block is empty 
    MalformedCodeBlock,             // if the code block is empty or not the expected number of bytes
    InvalidInstruction,             // if a instruction byte is read that does not map to an instruction
    ReadPastProgramData,            // if the fetch reads past the end of program data
    StepWithNoInstructionPrimed,    // if a step is requested with no instruction primed
    ExpectedInstructionArgument,    // if a instruction with an argument is being executed but the EOF is reached
    PopAttemptedOnEmptyStack,       // if a pop is attempted on an empty stack 
    MalformedOffset,                // if a offset is expected but EOF is reached
}

impl Display for IJVMError {
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(fmt, "IJVMError")
    }
}

impl From<io::Error> for IJVMError {
    fn from(error: io::Error) -> Self {
        IJVMError::IOError(error.kind())
    }
}

pub struct IJVM {
    state: IJVMState,
    program: Program,
    stack: Vec<i32>,
    input_file: Option<File>,
    output_file: Option<File>
}

#[derive(Debug, PartialEq)]
pub enum IJVMState {
    Primed(Instruction),
    Halted(HaltReason)
}

#[derive(Debug, PartialEq)]
pub enum HaltReason {
    HALTInstruction,
    ERRInstruction,
    Error(IJVMError)
}

/// fetch and validate the instruction at the given index
fn fetch(code_bytes: &[u8], i: usize) -> VMResult<Instruction> {
    let byte: u8 = code_bytes.get(i)
        .map(|&b| b)
        .ok_or_else(|| IJVMError::ReadPastProgramData)?;

    let instruction = Instruction::from_u8(byte)
        .ok_or_else(|| IJVMError::InvalidInstruction)?;

    Ok(instruction)
}

impl Drop for IJVM {
    fn drop(&mut self) {
        unimplemented!();
    }
}

impl IJVM {
    /// This function should return the word at the top of the stack of the current
    /// frame, interpreted as a signed integer.
    pub fn tos(&self) -> Option<i32> {
        self.stack.last().map(|&i| i)
    }

    /// Returns the stack of the current frame as an array of integers,
    /// with entry[0] being the very bottom of the stack and
    /// entry[stack_size() - 1] being the top.
    pub fn get_stack(&self) -> &Vec<i32> {
        &self.stack
    }

    /// Returns the currently loaded program text as a byte array.
    pub fn get_code_as_bytes(&self) -> &Vec<u8> {
        &self.program.code.bytes
    }

    /// Returns the value of the program counter (as an offset from the first instruction).
    pub fn get_program_counter(&self) -> usize {
        self.program.code.pc
    }

    /// Returns the i:th local variable of the current frame.
    pub fn get_local_variable(&self, i: usize) -> Option<i32> {
        self.stack.get(i).map(|&i| i)
    }

    /// Returns the constant at location i in the constant pool.
    pub fn get_constant(&self, i: usize) -> Option<i32> {
        self.program.constants.values.get(i).map(|&i| i)
    }

    /// Step (perform) one instruction and return.
    /// In the case of WIDE, perform the whole WIDE_ISTORE or WIDE_ILOAD.
    /// Returns true if an instruction was executed. Returns false if machine has
    /// halted or encountered an error.
    pub fn step(&mut self) -> VMResult<()> {
        // perform the primed instruction
        if let IJVMState::Primed(instruction) = self.state {
            match instruction {
                Instruction::BIPUSH => {
                    instructions::bipush(&mut self.stack, &mut self.program.code)
                },
                Instruction::DUP => instructions::dup(&mut self.stack),
                Instruction::ERR => instructions::err(&mut self.state),
                Instruction::GOTO => {
                    instructions::goto(&mut self.program.code)
                },
                Instruction::HALT => instructions::halt(&mut self.state),
                Instruction::IADD => instructions::iadd(&mut self.stack),
                Instruction::IAND => instructions::iand(&mut self.stack),
                Instruction::IFEQ => {
                    instructions::ifeq(&mut self.stack, &mut self.program.code)
                },
                Instruction::IFLT => {
                    instructions::iflt(&mut self.stack, &mut self.program.code)
                },
                Instruction::ICMPEQ => {
                    instructions::icmpeq(&mut self.stack, &mut self.program.code)
                },
                Instruction::IINC => instructions::iinc(),
                Instruction::ILOAD => instructions::iload(),
                Instruction::IN => instructions::read_in(),
                Instruction::INVOKEVIRTUAL => instructions::invokevirtual(),
                Instruction::IOR => instructions::ior(&mut self.stack),
                Instruction::IRETURN => instructions::ireturn(),
                Instruction::ISTORE => instructions::istore(),
                Instruction::ISUB => instructions::isub(&mut self.stack),
                Instruction::LDCW => instructions::ldcw(),
                Instruction::NOP => instructions::nop(),
                Instruction::OUT => instructions::write_out(&mut self.stack),
                Instruction::POP => instructions::pop(&mut self.stack),
                Instruction::SWAP => instructions::swap(&mut self.stack),
                Instruction::WIDE => instructions::wide(),
            }
        } else {
            return Err(IJVMError::StepWithNoInstructionPrimed)
        }?;
        
        // fetch the next instruction if it exists
        self.program.code.pc += 1;
        match self.fetch() {
            Ok(instruction) => {
                self.state = IJVMState::Primed(instruction);
                Ok(())
            },
            Err(err) => {
                self.state = IJVMState::Halted(HaltReason::Error(err));
                Err(err)
            }
        }
    }

    fn fetch(&self) -> VMResult<Instruction> {
        fetch(&self.program.code.bytes, self.program.code.pc)
    }

    /// Check whether the machine has any more instructions to execute.
    /// 
    /// A machine will stop running after:
    /// * reaching the end of the text section
    /// * encountering either the HALT/ERR instructions
    /// * encountering an invalid instruction
    pub fn is_finished(&self) -> bool {
        unimplemented!();
    }

    /// Run the vm with the current state until the machine halts.
    pub fn run(&self) {
        unimplemented!();
    }

    /// Returns the value of the current instruction represented as a u8.
    /// This should NOT increase the program counter.
    pub fn get_instruction_as_byte(&self) -> Option<u8> {
        self.get_instruction().map(|instruction| instruction as u8)
    }

    /// Returns the value of the current instruction represented as Rust enum.
    /// This should NOT increase the program counter.
    pub fn get_instruction(&self) -> Option<Instruction> {
       match self.state {
           IJVMState::Primed(instruction) => Some(instruction),
           IJVMState::Halted(_) => None,
       }
    }

    /// Sets the output of the IJVM instance to the provided file
    pub fn set_output_file(&mut self, file: File) {
        self.output_file = Some(file);
    }

    /// Sets the input of the IJVM instance to the provided file.
    pub fn set_input_file(&mut self, file: File) {
        self.input_file = Some(file);
    }

    /// Accepts and parses the bytes for a program e.g. the mime type should be stripped off
    /// # Arguments
    /// * `bytes` program bytes can will be consumed by this VM
    pub fn init_with_program_bytes(bytes: Vec<u8>) -> VMResult<IJVM> {
        let program = parse::program_bytes_to_program(bytes)?;
        let instruction = fetch(&program.code.bytes, 0)?;
        Ok(IJVM {
            state: IJVMState::Primed(instruction),
            program,
            stack: Vec::with_capacity(DEFAULT_STACK_SIZE),
            input_file: None,
            output_file: None
        })
    }

    /// Accepts and parses the bytes for a vm file e.g. the mime type is expected to be present
    /// # Arguments
    /// * `bytes` program bytes can will be consumed by this VM
    pub fn init_with_file_bytes(bytes: Vec<u8>) -> VMResult<IJVM> {
        let mut stream: &[u8] = &bytes;
        let bytes = parse::validate_and_strip_mime(&mut stream, Some(bytes.len()))?;
        IJVM::init_with_program_bytes(bytes)
    }

    /// Accepts and parses the file at the given path.
    pub fn init_with_file_path<P: AsRef<Path>>(file_path: P) -> VMResult<IJVM> {
        let bytes = parse::file_to_program_bytes(&file_path)?;
        IJVM::init_with_program_bytes(bytes)
    }
}