use std::{
    fmt::{self, Debug, Display},
    fs::File,
    io::{self},
    mem::size_of,
    path::Path
};

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_malformed_mime() {
        let blob: [u8; 3] = [
            0x1D, 0xEA, 0xDF,     // corrupt MIME type
        ];

        let mut reader: &[u8] = &blob;
        let result = validate_and_strip_mime(&mut reader, Some(blob.len()));
        assert_eq!(result, Err(IJVMError::MalformedMIME));
    }

    #[test]
    fn test_invalid_mime() {
        let blob: [u8; 4] = [
            0x1D, 0xEA, 0xDF, 0x00,    // invalid MIME type
        ];

        let mut reader: &[u8] = &blob;
        let result = validate_and_strip_mime(&mut reader, Some(blob.len()));
        assert_eq!(result, Err(IJVMError::InvalidMIME));
    }

    #[test]
    fn test_nonexistent_program() {
        let blob: [u8; 4] = [
            0x1D, 0xEA, 0xDF, 0xAD,     // valid MIME type
        ];

        let result = parse_file_bytes_to_program(blob.to_vec());
        assert_eq!(result, Err(IJVMError::ProgramDataNotFound));
    }

    #[test]
    fn test_empty_constant_block() {
        let blob: [u8; 24] = [
            0x1D, 0xEA, 0xDF, 0xAD,     // MIME type
            0x00, 0x01, 0x00, 0x00,     // start constant block, memory origin
            0x00, 0x00, 0x00, 0x00,     // constant block byte length, value: 0 bytes
            0x00, 0x00, 0x00, 0x00,     // start code block, memory origin, value: 0
            0x00, 0x00, 0x00, 0x04,     // code block byte length, value: 0x0F => 15 bytes
            0x10, 0x70, 0x59, 0x10,     // BIPUSH, 0x70, DUP, BIPUSH,
        ];

        let result = parse_file_bytes_to_program(blob.to_vec());
        assert!(result.is_ok());

        let program = result.unwrap();

        assert_eq!(program.constants.content.len(), 0);
        assert_eq!(program.code.content.len(), 4);
        assert_eq!(program.code.content[0], 0x10);
        assert_eq!(program.code.content[3], 0x10);
    }

    #[test]
    fn test_malformed_constant_block() {
        let blob: [u8; 12] = [
            0x1D, 0xEA, 0xDF, 0xAD,     // MIME type
            0x00, 0x01, 0x00, 0x00,     // start constant block, memory origin
            0x00, 0x00, 0x00, 0x0C,     // constant block byte length, value: 0x0C => 12 bytes
        ];

        let result = parse_file_bytes_to_program(blob.to_vec());
        assert_eq!(result, Err(IJVMError::MalformedConstantBlock));
    }

    #[test]
    fn test_malformed_constant_block_trailing_bytes() {
        let blob: [u8; 14] = [
            0x1D, 0xEA, 0xDF, 0xAD,     // MIME type
            0x00, 0x01, 0x00, 0x00,     // start constant block, memory origin
            0x00, 0x00, 0x00, 0x0C,     // constant block byte length, value: 0x0C => 12 bytes
            0x46, 0x35
        ];

        let result = parse_file_bytes_to_program(blob.to_vec());
        assert_eq!(result, Err(IJVMError::MalformedConstantBlock));
    }

    #[test]
    fn test_parse_bytes_to_program() {
        let blob: [u8; 47] = [
            0x1D, 0xEA, 0xDF, 0xAD,     // MIME type
            0x00, 0x01, 0x00, 0x00,     // start constant block, memory origin
            0x00, 0x00, 0x00, 0x0C,     // constant block byte length, value: 0x0C => 12 bytes
            0xFF, 0xFF, 0xFF, 0xFF,     // constant 0 = -1 
            0x00, 0x00, 0x00, 0x02,     // constant 1 = 2
            0x00, 0x00, 0x00, 0x03,     // constant 2 = 3
            0x00, 0x00, 0x00, 0x00,     // start code block, memory origin
            0x00, 0x00, 0x00, 0x0F,     // code block byte length, value: 0x0F => 15 bytes
            0x10, 0x70, 0x59, 0x10,     // BIPUSH, 0x70, DUP, BIPUSH,
            0xFF, 0x60, 0x59, 0x59,     // (0xFF) -1, IADD, DUP, DUP,
            0x10, 0xFF, 0x64, 0xFD,     // BIPUSH, (0xFF) -1, ISUB, OUT,
            0xFD, 0xFD, 0xFD,           // OUT, OUT, OUT
        ];
        
        let result = parse_file_bytes_to_program(blob.to_vec());
        assert!(result.is_ok());
        let program = result.unwrap();

        assert_eq!(program.constants.content.len(), 3);
        assert_eq!(program.constants.content[0], -1);
        assert_eq!(program.constants.content[1], 2);
        assert_eq!(program.constants.content[2], 3);
        assert_eq!(program.code.content.len(), 15);
        assert_eq!(program.code.content[0], 0x10);
        assert_eq!(program.code.content[14], 0xFD);
    }
}

type VMResult<T> = Result<T, IJVMError>;

pub type Word = u32; // the basic unit of the ijvm will be an int32
pub const WORD_BYTE_LEN: usize = size_of::<u32>();
pub const HEADER_BYTE_LEN: usize = WORD_BYTE_LEN;
pub const MAGIC_NUMBER: i32 = 0x1DEADFAD;
const DEFAULT_READ_BUFFER_SIZE: usize = 1000;
const DEFAULT_STACK_SIZE: usize = 100;

#[derive(Copy, Clone)]
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

#[derive(Debug, PartialEq)]
pub struct Block<T> {
    pub memory_origin: Word,
    pub content: Vec<T>
}

pub type ConstantBlock = Block<i32>;
pub type CodeBlock = Block<u8>;

#[derive(Debug, PartialEq)]
pub struct Program {
    pub constants: ConstantBlock,
    pub code: CodeBlock
}

#[derive(Debug, PartialEq)]
pub enum IJVMError {
    IOError(io::ErrorKind),
    MalformedMIME,              // the MIME bytes were smaller than [HEADER_BYTE_LEN] bytes
    InvalidMIME,                // the MIME bytes did not match the IJVM spec
    ProgramDataNotFound,        // no program data was found in the 
    ConstantBlockNotFound,      // the constant block was not found in the program data
    MalformedConstantBlock,     // The contant block is not a multiple of [WORD_BYTE_LEN] bytes in size
    CodeBlockNotFound,          // the code block was not found in the program data
    MalformedCodeBlock,         // if the code block is empty or not the expected number of bytes
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

pub fn parse_file_to_program_bytes<P: AsRef<Path>>(path: P) -> VMResult<Vec<u8>> {
    let mut file = File::open(path)?;
    let bytes_to_read = file.metadata()
        .map(|m| m.len() as usize)
        .ok();
    validate_and_strip_mime(&mut file, bytes_to_read)
}

/// validate and strip the mime type from given bytes
/// # Arguments
/// * `reader` used to read in the bytes to process
/// * `reader_byte_len` if the size of the reader is known ahead of reading, then supply it so that the buffer can be sized efficiently
pub fn validate_and_strip_mime(reader: &mut dyn io::Read, reader_byte_len: Option<usize>) -> VMResult<Vec<u8>> {
    let mut header_buf = [0; HEADER_BYTE_LEN];
    // try read in the file header convert an unexpected EOF to an MalformedMIME error 
    reader.read_exact(&mut header_buf)
        .map_err(|io_err| {
            match io_err.kind() {
                io::ErrorKind::UnexpectedEof => IJVMError::MalformedMIME,
                _ => IJVMError::IOError(io_err.kind())
            }
        })?;

    let header: i32 = i32::from_be_bytes(header_buf);

    if header == MAGIC_NUMBER {
        // We've already taken 4 bytes to check the header.
        // And we want to allocate one extra byte so the buffer doesn't need to grow before the
        // final `read` call at the end of the file. 4 - 1 = 3
        let mut bytes = match reader_byte_len {
            Some(byte_len) => Vec::with_capacity(byte_len - (HEADER_BYTE_LEN - 1)),
            None => Vec::with_capacity(DEFAULT_READ_BUFFER_SIZE)
        };
        let bytes_read = reader.read_to_end(&mut bytes)?;

        if bytes_read > 0 {
            Ok(bytes)
        } else {
            Err(IJVMError::ProgramDataNotFound)
        }
    } else {
        Err(IJVMError::InvalidMIME)
    }
}

fn parse_word_u32<F>(reader: &mut dyn io::Read, on_eof: F) -> VMResult<u32> 
    where F: FnOnce() -> IJVMError {
    let mut buf = [0u8; WORD_BYTE_LEN];
    reader.read_exact(&mut buf)
        .map_err(|io_err|
            match io_err.kind() {
                io::ErrorKind::UnexpectedEof => on_eof(),
                _ => IJVMError::IOError(io_err.kind())
            }
        )?;
    Ok(u32::from_be_bytes(buf))
}

fn parse_word_i32<F>(reader: &mut dyn io::Read, on_eof: F) -> VMResult<i32>
    where F: FnOnce() -> IJVMError {
    let value = parse_word_u32(reader, on_eof)?;
    Ok(value as i32)
}

pub fn parse_file_bytes_to_program(file_bytes: Vec<u8>) -> VMResult<Program> {
    let mut reader: &[u8] = &file_bytes[..];
    let program_bytes = validate_and_strip_mime(&mut reader, Some(file_bytes.len()))?;
    Ok(parse_program_bytes_to_program(program_bytes)?)
}

pub fn parse_program_bytes_to_program(bytes: Vec<u8>) -> VMResult<Program> {
    let mut reader: &[u8] = &bytes;
    let cons_block = parse_constant_block(&mut reader)?;
    let code_block = parse_code_block(&mut reader)?;

    Ok(
        Program {
            constants: cons_block,
            code: code_block
        }
    )
}

fn parse_constant_block(reader: &mut dyn io::Read) -> VMResult<ConstantBlock> {
    let mut reader = reader; 
    let memory_origin = parse_word_u32(&mut reader, || IJVMError::ConstantBlockNotFound)?;
    let byte_len = parse_word_u32(&mut reader, || IJVMError::ConstantBlockNotFound)? as usize;

    if byte_len % WORD_BYTE_LEN != 0 {
        return Err(IJVMError::MalformedConstantBlock)
    }

    let mut size = byte_len / WORD_BYTE_LEN;
    let mut values = Vec::with_capacity(byte_len);

    while size > 0 {
        size -= 1;
        values.push(parse_word_i32(&mut reader, || IJVMError::MalformedConstantBlock)?);
    }

    Ok(
        Block {
            memory_origin,
            content: values
        }
    )
} 

fn parse_code_block(reader: &mut dyn io::Read) -> VMResult<CodeBlock> {
    let mut reader = reader;
    let memory_origin = parse_word_u32(&mut reader, || IJVMError::CodeBlockNotFound)?;
    let byte_len = parse_word_u32(&mut reader, || IJVMError::CodeBlockNotFound)? as usize;

    if byte_len == 0 {
        return Err(IJVMError::CodeBlockNotFound)
    }

    let mut bytes = Vec::with_capacity(byte_len);
    let bytes_read = reader.read_to_end(&mut bytes)?;

    if bytes_read == 0 || bytes_read != byte_len {
        return Err(IJVMError::MalformedCodeBlock)
    }

    Ok(
        Block {
            memory_origin,
            content: bytes
        }
    )
}

pub struct IJVM {
    program: Program,
    pc: u32,
    instruction: Instruction,
    stack: Vec<Word>,
    input_file: Option<File>,
    output_file: Option<File>
}

impl Drop for IJVM {
    fn drop(&mut self) {
        unimplemented!();
    }
}

impl IJVM {
    /// This function should return the word at the top of the stack of the current
    /// frame, interpreted as a signed integer.
    pub fn tos(&self) -> Option<&Word> {
        self.stack.last()
    }

    /// Returns the stack of the current frame as an array of integers,
    /// with entry[0] being the very bottom of the stack and
    /// entry[stack_size() - 1] being the top.
    pub fn get_stack(&self) -> &Vec<Word> {
        &self.stack
    }

    /// Returns the currently loaded program text as a byte array.
    pub fn get_code_as_bytes(&self) -> &Vec<u8> {
        &self.program.code.content
    }

    /// Returns the value of the program counter (as an offset from the first instruction).
    pub fn get_program_counter(&self) -> u32 {
        self.pc
    }

    /// Returns the i:th local variable of the current frame.
    pub fn get_local_variable(&self, _i: usize) -> Word {
        unimplemented!();
    }

    /// Returns the constant at location i in the constant pool.
    pub fn get_constant(&self, i: usize) -> i32 {
        self.program.constants.content[i]
    }

    /// Step (perform) one instruction and return.
    /// In the case of WIDE, perform the whole WIDE_ISTORE or WIDE_ILOAD.
    /// Returns true if an instruction was executed. Returns false if machine has
    /// halted or encountered an error.
    pub fn step(&self) -> Result<(), IJVMError> {
        unimplemented!();
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
    pub fn get_instruction_as_byte(&self) -> u8 {
        *self.get_instruction() as u8
    }

    /// Returns the value of the current instruction represented as Rust enum.
    /// This should NOT increase the program counter.
    pub fn get_instruction(&self) -> &Instruction {
       &self.instruction
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
        let program = parse_program_bytes_to_program(bytes)?;
        Ok(IJVM {
            program,
            pc: 0u32,
            instruction: Instruction::BIPUSH,
            stack: Vec::with_capacity(DEFAULT_STACK_SIZE),
            input_file: None,
            output_file: None
        })
    }

    /// Accepts and parses the bytes for a vm file e.g. the mime type is expected to be present
    /// # Arguments
    /// * `bytes` program bytes can will be consumed by this VM
    pub fn init_with_file_bytes(bytes: Vec<u8>) -> VMResult<IJVM> {
        let mut reader: &[u8] = &bytes;
        let bytes = validate_and_strip_mime(&mut reader, Some(bytes.len()))?;
        IJVM::init_with_program_bytes(bytes)
    }

    /// Accepts and parses the file at the given path.
    pub fn init_with_file_path<P: AsRef<Path>>(file_path: P) -> VMResult<IJVM> {
        let bytes = parse_file_to_program_bytes(&file_path)?;
        IJVM::init_with_program_bytes(bytes)
    }
}