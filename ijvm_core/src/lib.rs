use std::{
    fmt,
    fmt::{Debug, Display},
    fs::File,
    io,
    path::Path
};

#[cfg(test)]
mod tests {
    #[test]
    fn it_works() {
        assert_eq!(2 + 2, 4);
    }
}

pub type Byte = u8; // raw memory will be typed as uint8
pub type Word = u32; // the basic unit of the ijvm will be an int32
pub const MAGIC_NUMBER: u32 = 0x1DEADFAD;
pub const HEADER_BYTE_LEN: usize = 4;

pub enum Op {
    BIPUSH = 0x10,
    DUP = 0x59,
    ERR = 0xFE,
    GOTO = 0xA7,
    HALT = 0xFF,
    IADD = 0x60,
    IAND = 0x7E,
    IFEQ = 0x99,
    IFLT = 0x9B,
    ICMPEQ = 0x9F,
    IINC = 0x84,
    ILOAD = 0x15,
    IN = 0xFC,
    INVOKEVIRTUAL = 0xB6,
    IOR = 0xB0,
    IRETURN = 0xAC,
    ISTORE = 0x36,
    ISUB = 0x64,
    LDCW = 0x13,
    NOP = 0x00,
    OUT = 0xFD,
    POP = 0x57,
    SWAP = 0x5F,
    WIDE = 0xC4
}

pub enum IJVMError {
    IOError(io::Error),
    MalformedHeader,
    InvalidHeader,
    ByteCodeNotFound
}

impl Display for IJVMError {
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(fmt, "IJVMError")
    }
}

impl Debug for IJVMError {
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result { 
        write!(fmt, "IJVMError")
    }
}

impl From<io::Error> for IJVMError {
    fn from(error: io::Error) -> Self {
        IJVMError::IOError(error)
    }
}

pub fn parse_file<P: AsRef<Path>>(path: P) -> Result<Vec<Byte>, IJVMError> {
    let mut file = File::open(path)?;
    let bytes_to_read = file.metadata()
        .map(|m| m.len() as usize)
        .ok();
    parse_reader(&mut file, bytes_to_read)
}

pub fn parse_reader(reader: &mut dyn io::Read, reader_byte_len: Option<usize>) -> Result<Vec<Byte>, IJVMError> {
    let mut header_buf = [0; HEADER_BYTE_LEN];
    // try read in the file header convert an unexpected EOF to an MalformedHeader error 
    reader.read_exact(&mut header_buf)
        .map_err(|io_err| {
            match io_err.kind() {
                io::ErrorKind::UnexpectedEof => IJVMError::MalformedHeader,
                _ => IJVMError::IOError(io_err)
            }
        })?;

    // TODO: convert from BigEdian to LittleEndian
    let header: u32 = 0;

    if header == MAGIC_NUMBER {
        // We've already taken 4 bytes to check the header.
        // And we want to allocate one extra byte so the buffer doesn't need to grow before the
        // final `read` call at the end of the file. 4 - 1 = 3
        let mut bytes = match reader_byte_len {
            Some(byte_len) => Vec::with_capacity(byte_len - (HEADER_BYTE_LEN - 1)),
            None => Vec::with_capacity(1)
        };
        let bytes_read = reader.read_to_end(&mut bytes)?;

        if bytes_read > 0 {
            Ok(bytes)
        } else {
            Err(IJVMError::ByteCodeNotFound)
        }
    } else {
        Err(IJVMError::InvalidHeader)
    }
}

pub trait IJVM : Drop {
    /**
     * This function should return the word at the top of the stack of the current
     * frame, interpreted as a signed integer.
     **/
    fn tos() -> Word;

    /**
     * Returns the stack of the current frame as an array of integers,
     * with entry[0] being the very bottom of the stack and
     * entry[stack_size() - 1] being the top.
     **/
    fn get_stack() -> Vec<Word>;

    /**
     * Returns the currently loaded program text as a byte array.
     **/
    fn get_program_bytes() -> Vec<Byte>;

    /**
     * Returns the value of the program counter (as an offset from the first instruction).
     **/
    fn get_program_counter() -> i32;

    /**
     * @param i, index of variable to obtain.
     * @return Returns the i:th local variable of the current frame.
     **/
    fn get_local_variable(i: i32) -> Word;

    /**
     * @param i, index of the constant to obtain
     * @return The constant at location i in the constant pool.
     **/
    fn get_constant(i: i32) -> Word;

    /**
     * Step (perform) one instruction and return.
     * In the case of WIDE, perform the whole WIDE_ISTORE or WIDE_ILOAD.
     * Returns true if an instruction was executed. Returns false if machine has
     * halted or encountered an error.
     **/
    fn step() -> Result<(), IJVMError>;

    /**
     * Check whether the machine has any more instructions to execute.
     *
     * A machine will stop running after:
     * - reaching the end of the text section
     * - encountering either the HALT/ERR instructions
     * - encountering an invalid instruction
     */
    fn is_finished() -> bool;

    /**
     * Run the vm with the current state until the machine halts.
     **/
    fn run();


    /**
     * @return The value of the current instruction represented as a byte_t.
     *
     * This should NOT increase the program counter.
     **/
    fn get_instruction() -> Byte;


    /**
     * Sets the output of the IJVM instance to the provided file
     **/
    fn set_output_file(file: &File);


    /**
     * Sets the input of the IJVM instance to the provided file.
     **/
    fn set_input_file(file: &File);


    /**
     * Initializes the IJVM with the binary file found at the provided argument
     * Note. You need to be able to re-initialize the IJVM after it has been started.
     **/
    fn init(file: &File) -> Result<(), IJVMError>;
}