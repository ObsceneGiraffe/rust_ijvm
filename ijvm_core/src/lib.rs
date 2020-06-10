use std::{
    fmt,
    fmt::{Debug, Display},
    fs::File
};

#[cfg(test)]
mod tests {
    #[test]
    fn it_works() {
        assert_eq!(2 + 2, 4);
    }
}

#[allow(dead_code)]
type Byte = u8; /* raw memory will be typed as uint8 */

#[allow(dead_code)]
type Word = i32; /* the basic unit of the ijvm will be an int32 */

#[allow(dead_code)]
const MAGIC_NUMBER: usize = 0x1DEADFAD;

#[allow(dead_code)]
enum Op {
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

pub struct IJVMError;

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