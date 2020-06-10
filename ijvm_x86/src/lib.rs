
use std::fs::File;

use ijvm_core::{
    IJVM,
    IJVMError,
    Word,
    Byte
};

#[cfg(test)]
mod tests {
    #[test]
    fn it_works() {
        assert_eq!(2 + 2, 4);
    }
}

pub struct IJVMx86 {

}

impl Drop for IJVMx86 {
    fn drop(&mut self) {
        unimplemented!();
    }
}

impl IJVM for IJVMx86 {
        /**
     * This function should return the word at the top of the stack of the current
     * frame, interpreted as a signed integer.
     **/
     fn tos() -> Word {
        unimplemented!();
     }

     /**
      * Returns the stack of the current frame as an array of integers,
      * with entry[0] being the very bottom of the stack and
      * entry[stack_size() - 1] being the top.
      **/
     fn get_stack() -> Vec<Word> {
        unimplemented!();
     }
 
     /**
      * Returns the currently loaded program text as a byte array.
      **/
     fn get_program_bytes() -> Vec<Byte> {
        unimplemented!();
     }
 
     /**
      * Returns the value of the program counter (as an offset from the first instruction).
      **/
     fn get_program_counter() -> i32 {
        unimplemented!();
     }
 
     /**
      * @param i, index of variable to obtain.
      * @return Returns the i:th local variable of the current frame.
      **/
     fn get_local_variable(_i: i32) -> Word {
        unimplemented!();
     }
 
     /**
      * @param i, index of the constant to obtain
      * @return The constant at location i in the constant pool.
      **/
     fn get_constant(_i: i32) -> Word {
        unimplemented!();
     }
 
     /**
      * Step (perform) one instruction and return.
      * In the case of WIDE, perform the whole WIDE_ISTORE or WIDE_ILOAD.
      * Returns true if an instruction was executed. Returns false if machine has
      * halted or encountered an error.
      **/
     fn step() -> Result<(), IJVMError> {
        unimplemented!();
     }
 
     /**
      * Check whether the machine has any more instructions to execute.
      *
      * A machine will stop running after:
      * - reaching the end of the text section
      * - encountering either the HALT/ERR instructions
      * - encountering an invalid instruction
      */
     fn is_finished() -> bool {
        unimplemented!();
     }
 
     /**
      * Run the vm with the current state until the machine halts.
      **/
     fn run() {
        unimplemented!();
     }
 
 
     /**
      * @return The value of the current instruction represented as a byte_t.
      *
      * This should NOT increase the program counter.
      **/
     fn get_instruction() -> Byte {
        unimplemented!();
     }
 
 
     /**
      * Sets the output of the IJVM instance to the provided file
      **/
     fn set_output_file(_file: &File) {
        unimplemented!();
     }
 
     /**
      * Sets the input of the IJVM instance to the provided file.
      **/
     fn set_input_file(_file: &File) {
        unimplemented!();
     }
 
     fn init(_file: &File) -> Result<(), IJVMError> {
         unimplemented!();
     }
}