use ijvm_core::{
    IJVMError,
    Instruction
};

#[test]
fn test_malformed_mime() {
    let blob: [u8; 3] = [
        0x1D, 0xEA, 0xDF,     // corrupt MIME type
    ];

    let mut reader: &[u8] = &blob;
    let result = ijvm_core::validate_and_strip_mime(&mut reader, Some(blob.len()));
    assert_eq!(result, Err(IJVMError::MalformedMIME));
}

#[test]
fn test_invalid_mime() {
    let blob: [u8; 4] = [
        0x1D, 0xEA, 0xDF, 0x00,    // invalid MIME type
    ];

    let mut reader: &[u8] = &blob;
    let result = ijvm_core::validate_and_strip_mime(&mut reader, Some(blob.len()));
    assert_eq!(result, Err(IJVMError::InvalidMIME));
}

#[test]
fn test_nonexistent_program() {
    let blob: [u8; 4] = [
        0x1D, 0xEA, 0xDF, 0xAD,     // valid MIME type
    ];

    let result = ijvm_core::parse_file_bytes_to_program(blob.to_vec());
    assert_eq!(result, Err(IJVMError::ProgramDataNotFound));
}

#[test]
fn test_empty_constant_block() {
    let blob: [u8; 24] = [
        0x1D, 0xEA, 0xDF, 0xAD,     // MIME type
        0x00, 0x01, 0x00, 0x00,     // start constant block, memory origin
        0x00, 0x00, 0x00, 0x00,     // constant block byte length, value: 0 bytes
        0x00, 0x00, 0x00, 0x00,     // start code block, memory origin, value: 0
        0x00, 0x00, 0x00, 0x04,     // code block byte length, value: 4 bytes
        0x10, 0x70, 0x59, 0x10,     // BIPUSH, 0x70, DUP, BIPUSH,
    ];

    let result = ijvm_core::parse_file_bytes_to_program(blob.to_vec());
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

    let result = ijvm_core::parse_file_bytes_to_program(blob.to_vec());
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

    let result = ijvm_core::parse_file_bytes_to_program(blob.to_vec());
    assert_eq!(result, Err(IJVMError::MalformedConstantBlock));
}

#[test]
fn test_empty_code_block() {
    let blob: [u8; 20] = [
        0x1D, 0xEA, 0xDF, 0xAD,     // MIME type
        0x00, 0x01, 0x00, 0x00,     // start constant block, memory origin
        0x00, 0x00, 0x00, 0x00,     // constant block byte length, value: 0 bytes
        0x00, 0x00, 0x00, 0x00,     // start code block, memory origin, value: 0
        0x00, 0x00, 0x00, 0x00,     // code block byte length, value: 0 bytes
    ];

    let result = ijvm_core::parse_file_bytes_to_program(blob.to_vec());
    assert_eq!(result, Err(IJVMError::EmptyCodeBlock));
}

#[test]
fn test_malformed_code_block() {
    let blob: [u8; 20] = [
        0x1D, 0xEA, 0xDF, 0xAD,     // MIME type
        0x00, 0x01, 0x00, 0x00,     // start constant block, memory origin
        0x00, 0x00, 0x00, 0x00,     // constant block byte length, value: 0x0C => 12 bytes
        0x00, 0x00, 0x00, 0x00,     // start code block, memory origin, value: 0
        0x00, 0x00, 0x00, 0x04,     // code block byte length, value: 4 bytes
    ];

    let result = ijvm_core::parse_file_bytes_to_program(blob.to_vec());
    assert_eq!(result, Err(IJVMError::MalformedCodeBlock));
}

#[test]
fn test_malformed_code_block_trailing_bytes() {
    let blob: [u8; 22] = [
        0x1D, 0xEA, 0xDF, 0xAD,     // MIME type
        0x00, 0x01, 0x00, 0x00,     // start constant block, memory origin
        0x00, 0x00, 0x00, 0x00,     // constant block byte length, value: 0x0C => 12 bytes
        0x00, 0x00, 0x00, 0x00,     // start code block, memory origin, value: 0
        0x00, 0x00, 0x00, 0x04,     // code block byte length, value: 0 bytes
        0xEA, 0xAD
    ];

    let result = ijvm_core::parse_file_bytes_to_program(blob.to_vec());
    assert_eq!(result, Err(IJVMError::MalformedCodeBlock));
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
    
    let result = ijvm_core::parse_file_bytes_to_program(blob.to_vec());
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

#[test]
fn test_ijvm_init() {
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

    let result = ijvm_core::IJVM::init_with_file_bytes(blob.to_vec());
    assert!(result.is_ok());

    let vm = result.unwrap();
    assert_eq!(vm.get_constant(0), Some(-1));
    assert_eq!(vm.get_constant(1), Some(2));
    assert_eq!(vm.get_constant(2), Some(3));
    assert_eq!(vm.get_constant(3), None);
    assert_eq!(vm.get_instruction(), Some(Instruction::BIPUSH));
    assert_eq!(vm.get_local_variable(0), Some(0x70));
    assert_eq!(vm.get_local_variable(1), None);

    let mut vm: IJVM = vm;

    let result = vm.step();
    assert!(result.is_ok());

    assert_eq!(vm.get_instruction_as_byte(), Some(0x59));
    assert_eq!(vm.get_instruction(), Some(Instruction::DUP));
}