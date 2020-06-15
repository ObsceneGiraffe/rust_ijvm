use crate::{CodeBlock, ConstantBlock, IJVMError, Program, VMResult};
use crate::{DEFAULT_READ_BUFFER_SIZE, HEADER_BYTE_LEN, MAGIC_NUMBER, OFFSET_BYTE_LEN, WORD_BYTE_LEN};

use std::{
    fs::File,
    io::{self},
    path::Path
};

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn text_parse_word_EOF()
    {
        let blob: [u8; 3] = [0x1D, 0xEA, 0xDF];
        let mut reader: &[u8] = &blob;
        let result = word_u32(&mut reader, || IJVMError::InvalidInstruction);
        assert_eq!(result, Err(IJVMError::InvalidInstruction))
    }

    fn text_parse_word()
    {
        let blob: [u8; 4] = [0xFF, 0xFF, 0xFF, 0xFF];
        let mut reader: &[u8] = &blob;
        let result = word_u32(&mut reader, || IJVMError::InvalidInstruction);
        assert_eq!(result, Ok(u32::max_value()))
    }
}

/// Parse the file at the given path into the program bytes e.g. the files bytes without the mime type.
pub fn file_to_program_bytes<P: AsRef<Path>>(path: P) -> VMResult<Vec<u8>> {
    let mut file = File::open(path)?;
    let bytes_to_read = file.metadata()
        .map(|m| m.len() as usize)
        .ok();
    validate_and_strip_mime(&mut file, bytes_to_read)
}

/// Validate and strip the mime type from given bytes
/// # Arguments
/// * `reader` used to read in the bytes to process
/// * `reader_byte_len` if the size of the reader is known ahead of reading, then supply it so that the buffer can be sized efficiently
pub fn validate_and_strip_mime(stream: &mut dyn io::Read, reader_byte_len: Option<usize>) -> VMResult<Vec<u8>> {
    let mut header_buf = [0; HEADER_BYTE_LEN];
    // try read in the file header convert an unexpected EOF to an MalformedMIME error 
    stream.read_exact(&mut header_buf)
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
        let bytes_read = stream.read_to_end(&mut bytes)?;

        if bytes_read > 0 {
            Ok(bytes)
        } else {
            Err(IJVMError::ProgramDataNotFound)
        }
    } else {
        Err(IJVMError::InvalidMIME)
    }
}

/// Parses files bytes into a program.
/// File bytes are a sequence of bytes with a mime type header
pub fn file_bytes_to_program(file_bytes: Vec<u8>) -> VMResult<Program> {
    let mut stream: &[u8] = &file_bytes[..];
    let program_bytes = validate_and_strip_mime(&mut stream, Some(file_bytes.len()))?;
    Ok(program_bytes_to_program(program_bytes)?)
}

/// Parses program bytes into a program.
/// Program bytes are a sequence of bytes without a mime type header
pub fn program_bytes_to_program(bytes: Vec<u8>) -> VMResult<Program> {
    let mut stream: &[u8] = &bytes;
    let cons_block = constant_block(&mut stream)?;
    let code_block = code_block(&mut stream)?;

    Ok(
        Program {
            constants: cons_block,
            code: code_block
        }
    )
}

/// Parses the constant block from a given stream
fn constant_block(stream: &mut dyn io::Read) -> VMResult<ConstantBlock> {
    let mut stream = stream; 
    let memory_origin = word_u32(&mut stream, || IJVMError::ConstantBlockNotFound)?;
    let byte_len = word_u32(&mut stream, || IJVMError::ConstantBlockNotFound)? as usize;

    if byte_len % WORD_BYTE_LEN != 0 {
        return Err(IJVMError::MalformedConstantBlock)
    }

    let mut size = byte_len / WORD_BYTE_LEN;
    let mut values = Vec::with_capacity(byte_len);

    while size > 0 {
        size -= 1;
        values.push(word_i32(&mut stream, || IJVMError::MalformedConstantBlock)?);
    }

    Ok(ConstantBlock { memory_origin, values })
} 

/// Parses the code block from a given stream
fn code_block(stream: &mut dyn io::Read) -> VMResult<CodeBlock> {
    let mut stream = stream;
    let memory_origin = word_u32(&mut stream, || IJVMError::CodeBlockNotFound)?;
    let byte_len = word_u32(&mut stream, || IJVMError::CodeBlockNotFound)? as usize;

    if byte_len == 0 {
        return Err(IJVMError::EmptyCodeBlock)
    }

    let mut bytes = Vec::with_capacity(byte_len);
    let bytes_read = stream.read_to_end(&mut bytes)?;

    if bytes_read == 0 || bytes_read != byte_len {
        return Err(IJVMError::MalformedCodeBlock)
    }

    Ok(CodeBlock { memory_origin, bytes, pc: 0usize })
}

/// Parse a single IJVM word.
/// IJVM binary is Big Endian (BE) and so this function will convert the BE binary to the native endianess 
/// x86 is Little Endian
pub fn word_u32<F>(stream: &mut dyn io::Read, on_eof: F) -> VMResult<u32> 
    where F: FnOnce() -> IJVMError {
    let mut buf = [0u8; WORD_BYTE_LEN];
    stream.read_exact(&mut buf)
        .map_err(|io_err|
            match io_err.kind() {
                io::ErrorKind::UnexpectedEof => on_eof(),
                _ => IJVMError::IOError(io_err.kind())
            }
        )?;
    Ok(u32::from_be_bytes(buf))
}

/// The i32 variant of word_u32
pub fn word_i32<F>(stream: &mut dyn io::Read, on_eof: F) -> VMResult<i32>
    where F: FnOnce() -> IJVMError {
    let value = word_u32(stream, on_eof)?;
    Ok(value as i32)
}

pub fn offset<F>(stream: &mut dyn io::Read, on_eof: F) -> VMResult<u16> 
    where F: FnOnce() -> IJVMError {
    let mut buf = [0u8; OFFSET_BYTE_LEN];
    stream.read_exact(&mut buf)
    .map_err(|io_err|
        match io_err.kind() {
            io::ErrorKind::UnexpectedEof => on_eof(),
            _ => IJVMError::IOError(io_err.kind())
        }
    )?;
    Ok(u16::from_be_bytes(buf))
}