use super::fs;
use alloc::string::String;
use alloc::vec::Vec;
use alloc::str::Utf8Error;

pub type Result<T> = core::result::Result<T, Error>;

#[derive(Debug)]
pub enum Error {
    Os(i32),
    Utf8(Utf8Error),
}

impl Error {
    #[cfg(target_os = "linux")]
    pub fn last_os_error() -> Self {
        Self::Os(unsafe { *libc::__errno_location() })
    }

    #[allow(unused)]
    pub fn raw_os_error(&self) -> Option<i32> {
        match self {
            Error::Os(errno) => Some(*errno),
            _ => None
        }
    }

    #[allow(unused)]
    pub fn raw_utf8_error(&self) -> Option<Utf8Error> {
        match self {
            Error::Utf8(err) => Some(*err),
            _ => None
        }
    }
}

pub struct BufReader {
    file: fs::File,
}

impl BufReader {
    pub fn new(file: fs::File) -> Self {
        Self { file }
    }

    fn read_line(&mut self) -> Option<Result<String>> {
        let mut bytes = Vec::new();

        loop {
            let mut buf = [0u8; 1];

            match self.file.read(&mut buf) {
                Ok(0) => {
                    if bytes.is_empty() {
                        return None;
                    }
                    break;
                }
                Ok(_) => {
                    if buf[0] == b'\n' {
                        break;
                    }
                    bytes.push(buf[0]);
                }
                Err(err) => {
                    return Some(Err(err));
                }
            }
        }

        match String::from_utf8(bytes) {
            Ok(str) => Some(Ok(str)),
            Err(err) => Some(Err(Error::Utf8(err.utf8_error())))
        }
    }

    pub fn lines(self) -> Lines {
        Lines { reader: self }
    }
}

pub struct Lines {
    reader: BufReader,
}

impl Iterator for Lines {
    type Item = Result<String>;

    fn next(&mut self) -> Option<Self::Item> {
        self.reader.read_line() 
    }
}
