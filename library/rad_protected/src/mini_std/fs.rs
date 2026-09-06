use alloc::ffi::CString;
use super::io;

pub struct File {
    fd: i32,
}

impl File {
    pub fn open(path: &str) -> io::Result<File> {
        let path = CString::new(path).unwrap();
        let fd = unsafe { libc::open(path.as_ptr(), libc::O_RDONLY) };

        if fd == -1 {
            return Err(io::Error::last_os_error());
        }
        Ok(Self { fd })
    }

    pub fn read(&mut self, buf: &mut [u8]) -> io::Result<isize> {
        let len = buf.len();
        let buf = buf.as_mut_ptr() as *mut libc::c_void;

        let bytes_read = unsafe { libc::read(self.fd, buf, len) };

        if bytes_read == -1 {
            return Err(io::Error::last_os_error());
        }
        Ok(bytes_read)
    }
}

impl Drop for File {
    fn drop(&mut self) {
        unsafe { libc::close(self.fd); }
    }
}
