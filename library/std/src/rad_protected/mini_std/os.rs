pub mod fd {
    use core::mem::ManuallyDrop;

    #[derive(Debug)]
    pub struct OwnedFd {
        fd: i32,
    }

    impl OwnedFd {
        pub unsafe fn from_raw_fd(fd: i32) -> Self {
            Self { fd }
        }

        pub fn into_raw_fd(self) -> i32 {
            let this = ManuallyDrop::new(self);
            this.fd
        }

        pub fn as_raw_fd(&self) -> i32 {
            self.fd
        }
    }

    impl Drop for OwnedFd {
        fn drop(&mut self) {
            unsafe { libc::close(self.fd); }
        }
    }
}
