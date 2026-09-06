use super::libc_helpers::{shared_mmap, munmap};
use super::mini_std::{io, ipc::Barrier};
use core::{mem::size_of, ptr, ops::{Deref, DerefMut}};

pub(super) struct SharedMemoryHeader {
    barrier: Barrier,
}

impl SharedMemoryHeader {
    pub(super) fn sync(&self) -> bool {
        self.barrier.wait().is_leader()
    }
}

#[derive(Debug)]
pub(super) struct SharedMemory {
    header: *mut SharedMemoryHeader,
    _payload: *mut u8,
    size: usize,
}

impl SharedMemory {
    pub(super) fn open(payload_size: usize) -> io::Result<Self> {
        let header_size = size_of::<SharedMemoryHeader>();
        let size = header_size + (payload_size * 3);

        let ptr = shared_mmap(size)? as *mut u8;

        let header = ptr.cast::<SharedMemoryHeader>();
        let payload = unsafe { ptr.add(header_size) };

        unsafe {
            ptr::write(header,
                SharedMemoryHeader {
                    barrier: Barrier::new(3),
                },
            );
        }

        Ok(Self { header, _payload: payload, size })
    }

    pub(super) fn close(&self) {
        unsafe { ptr::drop_in_place(self.header); }
        munmap(self.header as *mut _, self.size);
    }
}

unsafe impl Send for SharedMemory {}
unsafe impl Sync for SharedMemory {}

impl Deref for SharedMemory {
    type Target = SharedMemoryHeader;

    fn deref(&self) -> &Self::Target {
        unsafe { &*self.header }
    }
}

impl DerefMut for SharedMemory {
    fn deref_mut(&mut self) -> &mut Self::Target {
        unsafe { &mut *self.header }
    }
}
