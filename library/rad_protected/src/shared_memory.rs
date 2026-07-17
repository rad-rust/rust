use super::libc_helpers::{shared_mmap, munmap};
use super::mini_std::{io, ipc::Barrier};
use core::{mem::size_of, ptr, ops::{Deref, DerefMut}};

pub(super) struct SharedMemoryData {
    barrier: Barrier,
}

impl SharedMemoryData {
    pub(super) fn sync(&self) -> bool {
        self.barrier.wait().is_leader()
    }
}

#[derive(Debug)]
pub(super) struct SharedMemory {
    inner: *mut SharedMemoryData,
}

impl SharedMemory {
    pub(super) fn open() -> io::Result<Self> {
        let size = size_of::<SharedMemoryData>();

        let ptr = shared_mmap(size)?;

        let inner = ptr.cast::<SharedMemoryData>();

        unsafe {
            ptr::write(inner,
                SharedMemoryData {
                    barrier: Barrier::new(3),
                },
            );
        }

        Ok(Self { inner })
    }

    pub(super) fn close(&self) {
        unsafe { ptr::drop_in_place(self.inner); }
        munmap(self.inner as *mut _, size_of::<SharedMemoryData>());
    }
}

unsafe impl Send for SharedMemory {}
unsafe impl Sync for SharedMemory {}

impl Deref for SharedMemory {
    type Target = SharedMemoryData;

    fn deref(&self) -> &Self::Target {
        unsafe { &*self.inner }
    }
}

impl DerefMut for SharedMemory {
    fn deref_mut(&mut self) -> &mut Self::Target {
        unsafe { &mut *self.inner }
    }
}
