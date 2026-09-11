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
    payload: *mut u8,
    slot_size: usize,
}

impl SharedMemory {
    pub(super) fn open(slot_size: usize) -> io::Result<Self> {
        let header_size = size_of::<SharedMemoryHeader>();
        let size = Self::calculate_size(slot_size);

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

        Ok(Self { header, payload, slot_size })
    }

    pub(super) fn close(&self) {
        unsafe { ptr::drop_in_place(self.header); }
        munmap(self.header as *mut _, Self::calculate_size(self.slot_size));
    }

    pub(super) fn get_slot(&self, slot: u32) -> *mut u8 {
        assert!(slot <= 2);
        unsafe {
            self.payload.add((slot as usize) * self.slot_size)
        }
    }

    fn calculate_size(slot_size: usize) -> usize {
        size_of::<SharedMemoryHeader>() + (slot_size * 3)
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
