use super::mini_std::hal::PSRAM_BASE;

// TODO: Remove if no header is needed
pub(super) struct SharedMemoryHeader;

pub(super) struct SharedMemory;

impl SharedMemory {
    pub fn header(&mut self) -> &mut SharedMemoryHeader {
        unsafe { &mut *(PSRAM_BASE as *mut u8 as *mut SharedMemoryHeader) }
    }

    pub fn buffer(&mut self) -> *mut u8 {
        unsafe { (PSRAM_BASE as *mut u8).add(size_of::<SharedMemoryHeader>()) }
    }
}
