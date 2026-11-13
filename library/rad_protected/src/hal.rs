use core::fmt::{self, Write};
use core::sync::atomic::{AtomicUsize, Ordering};

static WRITE: AtomicUsize = AtomicUsize::new(0);
static CORE_NUM: AtomicUsize = AtomicUsize::new(0);
static FIFO_PUSH_BLOCKING: AtomicUsize = AtomicUsize::new(0);
static FIFO_POP_BLOCKING: AtomicUsize = AtomicUsize::new(0);

pub(crate) fn init_hal(write: fn(&[u8]), core_num: fn()->u32, fifo_push_blocking: fn(u32), fifo_pop_blocking: fn()->u32) {
    WRITE.store(write as usize, Ordering::Release);
    CORE_NUM.store(core_num as usize, Ordering::Release);
    FIFO_PUSH_BLOCKING.store(fifo_push_blocking as usize, Ordering::Release);
    FIFO_POP_BLOCKING.store(fifo_pop_blocking as usize, Ordering::Release);
}

pub(crate) fn write(s: &str) -> Option<()> {
    let write = WRITE.load(Ordering::Acquire);

    if write != 0 {
        let f: fn(&[u8]) = unsafe { 
            core::mem::transmute(write) 
        };
        f(s.as_bytes());
        return Some(());
    }
    None
}

pub(crate) fn core_num() -> Option<u32> {
    let core_num = CORE_NUM.load(Ordering::Acquire);

    if core_num != 0 {
        let f: fn()->u32 = unsafe { 
            core::mem::transmute(core_num) 
        };
        return Some(f());
    }
    None
}

pub(crate) fn fifo_push_blocking(data: u32) -> Option<()> {
    let fifo_push_blocking = FIFO_PUSH_BLOCKING.load(Ordering::Acquire);

    if fifo_push_blocking != 0 {
        let f: fn(u32) = unsafe { 
            core::mem::transmute(fifo_push_blocking) 
        };
        f(data);
        return Some(())
    }
    None
}

pub(crate) fn fifo_pop_blocking() -> Option<u32> {
    let fifo_pop_blocking = FIFO_POP_BLOCKING.load(Ordering::Acquire);

    if fifo_pop_blocking != 0 {
        let f: fn()->u32 = unsafe { 
            core::mem::transmute(fifo_pop_blocking) 
        };
        return Some(f())
    }
    None
}

pub(crate) struct DeviceWriter;

impl Write for DeviceWriter {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        write(s).ok_or(core::fmt::Error)
    }
}
