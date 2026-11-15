use core::{ptr, slice};
use core::fmt::Write;

use crate::hal;

const MSG_BARRIER: u32 = 0x1;
const MSG_ACK: u32 = 0x2;
const CHECKPOINT_MSG: u32 = 0x3;
const VERDICT_OK: u32 = 0x4;
const VERDICT_BAD: u32 = 0x5;

#[rustc_diagnostic_item = "checkpoint_buffer_size"]
const BUFFER_SIZE: usize = 2048;

// Shared SRAM buffer
static mut CHECKPOINT_BUFFER: [u8; BUFFER_SIZE] = [0; BUFFER_SIZE];

// Fake PSRAM buffer on SRAM for demo
static mut PSRAM_DATA: PsramData = PsramData {
    before_size: 0,
    buffer: [0; BUFFER_SIZE],
};

struct PsramData {
    before_size: usize,
    buffer: [u8; BUFFER_SIZE],
}

pub(super) type Regions<'a> = &'a [(*mut u8, usize, bool)];

pub(super) enum Core {
    Core0,
    Core1,
}

impl Core {
    fn get_core() -> Self {
        match hal::core_num() {
            Some(0) => Core::Core0,
            Some(1) => Core::Core1,
            _ => panic!(),
        }
    }
}

pub(crate) fn checkpoint(site: u32, regions: Regions<'_>) -> bool {
    if compare_regions(regions) {
        snapshot(site, regions, false);
        true
    } else {
        false
    }
}

fn compare_regions(regions: Regions<'_>) -> bool {
    match Core::get_core() {
        Core::Core0 => {
            while hal::fifo_pop_blocking().unwrap() != CHECKPOINT_MSG {}

            let mut offset = 0usize;

            for &(local_ptr, size, compare) in regions {
                if !compare {
                    continue;
                }
                
                let local = unsafe { slice::from_raw_parts(local_ptr.cast_const(), size) };

                if unsafe { local != &CHECKPOINT_BUFFER[offset..offset + size] } {
                    hal::fifo_push_blocking(VERDICT_BAD);
                    return false;
                }

                offset += size;
            }

            hal::fifo_push_blocking(VERDICT_OK);
            true
        },
        Core::Core1 => {
            let mut offset = 0usize;

            for &(local_ptr, size, compare) in regions {
                if !compare {
                    continue;
                }

                unsafe {
                    ptr::copy_nonoverlapping(
                        local_ptr.cast_const(),
                        #[allow(static_mut_refs)]
                        CHECKPOINT_BUFFER.as_mut_ptr().add(offset),
                        size,
                    );
                }

                offset += size;
            }

            hal::fifo_push_blocking(CHECKPOINT_MSG);
            hal::fifo_pop_blocking().unwrap() == VERDICT_OK
        }
    }
}

// TODO: This snapshot/restore implementation is a hacky workaround for the demo. Note that it only works when:
//      1. The delta contains the entire state
//      2. No skippable restore sites are present
//      3. There are no heap reallocations
pub(crate) fn snapshot(_site: u32, regions: Regions<'_>, await_effects: bool) {
    if !matches!(Core::get_core(), Core::Core0) {
        return;
    }

    unsafe {
        let mut offset = PSRAM_DATA.before_size;
        let buffer = ptr::addr_of_mut!(PSRAM_DATA.buffer).cast::<u8>();

        for &(local_ptr, size, _compare) in regions {
            assert!(offset + size <= BUFFER_SIZE);

            ptr::copy_nonoverlapping(
                local_ptr.cast_const(),
                buffer.add(offset),
                size,
            );

            offset += size;
        }

        PSRAM_DATA.before_size = if await_effects { 0 } else { offset };
    }
}

pub(crate) fn restore(_site: u32, checkpoint: Regions<'_>, await_effects: Regions<'_>) {
    unsafe {
        let buffer = ptr::addr_of!(PSRAM_DATA.buffer).cast::<u8>();
        let mut offset = 0usize;

        for regions in [checkpoint, await_effects] {
            for &(local_ptr, size, _compare) in regions {
                assert!(offset + size <= BUFFER_SIZE);

                ptr::copy_nonoverlapping(
                    buffer.add(offset),
                    local_ptr,
                    size,
                );

                offset += size;
            }
        }
    }
}

pub(crate) fn sync() {
    match Core::get_core() {
        Core::Core0 => {
            while hal::fifo_pop_blocking().unwrap() != MSG_BARRIER { }
            hal::fifo_push_blocking(MSG_ACK);
        },
        Core::Core1 => {
            hal::fifo_push_blocking(MSG_BARRIER);
            while hal::fifo_pop_blocking().unwrap() != MSG_ACK { }
        },
    }
}

#[allow(dead_code)]
pub(crate) fn print_checkpoint(site: u32, regions: Regions<'_>, kind: &str) {
    if !matches!(Core::get_core(), Core::Core0) {
        return;
    }

    let mut w = hal::DeviceWriter;
    let _ = writeln!(w, "{kind}: state {site}, {} regions", regions.len());

    for (i, &(ptr, len, compare)) in regions.iter().enumerate() {
        let _ = writeln!(
            w,
            "  region {i}: {len} bytes at {ptr:p} {}",
            if compare { "comparing" } else { "non-comparing" }
        );

        let _ = write!(w, "    bytes: ");
        if !ptr.is_null() && len != 0 {
            let bytes = unsafe { core::slice::from_raw_parts(ptr as *const u8, len) };
            for &b in bytes {
                let _ = write!(w, "{b:02x} ");
            }
        }
        let _ = writeln!(w);
    }
}
