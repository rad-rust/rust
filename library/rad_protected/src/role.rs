use super::mini_std::hal::{fifo_push_blocking, fifo_pop_blocking};
use super::mini_std::ipc::CoreLocal;
use super::checkpoint::Checkpoint;
use core::{ptr, slice};

const MSG_BARRIER: u32 = 0x1;
const MSG_ACK: u32 = 0x2;
const CHECKPOINT_MSG: u32 = 0x3;
const VERDICT_OK: u32 = 0x4;
const VERDICT_BAD: u32 = 0x5;

// Each core gets a unique role
// TODO: Wrap with Mutex if in a multithreaded environment
pub(super) static ROLE: CoreLocal<Role> = 
    CoreLocal::new(
        Role::Parent(Parent { crit_depth: 0 }),
        Role::Child,
    );

#[rustc_diagnostic_item = "checkpoint_buffer_size"]
const BUFFER_SIZE: usize = 2048;

// Shared SRAM buffer
static mut CHECKPOINT_BUFFER: [u8; BUFFER_SIZE] = [0; BUFFER_SIZE];

#[derive(Debug)]
pub(super) enum Role {
    Parent(Parent),
    Child,
}

impl Role {
    pub(super) fn enter_critical_section(&mut self) -> bool {
        match self {
            Role::Parent(parent) => {
                if parent.crit_depth == 0 {
                    Parent::sync();
                }
                parent.crit_depth += 1;
                return true;
            },
            Role::Child => {
                Child::sync();
                return false;
            }
        }
    }

    pub(super) fn exit_critical_section(&mut self) {
        match self {
            Role::Parent(parent) => {
                if parent.crit_depth > 0 {
                    parent.crit_depth -= 1;
                }
                if parent.crit_depth == 0 {
                    Parent::sync();
                }
            },
            Role::Child => {
                Child::sync();
            }
        }
    }

    pub(super) fn sync(&self) {
        match self {
            Role::Parent(_) => Parent::sync(),
            Role::Child => Child::sync(),
        }
    }

    pub(super) fn checkpoint(&self, locals: &[(*mut u8, usize)]) {
        if self.compare_locals(locals) {
            Checkpoint::snapshot();
        } else {
            Checkpoint::rollback();
        }
    }

    fn compare_locals(&self, locals: &[(*mut u8, usize)]) -> bool {
        match self {
            Role::Parent(_) => {
                while fifo_pop_blocking() != CHECKPOINT_MSG {}

                let mut offset = 0usize;

                for &(local_ptr, size) in locals {
                    let local = unsafe { slice::from_raw_parts(local_ptr.cast_const(), size) };

                    if unsafe { local != &CHECKPOINT_BUFFER[offset..offset + size] } {
                        fifo_push_blocking(VERDICT_BAD);
                        return false;
                    }

                    offset += size;
                }

                fifo_push_blocking(VERDICT_OK);
                true
            },
            Role::Child => {
                let mut offset = 0usize;

                for &(local_ptr, size) in locals {
                    unsafe {
                        ptr::copy_nonoverlapping(
                            local_ptr.cast_const(),
                            CHECKPOINT_BUFFER.as_mut_ptr().add(offset),
                            size,
                        );
                    }

                    offset += size;
                }

                fifo_push_blocking(CHECKPOINT_MSG);
                fifo_pop_blocking() == VERDICT_OK
            }
        }
    }
}

#[derive(Debug)]
pub struct Parent {
    crit_depth: u32,
}

impl Parent {
    fn sync() {
        while fifo_pop_blocking() != MSG_BARRIER { }
        fifo_push_blocking(MSG_ACK);
    }
}

pub struct Child;

impl Child {
    fn sync() {
        fifo_push_blocking(MSG_BARRIER);
        while fifo_pop_blocking() != MSG_ACK { }
    }
}
