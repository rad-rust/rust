use super::fork::{fork_copy, ForkOutcome};
use super::role::{ROLE, Role, Parent, Child};
use super::shared_memory::SharedMemory;

/// Runtime for rad_protected
#[stable(feature = "rad_protected", since = "1.95.0")]
#[derive(Debug)]
pub struct Runtime;

impl Runtime {
    
    /// Triplicate the running process over the current rad_protected function
    /// Fork the running process and copy its memory to create 3 identical processes
    #[stable(feature = "rad_protected", since = "1.95.0")]
    #[rustc_diagnostic_item = "triplicate_process"]
    pub fn triplicate_process(payload_size: usize) -> Result<ProcessGuard, ()> {
        if ROLE.lock().unwrap().as_ref().is_some() {
            return Err(());
        }

        let Ok(shared_memory) = SharedMemory::open(payload_size) else {
            return Err(());
        };

        let link1 = match fork_copy() {
            Some(ForkOutcome::Parent(link1)) => link1,
            Some(ForkOutcome::Child) => {
                ROLE.lock().unwrap().replace(Role::Child(Child::new(shared_memory)));
                return Ok(ProcessGuard{});
            }
            None => { 
                shared_memory.close();
                return Err(());
            }
        };

        let link2 = match fork_copy() {
            Some(ForkOutcome::Parent(link2)) => link2,
            Some(ForkOutcome::Child) => {
                ROLE.lock().unwrap().replace(Role::Child(Child::new(shared_memory)));
                return Ok(ProcessGuard{});
            }
            None => {
                shared_memory.close();
                link1.kill_child();
                return Err(());
            }
        };

        ROLE.lock().unwrap().replace(Role::Parent(Parent::new(
            shared_memory,
            link1,
            link2,
        )));

        Ok(ProcessGuard{})
    }

    /// Enter a critical (unsafe) section of code, allowing only a single process through
    /// Syncs the three processes. Returns `true` for the one leader (parent) process
    #[stable(feature = "rad_protected", since = "1.95.0")]
    pub fn enter_critical_section() -> bool {
        let mut guard = ROLE.lock().unwrap();
        if let Some(role) = guard.as_mut() {
            return role.ctx_mut().enter_critical_section();
        }
        true
    }

    /// Exit a critical (unsafe) section of code
    /// Syncs the three processes
    #[stable(feature = "rad_protected", since = "1.95.0")]
    pub fn exit_critical_section() {
        let mut guard = ROLE.lock().unwrap();
        if let Some(role) = guard.as_mut() {
            return role.ctx_mut().exit_critical_section();
        }
    }

    /// Close and clean up the triplicated processes at the end of rad_protected execution
    #[stable(feature = "rad_protected", since = "1.95.0")]
    pub fn close() {
        let mut guard = ROLE.lock().unwrap();
        if let Some(role) = guard.as_ref() {
            role.ctx().sync();
            if let Role::Parent(parent) = role {
                parent.kill_children();
                parent.close_shared_mem();
            } else {
                unsafe { libc::pause(); }
            }
        }
        guard.take();
    }

    // Checkpoint given locals via a majority vote over the triplicated threads
    #[stable(feature = "rad_protected", since = "1.95.0")]
    #[rustc_diagnostic_item = "checkpoint"]
    pub fn checkpoint(locals: &[(*mut u8, usize)]) {
        if locals.is_empty() {
            return;
        }

        let hex_fmt = b"%02x \0".as_ptr() as *const libc::c_char;
        let nl_fmt = b"\n\0".as_ptr() as *const libc::c_char;

        for i in 0..locals.len() {
            let (buf_ptr, buf_len) = locals[i];

            if buf_ptr.is_null() || buf_len == 0 {
                continue;
            }

            for j in 0..buf_len {
                let byte = unsafe { *buf_ptr.add(j) };
                unsafe { libc::printf(hex_fmt, byte as libc::c_int); }
            }
            unsafe { libc::printf(nl_fmt); }
        }
    }


    // Internal checkpoint marker inserted during MIR building
    // Indicates the MIR pass should rewrite the terminator to a `checkpoint` call
    #[stable(feature = "rad_protected", since = "1.95.0")]
    #[rustc_diagnostic_item = "__checkpoint"]
    pub fn __checkpoint() {
    }
}

/// Guard to properly drop processes when done with the rad_protected function
#[stable(feature = "rad_protected", since = "1.95.0")]
#[derive(Debug)]
pub struct ProcessGuard;

/// Drop method for `ProcessGuard`, close the child processes
#[stable(feature = "rad_protected", since = "1.95.0")]
impl Drop for ProcessGuard {
    fn drop(&mut self) {
        Runtime::close();
    }
}
