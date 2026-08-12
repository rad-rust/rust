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
    pub fn triplicate_process() -> Result<ProcessGuard, ()> {
        if ROLE.lock().unwrap().as_ref().is_some() {
            return Err(());
        }

        let Ok(shared_memory) = SharedMemory::open() else {
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

    #[stable(feature = "rad_protected", since = "1.95.0")]
    #[rustc_diagnostic_item = "checkpoint"]
    pub fn checkpoint() {
        let fd: libc::c_int = 1; 
        let message = b"Hello, World!\n";
        let buf = message.as_ptr() as *const libc::c_void;
        let count = message.len() as libc::size_t;
        unsafe { libc::write(fd, buf, count); }
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
