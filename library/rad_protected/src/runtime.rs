use super::fork::{fork_copy, ForkOutcome};
use super::role::{ROLE, Role, Parent};

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

        let link1 = match fork_copy() {
            Some(ForkOutcome::Parent(link1)) => link1,
            Some(ForkOutcome::Child(child)) => {
                ROLE.lock().unwrap().replace(Role::Child(child));
                return Ok(ProcessGuard{});
            }
            None => { return Err(()); }
        };

        let link2 = match fork_copy() {
            Some(ForkOutcome::Parent(link2)) => link2,
            Some(ForkOutcome::Child(child)) => {
                ROLE.lock().unwrap().replace(Role::Child(child));
                return Ok(ProcessGuard{});
            }
            None => {
                link1.kill_child();
                return Err(());
            }
        };

        ROLE.lock().unwrap().replace(Role::Parent(Parent::new(
            link1,
            link2,
        )));

        Ok(ProcessGuard{})
    }

    /// Enter a critical (unsafe) section of code, allowing only a single process through
    /// Syncs the three processes. Returns `true` for the one leader (parent) process
    #[stable(feature = "rad_protected", since = "1.95.0")]
    pub fn enter_critical_section() -> bool {
        let guard = ROLE.lock().unwrap();
        if let Some(role) = guard.as_ref() {
            Self::sync(role);
            return role.is_parent();
        }
        true
    }

    /// Exit a critical (unsafe) section of code
    /// Syncs the three processes
    #[stable(feature = "rad_protected", since = "1.95.0")]
    pub fn exit_critical_section() {
        let guard = ROLE.lock().unwrap();
        if let Some(role) = guard.as_ref() {
            Self::sync(role);
        }
    }

    /// Close and clean up the triplicated processes at the end of rad_protected execution
    #[stable(feature = "rad_protected", since = "1.95.0")]
    pub fn close() {
        let mut guard = ROLE.lock().unwrap();
        if let Some(role) = guard.as_ref() {
            if let Role::Parent(parent) = role {
                parent.kill_children();
            }
            Self::sync(role);
        }
        guard.take();
    }

    fn sync(role: &Role) {
        match role {
            Role::Parent(parent) => {
                parent.wait_for_children();
                parent.update_children();
            }
            Role::Child(child) => {
                child.update_parent();
                child.wait_for_parent();
            }
        
        }
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
