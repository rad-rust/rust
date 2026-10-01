use super::mini_std::hal::multicore_launch_core1;
use super::role::ROLE;
/// Runtime for rad_protected
#[stable(feature = "rad_protected", since = "1.95.0")]
#[derive(Debug)]
pub struct Runtime;

impl Runtime {
    #[stable(feature = "initialize_runtime", since = "1.95.0")]
    pub fn initialize_runtime() {
        multicore_launch_core1();
        // TODO: All other initialization here (e.g. init PSRAM)
    }

    /// Enter a critical (unsafe) section of code, allowing only a single core through
    /// Syncs the cores. Returns `true` for the one leader (parent) core
    #[stable(feature = "rad_protected", since = "1.95.0")]
    pub fn enter_critical_section() -> bool {
        return ROLE.get_mut().enter_critical_section();
    }

    /// Exit a critical (unsafe) section of code
    /// Syncs the three cores
    #[stable(feature = "rad_protected", since = "1.95.0")]
    pub fn exit_critical_section() {
        return ROLE.get_mut().exit_critical_section();
    }

    /// Close and clean resources at the end of rad_protected execution
    #[stable(feature = "rad_protected", since = "1.95.0")]
    pub fn close() {
        // TODO: Do any other closing/cleaning operations here
        ROLE.get().sync();
    }

    // Checkpoint given locals via a majority vote over the cores
    #[stable(feature = "rad_protected", since = "1.95.0")]
    #[rustc_diagnostic_item = "checkpoint"]
    pub fn checkpoint(locals: &[(*mut u8, usize)]) {
        if locals.is_empty() {
            return;
        }

        ROLE.get_mut().checkpoint(locals);
    }

    // Internal checkpoint marker inserted during MIR building
    // Indicates the MIR pass should rewrite the terminator to a `checkpoint` call
    #[stable(feature = "rad_protected", since = "1.95.0")]
    #[rustc_diagnostic_item = "__checkpoint"]
    pub fn __checkpoint() {
    }
}

// TODO: Use this CoreGuard if calling close is necessary from all paths (right now Runtime::close() just syncs)
/*
/// Guard to properly close resources when done with the rad_protected execution
#[stable(feature = "rad_protected", since = "1.95.0")]
#[derive(Debug)]
pub struct CoreGuard;

/// Drop method for `CoreGuard`, close the child processes
#[stable(feature = "rad_protected", since = "1.95.0")]
impl Drop for CoreGuard {
    fn drop(&mut self) {
        Runtime::close();
    }
}
*/
