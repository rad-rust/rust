//! Standard library for runtime additions required by rad_protected

use core::mem;
use crate::thread;
use crate::sync::{Arc, Barrier};

fn bitwise_majority_vote(a: u8, b: u8, c: u8) -> u8 {
    (a & b) | (b & c) | (a & c)
}

/// Perform bitwise majority vote of the triplicated call results for rad_protected
#[stable(feature = "rad_protected", since = "1.95.0")]
pub fn vote<T: Sized>(a: T, b: T, c: T) -> T {
    let size = mem::size_of::<T>();

    unsafe {
        let a_ptr = &a as *const T as *mut u8;
        let b_ptr = &b as *const T as *const u8;
        let c_ptr = &c as *const T as *const u8;

        for i in 0..size {
            let a_byte = a_ptr.add(i);
            let b_byte = b_ptr.add(i);
            let c_byte = c_ptr.add(i);

            *a_byte = bitwise_majority_vote(*a_byte, *b_byte, *c_byte);
        }
    }

    a
}


/// Contains the logic for rad_protected multithreading
/// All valid rad_protected `Multithreading` types must implement this trait
#[stable(feature = "rad_protected", since = "1.95.0")]
pub trait Multithreading {

    /// Run the triplicated functions on new threads
    #[stable(feature = "rad_protected", since = "1.95.0")]
    fn run_triple<T, F1, F2, F3>(f1: F1, f2: F2, f3: F3) -> T
        where
            F1: FnOnce() -> T + Send + 'static,
            F2: FnOnce() -> T + Send + 'static,
            F3: FnOnce() -> T + Send + 'static,
            T: Send + 'static;

    /// Synchronizes the threads at the start of the critical section
    /// Returns `true` for the leader thread, and `false` for the non-leaders
    /// The non-leaders continue, waiting at `exit_critical_section`
    #[stable(feature = "rad_protected", since = "1.95.0")]
    fn enter_critical_section(&self) -> bool;

    /// Non-leader threads wait here for the leader to complete the critical section
    #[stable(feature = "rad_protected", since = "1.95.0")]
    fn exit_critical_section(&self);
}

/// An implementation of rad_protected `Multithreading` using the Rust std library
#[stable(feature = "rad_protected", since = "1.95.0")]
#[derive(Clone, Debug)]
pub struct StdMultithreading {
    inner_data: Arc<StdMultithreadingInnerData>
}

#[derive(Debug)]
struct StdMultithreadingInnerData {
    arrival_barrier: Barrier,
    departure_barrier: Barrier,
}

#[stable(feature = "rad_protected", since = "1.95.0")]
impl StdMultithreading {

    /// Create a new instance of `StdMultithreading`
    #[stable(feature = "rad_protected", since = "1.95.0")]
    pub fn new(num_threads: usize) -> Self {
        Self {
            inner_data: Arc::new(StdMultithreadingInnerData {
                arrival_barrier: Barrier::new(num_threads),
                departure_barrier: Barrier::new(num_threads),
            })
        }
    }
}

#[stable(feature = "rad_protected", since = "1.95.0")]
impl Multithreading for StdMultithreading {

    fn run_triple<T, F1, F2, F3>(f1: F1, f2: F2, f3: F3) -> T
        where
            F1: FnOnce() -> T + Send + 'static,
            F2: FnOnce() -> T + Send + 'static,
            F3: FnOnce() -> T + Send + 'static,
            T: Send + 'static,
    {
        let i1 = thread::spawn(f1);
        let i2 = thread::spawn(f2);
        let i3 = thread::spawn(f3);

        i1.join().unwrap();
        i2.join().unwrap();
        i3.join().unwrap()
    }

    fn enter_critical_section(&self) -> bool {
        self.inner_data.arrival_barrier.wait().is_leader()
    }

    fn exit_critical_section(&self) {
        self.inner_data.departure_barrier.wait();
    }
}
