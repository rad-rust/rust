//! Standard library for runtime additions required by rad_protected

use crate::thread;
use crate::sync::{Arc, Barrier};
use core::rad_protected::{Multithreading, vote};

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

        vote(
            i1.join().unwrap(), 
            i2.join().unwrap(),
            i3.join().unwrap()
        )
    }

    fn enter_critical_section(&self) -> bool {
        self.inner_data.arrival_barrier.wait().is_leader()
    }

    fn exit_critical_section(&self) {
        self.inner_data.departure_barrier.wait();
    }
}
