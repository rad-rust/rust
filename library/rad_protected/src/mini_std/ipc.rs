use core::sync::atomic::{AtomicU32, Ordering};
use super::super::libc_helpers::{futex_wait, futex_wake_all};

pub struct Barrier {
    threshold: u32,
    count: AtomicU32,
    _gen: AtomicU32,
}

impl Barrier {
    pub fn new(threshold: u32) -> Self {
        Self {
            threshold,
            count: AtomicU32::new(0),
            _gen: AtomicU32::new(0)
        }
    }

    pub fn wait(&self) -> BarrierWaitResult {
        let _gen = self._gen.load(Ordering::Acquire);
        let arrived = self.count.fetch_add(1, Ordering::AcqRel) + 1;
        
        if arrived == self.threshold {
            self.count.store(0, Ordering::Relaxed);
            self._gen.fetch_add(1, Ordering::Release);

            let _ = futex_wake_all(&self._gen);

            return BarrierWaitResult(true);
        }

        loop {
            if self._gen.load(Ordering::Acquire) != _gen {
                break;
            }

            let res = futex_wait(&self._gen, _gen);

            if let Err(err) = res {
                let err = err.raw_os_error().unwrap();

                match err {
                    libc::EAGAIN | libc::EINTR => continue,
                    _ => panic!("Failed to acquire futex"),
                }
            }
        }
        
        BarrierWaitResult(false)
    }
}

pub struct BarrierWaitResult(bool);

impl BarrierWaitResult {
    pub fn is_leader(&self) -> bool {
        self.0
    }
}
