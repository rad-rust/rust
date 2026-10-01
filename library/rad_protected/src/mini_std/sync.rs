// TODO: If the target architecture supports multithreading, implement the Mutex below (otherwise remove)

use core::{cell::UnsafeCell, ops::{Deref, DerefMut}};

pub struct Mutex<T> {
    data: UnsafeCell<T>,
}

pub struct MutexGuard<'a, T> {
    mutex: &'a Mutex<T>,
}

unsafe impl<T: Send> Send for Mutex<T> {}
unsafe impl<T: Send> Sync for Mutex<T> {}

type LockResult<T> = Result<T, i32>;

impl<T> Mutex<T> {
    pub const fn new(data: T) -> Self {
        Self {
            data: UnsafeCell::new(data),
        }
    }

    pub fn lock(&self) -> LockResult<MutexGuard<'_, T>> {
        Ok(MutexGuard { mutex: self })
    }
}

impl<T> Deref for MutexGuard<'_, T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        unsafe { &*self.mutex.data.get() }
    }
}

impl<T> DerefMut for MutexGuard<'_, T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        unsafe { &mut *self.mutex.data.get() }
    }
}

impl<T> Drop for MutexGuard<'_, T> {
    fn drop(&mut self) { 

    }
}

impl<T> Drop for Mutex<T> {
    fn drop(&mut self) {
        
    }
}
