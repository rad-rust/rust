use libc;
use core::{cell::UnsafeCell, ops::{Deref, DerefMut}};

pub struct Mutex<T> {
    lock: libc::pthread_mutex_t,
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
            lock: libc::PTHREAD_MUTEX_INITIALIZER,
            data: UnsafeCell::new(data),
        }
    }

    pub fn lock(&self) -> LockResult<MutexGuard<'_, T>> {
        let res = unsafe { libc::pthread_mutex_lock(&self.lock as *const _ as *mut _) };

        if res != 0 {
            return Err(res);
        }
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
        unsafe { libc::pthread_mutex_unlock(&self.mutex.lock as *const _ as *mut _); }
    }
}

impl<T> Drop for Mutex<T> {
    fn drop(&mut self) {
        unsafe {
            libc::pthread_mutex_destroy(&mut self.lock);
        }
    }
}
