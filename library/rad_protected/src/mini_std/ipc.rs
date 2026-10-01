use super::hal::core_id;
use core::cell::UnsafeCell;

pub struct CoreLocal<T>([UnsafeCell<T>; 2]);

unsafe impl<T> Sync for CoreLocal<T> {}

impl<T> CoreLocal<T> {
    pub const fn new(core0: T, core1: T) -> Self {
        Self([UnsafeCell::new(core0), UnsafeCell::new(core1)])
    }

    pub fn get(&self) -> &T {
        unsafe {
            &*self.0[core_id() as usize].get()
        }
    }
    
    pub fn get_mut(&self) -> &mut T {
        unsafe {
            &mut *self.0[core_id() as usize].get()
        }
    }
}
