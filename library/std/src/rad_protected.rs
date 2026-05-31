//! Standard library for runtime additions required by rad_protected

use core::mem;

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
