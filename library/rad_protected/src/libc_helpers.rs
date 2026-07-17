use super::mini_std::io;
use core::{ptr, sync::atomic::AtomicU32};
use libc;

pub(super) type Pid = libc::pid_t;

pub(super) unsafe fn fork() -> io::Result<libc::pid_t> {
    let pid = unsafe { libc::fork() };

    if pid == -1 {
        return Err(io::Error::last_os_error());
    }
    Ok(pid)
}

pub(super) fn kill(pid: libc::pid_t) -> io::Result<()> {
    if unsafe { libc::kill(pid, libc::SIGKILL) } == -1 {
        return Err(io::Error::last_os_error());
    }
    Ok(())
}

pub(super) fn waitpid(pid: libc::pid_t) -> io::Result<libc::pid_t> {
    let pid = unsafe { libc::waitpid(pid, ptr::null_mut(), 0) };

    if pid == -1 {
        return Err(io::Error::last_os_error());
    }
    Ok(pid)
}

pub(super) fn sysconf_sc_pagesize() -> io::Result<usize> {
    let page_size = unsafe { libc::sysconf(libc::_SC_PAGESIZE) };

    if page_size == -1 {
        return Err(io::Error::last_os_error());
    }
    Ok(page_size as usize)
}

pub(super) fn shared_mmap(size: usize) -> io::Result<*mut libc::c_void> {
    let ptr = unsafe {
        libc::mmap(
            ptr::null_mut(),
            size,
            libc::PROT_READ | libc::PROT_WRITE,
            libc::MAP_SHARED | libc::MAP_ANON,
            -1,
            0,
        )
    };

    if ptr == libc::MAP_FAILED {
        return Err(io::Error::last_os_error());
    }
    Ok(ptr)
}

pub(super) fn munmap(ptr: *mut libc::c_void, size: usize) {
    unsafe { libc::munmap(ptr, size); }
}

pub(super) fn futex_wait(addr: &AtomicU32, expected: u32) -> io::Result<()> {
    let addr = addr as *const _ as *const u32;

    let res = unsafe { 
        libc::syscall(
            libc::SYS_futex,
            addr,
            libc::FUTEX_WAIT,
            expected,
            ptr::null::<libc::timespec>(),
            ptr::null::<libc::c_void>(),
            0
        )
    };

    if res == -1 {
        return Err(io::Error::last_os_error());
    }
    Ok(())
}

pub(super) fn futex_wake_all(addr: &AtomicU32) -> io::Result<i32> {
    let addr = addr as *const _ as *const u32;
    
    let res = unsafe {
        libc::syscall(
            libc::SYS_futex,
            addr,
            libc::FUTEX_WAKE,
            libc::INT_MAX,
            ptr::null::<libc::timespec>(),
            ptr::null::<libc::c_void>(),
            0
        )
    } as i32;

    if res == -1 {
        return Err(io::Error::last_os_error());
    }
    Ok(res)
}
