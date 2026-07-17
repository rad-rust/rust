use super::mini_std::{io, os::fd::OwnedFd};
use core::ptr;
use libc;

pub(super) type Pid = libc::pid_t;

pub(super) fn pipe() -> io::Result<(OwnedFd, OwnedFd)> {
    let mut fds: [libc::c_int; 2] = [0; 2];

    if unsafe { libc::pipe(fds.as_mut_ptr()) } == -1 {
        return Err(io::Error::last_os_error());
    }
    // fds[0] is the read end, fds[1] is the write end
    Ok(unsafe { (OwnedFd::from_raw_fd(fds[0]), OwnedFd::from_raw_fd(fds[1])) })
}

pub(super) fn close(fd: OwnedFd) -> io::Result<()> {
    if unsafe { libc::close(fd.into_raw_fd()) } == -1 {
        return Err(io::Error::last_os_error());
    }
    Ok(())
}

pub(super) unsafe fn fork() -> io::Result<libc::pid_t> {
    let pid = unsafe { libc::fork() };

    if pid == -1 {
        return Err(io::Error::last_os_error());
    }
    Ok(pid)
}


pub(super) fn read(fd: &OwnedFd, buf: &mut [u8]) -> io::Result<isize> {
    let n = unsafe { libc::read(fd.as_raw_fd(), buf.as_mut_ptr() as *mut libc::c_void, buf.len()) };

    if n < 0 {
        return Err(io::Error::last_os_error());
    }
    Ok(n as isize)
}

pub(super) fn write(fd: &OwnedFd, buf: &[u8]) -> io::Result<isize> {
    let n = unsafe { libc::write(fd.as_raw_fd(), buf.as_ptr() as *const libc::c_void, buf.len()) };
    
    if n < 0 {
        return Err(io::Error::last_os_error());
    }
    Ok(n as isize)
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
