use super::mini_std::{fs::File, io::BufReader};
use core::ptr;
use super::libc_helpers::{pipe, close, fork, sysconf_sc_pagesize};
use super::role::{Child, ChildLink, SyncPipe};

pub(super) fn fork_copy() -> Option<ForkOutcome> {
    // Parent -> child
    let (p2c_read, p2c_write) = pipe().ok()?;
    // Child -> parent
    let (c2p_read, c2p_write) = pipe().ok()?;

    match unsafe { fork() }.ok()? {
        0 => {
            
            close(p2c_write).ok()?;
            close(c2p_read).ok()?;
            
            force_copy_pages();

            Some(ForkOutcome::Child(Child::new(
                SyncPipe::new(p2c_read, c2p_write)
            )))
        },
        child_pid => {
            
            close(p2c_read).ok()?;
            close(c2p_write).ok()?;

            Some(ForkOutcome::Parent(ChildLink::new(
                child_pid,
                SyncPipe::new(c2p_read, p2c_write)
            )))
        },
    }
}

pub(super) enum ForkOutcome {
    Parent(ChildLink),
    Child(Child),
}

fn force_copy_pages() {
    let page_size = sysconf_sc_pagesize().unwrap();

    let file = File::open("/proc/self/maps").unwrap();
    let reader = BufReader::new(file);

    for line in reader.lines().map_while(Result::ok) {
        let mut parts = line.split_whitespace();

        let (Some(range), Some(perms)) = (parts.next(), parts.next()) else {
            continue;
        };

        if !matches!(perms.as_bytes(), [_, b'w', _, b'p', ..]) {
            continue;
        }

        if line.contains("[vsyscall]")
            || line.contains("[vvar]")
            || line.contains("[vdso]")
        {
            continue;
        }

        let Some((start, end)) = range.split_once('-') else {
            continue;
        };

        let (Ok(start), Ok(end)) = (
            usize::from_str_radix(start, 16),
            usize::from_str_radix(end, 16),
        ) else {
            continue;
        };

        unsafe {
            let mut addr = start;

            while addr < end {
                let p = ptr::without_provenance_mut::<u8>(addr);

                // Force a write so the kernel faults in a private copy of the COW page.
                let v = ptr::read_volatile(p);
                ptr::write_volatile(p, v);

                addr += page_size;
            }
        }
    }
}
