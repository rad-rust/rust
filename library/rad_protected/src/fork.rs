use super::mini_std::{fs::File, io::BufReader};
use core::ptr;
use super::libc_helpers::{fork, sysconf_sc_pagesize};
use super::role::ChildLink;

pub(super) fn fork_copy() -> Option<ForkOutcome> {

    match unsafe { fork() }.ok()? {
        0 => {
            force_copy_pages();
            Some(ForkOutcome::Child)
        },
        child_pid => {
            Some(ForkOutcome::Parent(ChildLink::new(child_pid)))
        },
    }
}

pub(super) enum ForkOutcome {
    Parent(ChildLink),
    Child,
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
