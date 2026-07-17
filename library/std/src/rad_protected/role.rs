use super::mini_std::{os::fd::OwnedFd, sync::Mutex};
use super::libc_helpers::{write, read, kill, waitpid, Pid};

pub(super) static ROLE: Mutex<Option<Role>> = Mutex::new(None);

#[derive(Debug)]
pub(super) enum Role {
    Parent(Parent),
    Child(Child),
}

impl Role {
    pub(super) fn is_parent(&self) -> bool {
        matches!(self, Role::Parent(_))
    }
}

#[derive(Debug)]
pub struct Parent {
    child1: ChildLink,
    child2: ChildLink,
}

impl Parent {
    pub(super) fn new(child1: ChildLink, child2: ChildLink) -> Self {
        Self { child1, child2 }
    }

    pub(super) fn wait_for_children(&self) {
        self.child1.pipe.wait_for_update();
        self.child2.pipe.wait_for_update();
    }
    pub(super) fn update_children(&self) {
        self.child1.pipe.send_update();
        self.child2.pipe.send_update();
    }
    pub(super) fn kill_children(&self) {
        self.child1.kill_child();
        self.child2.kill_child();
    }
}

#[derive(Debug)]
pub struct Child {
    pipe: SyncPipe,
}

impl Child {
    pub(super) fn new(pipe: SyncPipe) -> Self {
        Self { pipe }
    }
    
    pub(super) fn update_parent(&self) {
        self.pipe.send_update();
    }
    pub(super) fn wait_for_parent(&self) {
        self.pipe.wait_for_update();
    }
}

#[derive(Debug)]
pub(super) struct SyncPipe {
    from_peer: OwnedFd,
    to_peer: OwnedFd,
}

impl SyncPipe {
    pub(super) fn new(from_peer: OwnedFd, to_peer: OwnedFd) -> Self {
        Self { from_peer, to_peer }
    }

    pub(super) fn wait_for_update(&self) {
        let mut buf = [0u8; 1];
        let _ = read(&self.from_peer, &mut buf);
    }
    pub(super) fn send_update(&self) {
        let _ = write(&self.to_peer, &[0u8]);
    }
}

#[derive(Debug)]
pub(super) struct ChildLink {
    pid: Pid,
    pipe: SyncPipe,
}

impl ChildLink {
    pub(super) fn new(pid: Pid, pipe: SyncPipe) -> Self {
        Self { pid, pipe }
    }

    pub(super) fn kill_child(&self) {
        let _ = kill(self.pid);
        let _ = waitpid(self.pid); 
    }
}
