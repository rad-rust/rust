use super::mini_std::sync::Mutex;
use super::libc_helpers::{kill, waitpid, Pid};
use super::shared_memory::SharedMemory;

pub(super) static ROLE: Mutex<Option<Role>> = Mutex::new(None);

#[derive(Debug)]
pub(super) enum Role {
    Parent(Parent),
    Child(Child),
}

#[derive(Debug)]
pub struct Parent {
    shared_memory: SharedMemory,
    child1: ChildLink,
    child2: ChildLink,
}

impl Parent {
    pub(super) fn new(shared_memory: SharedMemory, child1: ChildLink, child2: ChildLink) -> Self {
        Self { shared_memory, child1, child2 }
    }

    pub(super) fn kill_children(&self) {
        self.child1.kill_child();
        self.child2.kill_child();
    }

    pub(super) fn close_shared_mem(&self) {
        self.shared_memory.close();
    }
}

#[derive(Debug)]
pub struct Child {
    shared_memory: SharedMemory
}

impl Child {
    pub(super) fn new(shared_memory: SharedMemory) -> Self {
        Self { shared_memory }
    }
}

pub(super) trait Syncable {
    fn sync(&self) -> bool;
}

impl Syncable for Parent {
    fn sync(&self) -> bool {
        self.shared_memory.sync()
    }
}

impl Syncable for Child {
    fn sync(&self) -> bool {
        self.shared_memory.sync()
    }
}

impl Syncable for Role {
    fn sync(&self) -> bool {
        match self {
            Role::Parent(parent) => parent.sync(),
            Role::Child(child) => child.sync(),
        }
    }
}

#[derive(Debug)]
pub(super) struct ChildLink {
    pid: Pid,
}

impl ChildLink {
    pub(super) fn new(pid: Pid) -> Self {
        Self { pid }
    }

    pub(super) fn kill_child(&self) {
        let _ = kill(self.pid);
        let _ = waitpid(self.pid); 
    }
}
