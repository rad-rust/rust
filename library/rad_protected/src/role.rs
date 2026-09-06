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
    shared_mem_ctx: SharedMemoryContext,
    child1: ChildLink,
    child2: ChildLink,
}

impl Parent {
    pub(super) fn new(shared_memory: SharedMemory, child1: ChildLink, child2: ChildLink) -> Self {
        Self {
            shared_mem_ctx: SharedMemoryContext::new(shared_memory),
            child1,
            child2
        }
    }

    pub(super) fn kill_children(&self) {
        self.child1.kill_child();
        self.child2.kill_child();
    }

    pub(super) fn close_shared_mem(&self) {
        self.shared_mem_ctx.shared_memory.close();
    }
}

#[derive(Debug)]
pub struct Child {
    shared_mem_ctx: SharedMemoryContext,
}

impl Child {
    pub(super) fn new(shared_memory: SharedMemory) -> Self {
        Self {
            shared_mem_ctx: SharedMemoryContext::new(shared_memory), 
        }
    }
}

#[derive(Debug)]
pub(super) struct SharedMemoryContext {
    shared_memory: SharedMemory, 
    leader_depth: u32,
}

impl SharedMemoryContext {
    pub(super) fn new(shared_memory: SharedMemory) -> Self {
        Self { shared_memory, leader_depth: 0 }
    }

    pub(super) fn sync(&self) -> bool {
        self.shared_memory.sync()
    }

    pub(super) fn enter_critical_section(&mut self) -> bool {
        let leader = self.is_leader() || self.shared_memory.sync();

        if leader {
            self.leader_depth += 1;
        }

        leader
    }

    pub(super) fn exit_critical_section(&mut self) {
        if self.is_leader() {
            self.leader_depth -= 1;
        }

        if !self.is_leader() {
            self.shared_memory.sync();
        }
    }

    fn is_leader(&self) -> bool {
        self.leader_depth > 0
    }
}

impl Role {
    pub(super) fn ctx(&self) -> &SharedMemoryContext {
        match self {
            Role::Parent(parent) => &parent.shared_mem_ctx,
            Role::Child(child) => &child.shared_mem_ctx,
        }
    }
    pub(super) fn ctx_mut(&mut self) -> &mut SharedMemoryContext {
        match self {
            Role::Parent(parent) => &mut parent.shared_mem_ctx,
            Role::Child(child) => &mut child.shared_mem_ctx,
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
