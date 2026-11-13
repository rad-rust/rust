use core::future::Future;
use core::pin::Pin;
use core::task::{Context, Poll};

use crate::hal;
use crate::checkpoint::{self, Regions};

#[stable(feature = "rad_protected", since = "1.95.0")]
pub struct Runtime;

impl Runtime {
    #[stable(feature = "rad_protected", since = "1.95.0")]
    #[rustc_diagnostic_item = "checkpoint"]
    pub fn checkpoint(site: u32, regions: Regions<'_>) -> bool {
        checkpoint::checkpoint(site, regions)
    }

    #[stable(feature = "rad_protected", since = "1.95.0")]
    #[rustc_diagnostic_item = "await_effects"]
    pub fn await_effects(site: u32, regions: Regions<'_>) {
        checkpoint::snapshot(site, regions);
    }

    #[stable(feature = "rad_protected", since = "1.95.0")]
    #[rustc_diagnostic_item = "restore"]
    pub fn restore() {
        checkpoint::restore();
    }
    
    #[stable(feature = "rad_protected", since = "1.95.0")]
    pub fn sync() {
        checkpoint::sync();
    }
}

#[stable(feature = "rad_protected", since = "1.95.0")]
pub fn init_runtime(write: fn(&[u8]), core_num: fn()->u32, fifo_push_blocking: fn(u32), fifo_pop_blocking: fn()->u32) {
    hal::init_hal(write, core_num, fifo_push_blocking, fifo_pop_blocking);
}

#[stable(feature = "rad_protected", since = "1.95.0")]
pub fn checkpoint() -> impl Future<Output = ()> {
    Yield::new()
}

#[stable(feature = "rad_protected", since = "1.95.0")]
struct Yield {
    ready: u32
}

impl Yield {
    fn new() -> Self {
        Self { ready: 25 }
    }
}

impl Future for Yield {
    type Output = ();

    fn poll(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<()> {
        if self.ready == 0 {
            return Poll::Ready(());
        }
        self.ready -= 1;
        cx.waker().wake_by_ref();
        Poll::Pending
    }
}
