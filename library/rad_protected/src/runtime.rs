use core::future::Future;
use core::pin::Pin;
use core::task::{Context, Poll};

#[stable(feature = "rad_protected", since = "1.95.0")]
pub struct Runtime;

impl Runtime {
    #[stable(feature = "rad_protected", since = "1.95.0")]
    #[rustc_diagnostic_item = "checkpoint"]
    // TODO: implement Runtime::checkpoint
    pub fn checkpoint(_site: u32, _regions: &[(*mut u8, usize)]) {
        todo!();
    }
}

#[stable(feature = "rad_protected", since = "1.95.0")]
pub fn checkpoint() -> impl Future<Output = ()> {
    Yield::new()
}

#[stable(feature = "rad_protected", since = "1.95.0")]
struct Yield {
    ready: bool
}

impl Yield {
    fn new() -> Self {
        Self { ready: false }
    }
}

impl Future for Yield {
    type Output = ();

    fn poll(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<()> {
        if self.ready {
            return Poll::Ready(());
        }
        self.ready = true;
        cx.waker().wake_by_ref();
        Poll::Pending
    }
}
