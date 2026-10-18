use core::future::Future;
use core::pin::Pin;
use core::task::{Context, Poll};
use libc;

#[stable(feature = "rad_protected", since = "1.95.0")]
pub struct Runtime;

impl Runtime {
    #[stable(feature = "rad_protected", since = "1.95.0")]
    #[rustc_diagnostic_item = "checkpoint"]
    pub fn checkpoint(site: u32, regions: &[(*mut u8, usize)]) {
        unsafe {
            libc::printf(
                c"checkpoint: state %u, %zu regions\n".as_ptr(),
                site as libc::c_uint,
                regions.len() as libc::size_t,
            );

            for (i, &(ptr, len)) in regions.iter().enumerate() {
                libc::printf(
                    c"  region %zu: %zu bytes at %p\n".as_ptr(),
                    i as libc::size_t,
                    len as libc::size_t,
                    ptr,
                );

                let bytes = core::slice::from_raw_parts(ptr, len);
                libc::printf(c"    bytes: ".as_ptr());

                for &byte in bytes {
                    libc::printf(c"%02x ".as_ptr(), byte as libc::c_uint);
                }

                libc::printf(c"\n".as_ptr());
            }
        }
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
