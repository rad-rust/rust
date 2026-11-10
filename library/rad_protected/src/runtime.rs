use core::fmt::{self, Write};
use core::future::Future;
use core::pin::Pin;
use core::sync::atomic::{AtomicUsize, Ordering};
use core::task::{Context, Poll};

static WRITER: AtomicUsize = AtomicUsize::new(0);

#[stable(feature = "rad_protected", since = "1.95.0")]
pub fn set_writer(f: fn(&[u8])) {
    WRITER.store(f as usize, Ordering::Release);
}

#[stable(feature = "rad_protected", since = "1.95.0")]
pub fn clear_writer() {
    WRITER.store(0, Ordering::Release);
}

struct DeviceWriter;

impl Write for DeviceWriter {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        let writer = WRITER.load(Ordering::Acquire);
        if writer != 0 {
            let f: fn(&[u8]) = unsafe { core::mem::transmute::<usize, fn(&[u8])>(writer) };
            f(s.as_bytes());
        }
        Ok(())
    }
}

#[stable(feature = "rad_protected", since = "1.95.0")]
pub struct Runtime;

impl Runtime {
    #[stable(feature = "rad_protected", since = "1.95.0")]
    #[rustc_diagnostic_item = "checkpoint"]
    pub fn checkpoint(site: u32, regions: &[(*mut u8, usize, bool)]) {
        Self::print_checkpoint(site, regions, "checkpoint");
    }

    #[stable(feature = "rad_protected", since = "1.95.0")]
    #[rustc_diagnostic_item = "await_effects"]
    pub fn await_effects(site: u32, regions: &[(*mut u8, usize, bool)]) {
        Self::print_checkpoint(site, regions, "await effects");
    }

    fn print_checkpoint(site: u32, regions: &[(*mut u8, usize, bool)], kind: &str) {
        let mut w = DeviceWriter;
        let _ = writeln!(w, "{kind}: state {site}, {} regions", regions.len());

        for (i, &(ptr, len, compare)) in regions.iter().enumerate() {
            let _ = writeln!(
                w,
                "  region {i}: {len} bytes at {ptr:p} {}",
                if compare { "comparing" } else { "non-comparing" }
            );

            let _ = write!(w, "    bytes: ");
            if !ptr.is_null() && len != 0 {
                let bytes = unsafe { core::slice::from_raw_parts(ptr as *const u8, len) };
                for &b in bytes {
                    let _ = write!(w, "{b:02x} ");
                }
            }
            let _ = writeln!(w);
        }
    }
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
