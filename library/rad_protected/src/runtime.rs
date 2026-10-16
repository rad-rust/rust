/// Runtime for rad_protected
#[stable(feature = "rad_protected", since = "1.95.0")]
#[derive(Debug)]
pub struct Runtime;

impl Runtime {
    // Checkpoint given locals via a majority vote over the cores
    #[stable(feature = "rad_protected", since = "1.95.0")]
    #[rustc_diagnostic_item = "checkpoint"]
    pub fn checkpoint(_n: u32) {
        todo!();
    }
}
