use std::io::{self, Write};
use std::sync::Mutex;

use rustc_middle::ty::TyCtxt;

static LOGGER_STATE: Mutex<LoggerState> = Mutex::new(LoggerState {
    err_encountered: false
});

#[derive(Default)]
struct LoggerState {
    err_encountered: bool,
}

pub(crate) struct Logger;

impl Logger {
    const LOG_HEADER_MSG: &'static str = "\x1b[1;35mrad-protected\x1b[0m";

    pub(crate) fn info(msg: &str) {
        let mut stdout = io::stdout().lock();
        let _ = writeln!(stdout, "{} \x1b[1;34m[Info]\x1b[0m {}", Self::LOG_HEADER_MSG, msg);
    }

    pub(crate) fn warn(msg: &str) {
        let mut stderr = io::stderr().lock();
        let _ = writeln!(stderr, "{} \x1b[1;33m[Warning]\x1b[0m {}", Self::LOG_HEADER_MSG, msg);
    }

    pub(crate) fn error(msg: &str) {
        let mut stderr = io::stderr().lock();
        let _ = writeln!(stderr, "{} \x1b[1;31m[Error]\x1b[0m {}", Self::LOG_HEADER_MSG, msg);
        LOGGER_STATE.lock().unwrap().err_encountered = true;
    }

    pub(crate) fn report<'tcx>(tcx: TyCtxt<'tcx>) {
        if LOGGER_STATE.lock().unwrap().err_encountered {
            tcx.dcx().err("Failed to generate checkpoints");
        } else {
            Logger::info("Successfully generated checkpoints");
        }
    }
}
