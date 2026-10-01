// Targets the Cortex-M33 processor (Armv8-M Mainline),
// e.g. Raspberry Pi Pico 2 (RP2350)

use crate::spec::{
    Abi, Arch, FloatAbi, Os, PanicStrategy, Target, TargetMetadata, TargetOptions, base,
};

pub(crate) fn target() -> Target {
    Target {
        llvm_target: "thumbv8m.main-rad-none-eabi".into(),
        metadata: TargetMetadata {
            description: Some("Dual-core Arm Cortex-M33 (Raspberry Pi Pico 2)".into()),
            tier: None,
            host_tools: Some(false),
            std: Some(false),
        },
        pointer_width: 32,
        data_layout: "e-m:e-p:32:32-Fi8-i64:64-v128:64:128-a:0:32-n32-S64".into(),
        arch: Arch::Arm,

        options: TargetOptions {
            os: Os::None,
            abi: Abi::Eabi,
            llvm_floatabi: Some(FloatAbi::Soft),
            max_atomic_width: Some(32),
            panic_strategy: PanicStrategy::Abort,
            ..base::arm_none::opts()
        },
    }
}
