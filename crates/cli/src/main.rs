//! Architectural dependency smoke test: application code depends inward on the kernel.
//! This is not the beginning of a source parser.

fn main() {
    println!("gimbal kernel {}", gimbal_kernel::kernel_version());
}
