//! `hyprc`: the compiler driver executable.

#[global_allocator]
static GLOBAL: mimalloc::MiMalloc = mimalloc::MiMalloc;

fn main() {
    std::process::exit(hyprc::main_with_args(std::env::args_os()));
}
