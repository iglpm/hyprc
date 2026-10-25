use std::os::unix::thread::JoinHandleExt;
use std::thread;

thread_local! {
    static NUMBER: u32 = 7;
}

fn threads() {
    let current = thread::current().id();
    NUMBER.with(|number| assert_eq!(*number, 7));
    let handle = thread::Builder::new()
        .name("worker".to_string())
        .stack_size(256 * 1024)
        .spawn(move || (current, 42_u32))
        .unwrap();
    let _pthread = handle.as_pthread_t();
    let (_parent, answer) = handle.join().unwrap();
    assert_eq!(answer, 42);
    thread::yield_now();
}
