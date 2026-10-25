#![no_std]

extern crate std;

use std::sync::{Condvar, Mutex, Once, RwLock, TryLockError};
use std::time::Duration;

fn synchronization_surface() {
    let mutex = Mutex::new(1_u32);
    *mutex.lock().unwrap() += 1;
    match mutex.try_lock() {
        Ok(value) => assert_eq!(*value, 2),
        Err(TryLockError::WouldBlock) => {}
        Err(TryLockError::Poisoned(error)) => drop(error.into_inner()),
    }

    let condvar = Condvar::new();
    let guard = mutex.lock().unwrap();
    let (_guard, timeout) = condvar
        .wait_timeout(guard, Duration::from_nanos(0))
        .unwrap();
    assert!(timeout.timed_out());
    condvar.notify_one();
    condvar.notify_all();

    let lock = RwLock::new(1_u32);
    assert_eq!(*lock.read().unwrap(), 1);
    *lock.write().unwrap() = 2;
    assert_eq!(lock.into_inner().unwrap(), 2);

    let once = Once::new();
    once.call_once(|| {});
    assert!(once.is_completed());
}
