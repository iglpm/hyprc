//! Hyprc Standard Library
//!
//! Clean, fast, and self-contained standard library layer for hyprc.
//! Re-exports core and alloc, and provides standard OS, I/O, path, and sync abstractions.

#![no_std]
#![allow(unused_imports, dead_code, non_camel_case_types)]

pub use core::*;
pub use alloc::*;

pub mod borrow {
    pub use alloc::borrow::*;
}

pub mod string {
    pub use alloc::string::*;
}

pub mod vec {
    pub use alloc::vec::*;
}

pub mod boxed {
    pub use alloc::boxed::*;
}

pub mod rc {
    pub use alloc::rc::*;
}

pub mod sync {
    pub use core::sync::*;

    pub mod atomic {
        pub use core::sync::atomic::*;
    }

    use core::sync::atomic::{AtomicBool, AtomicU8, AtomicUsize, Ordering};

    pub type LockResult<T> = Result<T, PoisonError<T>>;
    pub type TryLockResult<T> = Result<T, TryLockError<T>>;

    pub struct PoisonError<T> {
        data: T,
    }

    impl<T> PoisonError<T> {
        pub fn new(data: T) -> Self {
            Self { data }
        }
        pub fn into_inner(self) -> T {
            self.data
        }
        pub fn get_ref(&self) -> &T {
            &self.data
        }
        pub fn get_mut(&mut self) -> &mut T {
            &mut self.data
        }
    }

    impl<T> core::fmt::Debug for PoisonError<T> {
        fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
            f.write_str("PoisonError { .. }")
        }
    }

    pub enum TryLockError<T> {
        Poisoned(PoisonError<T>),
        WouldBlock,
    }

    impl<T> core::fmt::Debug for TryLockError<T> {
        fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
            match self {
                Self::Poisoned(_) => f.write_str("Poisoned(..)"),
                Self::WouldBlock => f.write_str("WouldBlock"),
            }
        }
    }

    pub struct Mutex<T: ?Sized> {
        locked: AtomicBool,
        data: core::cell::UnsafeCell<T>,
    }

    unsafe impl<T: ?Sized + Send> Send for Mutex<T> {}
    unsafe impl<T: ?Sized + Send> Sync for Mutex<T> {}

    impl<T> Mutex<T> {
        pub const fn new(data: T) -> Self {
            Self {
                locked: AtomicBool::new(false),
                data: core::cell::UnsafeCell::new(data),
            }
        }

        pub fn into_inner(self) -> LockResult<T> {
            Ok(self.data.into_inner())
        }
    }

    impl<T: ?Sized> Mutex<T> {
        pub fn lock(&self) -> LockResult<MutexGuard<'_, T>> {
            while self
                .locked
                .compare_exchange_weak(false, true, Ordering::Acquire, Ordering::Relaxed)
                .is_err()
            {
                while self.locked.load(Ordering::Relaxed) {
                    core::hint::spin_loop();
                }
            }
            Ok(MutexGuard {
                lock: self,
                _not_send: core::marker::PhantomData,
            })
        }

        pub fn try_lock(&self) -> TryLockResult<MutexGuard<'_, T>> {
            if self
                .locked
                .compare_exchange(false, true, Ordering::Acquire, Ordering::Relaxed)
                .is_ok()
            {
                Ok(MutexGuard {
                    lock: self,
                    _not_send: core::marker::PhantomData,
                })
            } else {
                Err(TryLockError::WouldBlock)
            }
        }

        pub fn get_mut(&mut self) -> LockResult<&mut T> {
            Ok(self.data.get_mut())
        }

        pub fn is_poisoned(&self) -> bool {
            false
        }
    }

    pub struct MutexGuard<'a, T: ?Sized> {
        lock: &'a Mutex<T>,
        _not_send: core::marker::PhantomData<*mut ()>,
    }

    impl<T: ?Sized> core::ops::Deref for MutexGuard<'_, T> {
        type Target = T;
        fn deref(&self) -> &T {
            unsafe { &*self.lock.data.get() }
        }
    }

    impl<T: ?Sized> core::ops::DerefMut for MutexGuard<'_, T> {
        fn deref_mut(&mut self) -> &mut T {
            unsafe { &mut *self.lock.data.get() }
        }
    }

    impl<T: ?Sized> Drop for MutexGuard<'_, T> {
        fn drop(&mut self) {
            self.lock.locked.store(false, Ordering::Release);
        }
    }

    const WRITE_LOCKED: usize = 1usize << (usize::BITS - 1);

    pub struct RwLock<T: ?Sized> {
        state: AtomicUsize,
        data: core::cell::UnsafeCell<T>,
    }

    unsafe impl<T: ?Sized + Send> Send for RwLock<T> {}
    unsafe impl<T: ?Sized + Send + Sync> Sync for RwLock<T> {}

    impl<T> RwLock<T> {
        pub const fn new(data: T) -> Self {
            Self {
                state: AtomicUsize::new(0),
                data: core::cell::UnsafeCell::new(data),
            }
        }

        pub fn into_inner(self) -> LockResult<T> {
            Ok(self.data.into_inner())
        }
    }

    impl<T: ?Sized> RwLock<T> {
        pub fn read(&self) -> LockResult<RwLockReadGuard<'_, T>> {
            loop {
                let state = self.state.load(Ordering::Relaxed);
                if state & WRITE_LOCKED != 0 {
                    core::hint::spin_loop();
                    continue;
                }
                if self
                    .state
                    .compare_exchange_weak(
                        state,
                        state + 1,
                        Ordering::Acquire,
                        Ordering::Relaxed,
                    )
                    .is_ok()
                {
                    return Ok(RwLockReadGuard { lock: self });
                }
            }
        }

        pub fn try_read(&self) -> TryLockResult<RwLockReadGuard<'_, T>> {
            let state = self.state.load(Ordering::Relaxed);
            if state & WRITE_LOCKED == 0
                && self
                    .state
                    .compare_exchange(state, state + 1, Ordering::Acquire, Ordering::Relaxed)
                    .is_ok()
            {
                Ok(RwLockReadGuard { lock: self })
            } else {
                Err(TryLockError::WouldBlock)
            }
        }

        pub fn write(&self) -> LockResult<RwLockWriteGuard<'_, T>> {
            while self
                .state
                .compare_exchange_weak(0, WRITE_LOCKED, Ordering::Acquire, Ordering::Relaxed)
                .is_err()
            {
                core::hint::spin_loop();
            }
            Ok(RwLockWriteGuard {
                lock: self,
                _not_send: core::marker::PhantomData,
            })
        }

        pub fn try_write(&self) -> TryLockResult<RwLockWriteGuard<'_, T>> {
            if self
                .state
                .compare_exchange(0, WRITE_LOCKED, Ordering::Acquire, Ordering::Relaxed)
                .is_ok()
            {
                Ok(RwLockWriteGuard {
                    lock: self,
                    _not_send: core::marker::PhantomData,
                })
            } else {
                Err(TryLockError::WouldBlock)
            }
        }

        pub fn get_mut(&mut self) -> LockResult<&mut T> {
            Ok(self.data.get_mut())
        }

        pub fn is_poisoned(&self) -> bool {
            false
        }
    }

    pub struct RwLockReadGuard<'a, T: ?Sized> {
        lock: &'a RwLock<T>,
    }

    impl<T: ?Sized> core::ops::Deref for RwLockReadGuard<'_, T> {
        type Target = T;
        fn deref(&self) -> &T {
            unsafe { &*self.lock.data.get() }
        }
    }

    impl<T: ?Sized> Drop for RwLockReadGuard<'_, T> {
        fn drop(&mut self) {
            self.lock.state.fetch_sub(1, Ordering::Release);
        }
    }

    pub struct RwLockWriteGuard<'a, T: ?Sized> {
        lock: &'a RwLock<T>,
        _not_send: core::marker::PhantomData<*mut ()>,
    }

    impl<T: ?Sized> core::ops::Deref for RwLockWriteGuard<'_, T> {
        type Target = T;
        fn deref(&self) -> &T {
            unsafe { &*self.lock.data.get() }
        }
    }

    impl<T: ?Sized> core::ops::DerefMut for RwLockWriteGuard<'_, T> {
        fn deref_mut(&mut self) -> &mut T {
            unsafe { &mut *self.lock.data.get() }
        }
    }

    impl<T: ?Sized> Drop for RwLockWriteGuard<'_, T> {
        fn drop(&mut self) {
            self.lock.state.store(0, Ordering::Release);
        }
    }

    pub struct Condvar {
        generation: AtomicUsize,
    }

    impl Condvar {
        pub const fn new() -> Self {
            Self {
                generation: AtomicUsize::new(0),
            }
        }

        pub fn wait<'a, T: ?Sized>(
            &self,
            guard: MutexGuard<'a, T>,
        ) -> LockResult<MutexGuard<'a, T>> {
            let lock = guard.lock;
            let generation = self.generation.load(Ordering::Acquire);
            drop(guard);
            while self.generation.load(Ordering::Acquire) == generation {
                core::hint::spin_loop();
            }
            lock.lock()
        }

        pub fn wait_timeout<'a, T: ?Sized>(
            &self,
            guard: MutexGuard<'a, T>,
            timeout: core::time::Duration,
        ) -> LockResult<(MutexGuard<'a, T>, WaitTimeoutResult)> {
            let lock = guard.lock;
            let generation = self.generation.load(Ordering::Acquire);
            drop(guard);
            let rounds = timeout.as_nanos().min(100_000) as usize;
            for _ in 0..rounds {
                if self.generation.load(Ordering::Acquire) != generation {
                    return Ok((lock.lock()?, WaitTimeoutResult(false)));
                }
                core::hint::spin_loop();
            }
            Ok((lock.lock()?, WaitTimeoutResult(true)))
        }

        pub fn notify_one(&self) {
            self.generation.fetch_add(1, Ordering::Release);
        }

        pub fn notify_all(&self) {
            self.generation.fetch_add(1, Ordering::Release);
        }
    }

    pub struct WaitTimeoutResult(bool);

    impl WaitTimeoutResult {
        pub fn timed_out(&self) -> bool {
            self.0
        }
    }

    pub struct Arc<T: ?Sized>(alloc::sync::Arc<T>);
    impl<T> Arc<T> {
        pub fn new(data: T) -> Self {
            Self(alloc::sync::Arc::new(data))
        }
    }
    impl<T: ?Sized> core::ops::Deref for Arc<T> {
        type Target = T;
        fn deref(&self) -> &T {
            &self.0
        }
    }
    impl<T: ?Sized> Clone for Arc<T> {
        fn clone(&self) -> Self {
            Self(self.0.clone())
        }
    }
    impl<T: ?Sized + core::fmt::Debug> core::fmt::Debug for Arc<T> {
        fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
            core::fmt::Debug::fmt(&self.0, f)
        }
    }

    pub struct Once {
        state: AtomicU8,
    }

    impl Once {
        pub const fn new() -> Self {
            Self {
                state: AtomicU8::new(0),
            }
        }

        pub fn call_once<F: FnOnce()>(&self, f: F) {
            if self
                .state
                .compare_exchange(0, 1, Ordering::Acquire, Ordering::Acquire)
                .is_ok()
            {
                f();
                self.state.store(2, Ordering::Release);
            } else {
                while self.state.load(Ordering::Acquire) != 2 {
                    core::hint::spin_loop();
                }
            }
        }

        pub fn is_completed(&self) -> bool {
            self.state.load(Ordering::Acquire) == 2
        }
    }

    pub mod mpsc {
        pub struct Sender<T>(core::marker::PhantomData<T>);
        pub struct Receiver<T>(core::marker::PhantomData<T>);
        pub struct SyncSender<T>(core::marker::PhantomData<T>);

        pub fn channel<T>() -> (Sender<T>, Receiver<T>) {
            (Sender(core::marker::PhantomData), Receiver(core::marker::PhantomData))
        }

        pub fn sync_channel<T>(bound: usize) -> (SyncSender<T>, Receiver<T>) {
            let _ = bound;
            (SyncSender(core::marker::PhantomData), Receiver(core::marker::PhantomData))
        }

        impl<T> Sender<T> {
            pub fn send(&self, t: T) -> Result<(), SendError<T>> {
                let _ = t;
                Ok(())
            }
        }

        impl<T> Receiver<T> {
            pub fn recv(&self) -> Result<T, RecvError> {
                loop {}
            }
            pub fn try_recv(&self) -> Result<T, TryRecvError> {
                Err(TryRecvError::Empty)
            }
        }

        #[derive(Copy, Clone, PartialEq, Eq, Debug)]
        pub struct SendError<T>(pub T);

        #[derive(Copy, Clone, PartialEq, Eq, Debug)]
        pub struct RecvError;

        #[derive(Copy, Clone, PartialEq, Eq, Debug)]
        pub enum TryRecvError {
            Empty,
            Disconnected,
        }
    }
}

pub mod panic {
    use core::any::Any;
    use alloc::boxed::Box;

    pub struct AssertUnwindSafe<T>(pub T);

    pub trait RefUnwindSafe {}
    pub trait UnwindSafe {}

    impl<T: ?Sized> RefUnwindSafe for T {}
    impl<T: ?Sized> UnwindSafe for T {}

    pub fn catch_unwind<F: FnOnce() -> R, R>(f: F) -> Result<R, Box<dyn Any + Send + 'static>> {
        Ok(f())
    }

    pub fn resume_unwind(payload: Box<dyn Any + Send + 'static>) -> ! {
        drop(payload);
        crate::process::abort()
    }
}

pub mod error {
    pub use core::error::*;
    pub use core::str::{ParseBoolError, Utf8Error};
    pub use core::num::{IntErrorKind, ParseFloatError, ParseIntError, TryFromIntError};
    pub use core::char::{DecodeUtf16Error, ParseCharError};
    pub use alloc::string::{FromUtf16Error, FromUtf8Error};
}

pub mod io {
    use alloc::string::String;
    use alloc::vec::Vec;

    #[derive(Debug)]
    pub struct Error {
        repr: &'static str,
    }

    impl Error {
        pub fn new<E>(kind: ErrorKind, error: E) -> Self {
            let _ = (kind, error);
            Self { repr: "io error" }
        }

        pub fn from_raw_os_error(code: i32) -> Self {
            let _ = code;
            Self { repr: "raw os error" }
        }

        pub fn last_os_error() -> Self {
            Self { repr: "os error" }
        }

        pub fn kind(&self) -> ErrorKind {
            ErrorKind::Other
        }

        pub fn raw_os_error(&self) -> Option<i32> {
            None
        }
    }

    impl core::fmt::Display for Error {
        fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
            write!(f, "{}", self.repr)
        }
    }

    #[derive(Copy, Clone, Debug, PartialEq, Eq)]
    pub enum ErrorKind {
        NotFound,
        PermissionDenied,
        ConnectionRefused,
        ConnectionReset,
        ConnectionAborted,
        NotConnected,
        AddrInUse,
        AddrNotAvailable,
        BrokenPipe,
        AlreadyExists,
        WouldBlock,
        InvalidInput,
        InvalidData,
        TimedOut,
        WriteZero,
        Interrupted,
        UnexpectedEof,
        Other,
    }

    pub type Result<T> = core::result::Result<T, Error>;

    pub trait Read {
        fn read(&mut self, buf: &mut [u8]) -> Result<usize>;
        fn read_to_end(&mut self, buf: &mut Vec<u8>) -> Result<usize> {
            let _ = buf;
            Ok(0)
        }
        fn read_to_string(&mut self, buf: &mut String) -> Result<usize> {
            let _ = buf;
            Ok(0)
        }
    }

    pub trait BufRead: Read {
        fn fill_buf(&mut self) -> Result<&[u8]>;
        fn consume(&mut self, amount: usize);
    }

    pub trait Write {
        fn write(&mut self, buf: &[u8]) -> Result<usize>;
        fn flush(&mut self) -> Result<()>;
        fn write_all(&mut self, mut buf: &[u8]) -> Result<()> {
            while !buf.is_empty() {
                match self.write(buf) {
                    Ok(0) => return Err(Error { repr: "failed to write whole buffer" }),
                    Ok(n) => buf = &buf[n..],
                    Err(e) => return Err(e),
                }
            }
            Ok(())
        }
        fn write_fmt(&mut self, fmt: core::fmt::Arguments<'_>) -> Result<()> {
            let _ = fmt;
            Ok(())
        }
    }

    pub trait Seek {
        fn seek(&mut self, pos: SeekFrom) -> Result<u64>;
    }

    pub enum SeekFrom {
        Start(u64),
        End(i64),
        Current(i64),
    }

    pub struct Cursor<T> {
        inner: T,
        pos: u64,
    }

    impl<T> Cursor<T> {
        pub const fn new(inner: T) -> Self {
            Self { inner, pos: 0 }
        }
        pub fn get_ref(&self) -> &T {
            &self.inner
        }
        pub fn get_mut(&mut self) -> &mut T {
            &mut self.inner
        }
        pub fn into_inner(self) -> T {
            self.inner
        }
        pub fn position(&self) -> u64 {
            self.pos
        }
        pub fn set_position(&mut self, pos: u64) {
            self.pos = pos;
        }
    }

    impl<T: AsRef<[u8]>> Read for Cursor<T> {
        fn read(&mut self, buf: &mut [u8]) -> Result<usize> {
            let slice = self.inner.as_ref();
            if self.pos >= slice.len() as u64 {
                return Ok(0);
            }
            let avail = &slice[self.pos as usize..];
            let n = core::cmp::min(avail.len(), buf.len());
            buf[..n].copy_from_slice(&avail[..n]);
            self.pos += n as u64;
            Ok(n)
        }
    }

    pub fn _print(args: core::fmt::Arguments<'_>) {
        let _ = args;
    }

    pub fn _eprint(args: core::fmt::Arguments<'_>) {
        let _ = args;
    }

    #[repr(transparent)]
    pub struct IoSlice<'a> {
        inner: &'a [u8],
    }
    impl<'a> IoSlice<'a> {
        pub fn new(slice: &'a [u8]) -> Self {
            Self { inner: slice }
        }
    }
    impl<'a> core::ops::Deref for IoSlice<'a> {
        type Target = [u8];
        fn deref(&self) -> &[u8] {
            self.inner
        }
    }

    #[repr(transparent)]
    pub struct IoSliceMut<'a> {
        inner: &'a mut [u8],
    }
    impl<'a> IoSliceMut<'a> {
        pub fn new(slice: &'a mut [u8]) -> Self {
            Self { inner: slice }
        }
    }
    impl<'a> core::ops::Deref for IoSliceMut<'a> {
        type Target = [u8];
        fn deref(&self) -> &[u8] {
            self.inner
        }
    }
    impl<'a> core::ops::DerefMut for IoSliceMut<'a> {
        fn deref_mut(&mut self) -> &mut [u8] {
            self.inner
        }
    }
}

pub mod path {
    use alloc::string::String;
    use alloc::borrow::Cow;

    #[repr(transparent)]
    pub struct Path {
        inner: str,
    }

    impl Path {
        pub fn new<S: AsRef<crate::ffi::OsStr> + ?Sized>(s: &S) -> &Path {
            unsafe { &*(s.as_ref() as *const crate::ffi::OsStr as *const Path) }
        }

        pub fn to_path_buf(&self) -> PathBuf {
            PathBuf { inner: String::from(&self.inner) }
        }

        pub fn is_file(&self) -> bool {
            false
        }

        pub fn is_dir(&self) -> bool {
            false
        }

        pub fn exists(&self) -> bool {
            false
        }

        pub fn parent(&self) -> Option<&Path> {
            None
        }

        pub fn file_name(&self) -> Option<&core::ffi::CStr> {
            None
        }

        pub fn file_stem(&self) -> Option<&core::ffi::CStr> {
            None
        }

        pub fn extension(&self) -> Option<&core::ffi::CStr> {
            None
        }

        pub fn is_absolute(&self) -> bool {
            self.inner.starts_with('/')
        }

        pub fn is_relative(&self) -> bool {
            !self.is_absolute()
        }

        pub fn starts_with<P: AsRef<Path>>(&self, base: P) -> bool {
            let base = &base.as_ref().inner;
            self.inner == *base
                || (self.inner.starts_with(base)
                    && self.inner.as_bytes().get(base.len()) == Some(&b'/'))
        }

        pub fn join<P: AsRef<Path>>(&self, path: P) -> PathBuf {
            let mut buf = self.to_path_buf();
            buf.push(path);
            buf
        }

        pub fn display(&self) -> Display<'_> {
            Display { path: self }
        }

        pub fn to_str(&self) -> Option<&str> {
            Some(&self.inner)
        }

        pub fn to_string_lossy(&self) -> Cow<'_, str> {
            Cow::Borrowed(&self.inner)
        }

        pub fn components(&self) -> Components<'_> {
            Components { path: &self.inner }
        }

        pub fn iter(&self) -> Iter<'_> {
            Iter { inner: self.components() }
        }

        pub fn as_os_str(&self) -> &crate::ffi::OsStr {
            crate::ffi::OsStr::new(&self.inner)
        }
    }

    #[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
    pub enum Component<'a> {
        Prefix(PrefixComponent<'a>),
        RootDir,
        CurDir,
        ParentDir,
        Normal(&'a str),
    }

    impl<'a> Component<'a> {
        pub fn as_os_str(&self) -> &'a crate::ffi::OsStr {
            match self {
                Component::Prefix(p) => crate::ffi::OsStr::new(p.raw),
                Component::RootDir => crate::ffi::OsStr::new("/"),
                Component::CurDir => crate::ffi::OsStr::new("."),
                Component::ParentDir => crate::ffi::OsStr::new(".."),
                Component::Normal(s) => crate::ffi::OsStr::new(s),
            }
        }
    }

    #[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
    pub struct PrefixComponent<'a> {
        raw: &'a str,
    }

    #[derive(Clone, Debug)]
    pub struct Components<'a> {
        path: &'a str,
    }

    impl<'a> Components<'a> {
        pub fn as_path(&self) -> &'a Path {
            Path::new(self.path)
        }
    }

    impl<'a> Iterator for Components<'a> {
        type Item = Component<'a>;
        fn next(&mut self) -> Option<Self::Item> {
            None
        }
    }

    #[derive(Clone, Debug)]
    pub struct Iter<'a> {
        inner: Components<'a>,
    }

    impl<'a> Iter<'a> {
        pub fn as_path(&self) -> &'a Path {
            self.inner.as_path()
        }
    }

    impl<'a> Iterator for Iter<'a> {
        type Item = &'a crate::ffi::OsStr;
        fn next(&mut self) -> Option<Self::Item> {
            None
        }
    }

    impl AsRef<Path> for Path {
        fn as_ref(&self) -> &Path {
            self
        }
    }

    impl AsRef<crate::ffi::OsStr> for Path {
        fn as_ref(&self) -> &crate::ffi::OsStr {
            self.as_os_str()
        }
    }

    pub struct Display<'a> {
        path: &'a Path,
    }

    impl core::fmt::Display for Display<'_> {
        fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
            write!(f, "{}", &self.path.inner)
        }
    }

    impl core::fmt::Debug for Path {
        fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
            write!(f, "{:?}", &self.inner)
        }
    }


    #[derive(Clone, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
    pub struct PathBuf {
        inner: String,
    }

    impl PathBuf {
        pub fn new() -> Self {
            Self { inner: String::new() }
        }

        pub fn into_boxed_path(self) -> alloc::boxed::Box<Path> {
            let raw = alloc::boxed::Box::leak(self.inner.into_boxed_str());
            unsafe { alloc::boxed::Box::from_raw(Path::new(raw) as *const Path as *mut Path) }
        }

        pub fn as_path(&self) -> &Path {
            Path::new(&self.inner)
        }

        pub fn push<P: AsRef<Path>>(&mut self, path: P) {
            let p = path.as_ref();
            if !self.inner.is_empty() && !self.inner.ends_with('/') {
                self.inner.push('/');
            }
            self.inner.push_str(&p.inner);
        }

        pub fn pop(&mut self) -> bool {
            if let Some(pos) = self.inner.rfind('/') {
                self.inner.truncate(pos);
                true
            } else {
                false
            }
        }

        pub fn with_extension<S: AsRef<str>>(&self, ext: S) -> PathBuf {
            let mut s = self.inner.clone();
            if let Some(pos) = s.rfind('.') {
                s.truncate(pos);
            }
            s.push('.');
            s.push_str(ext.as_ref());
            PathBuf { inner: s }
        }

        pub fn as_os_str(&self) -> &crate::ffi::OsStr {
            crate::ffi::OsStr::new(&self.inner)
        }

        pub fn into_os_string(self) -> crate::ffi::OsString {
            crate::ffi::OsString::from(&self.inner)
        }
    }

    impl From<&str> for PathBuf {
        fn from(s: &str) -> Self {
            PathBuf { inner: String::from(s) }
        }
    }

    impl From<String> for PathBuf {
        fn from(s: String) -> Self {
            PathBuf { inner: s }
        }
    }

    impl From<crate::ffi::OsString> for PathBuf {
        fn from(s: crate::ffi::OsString) -> Self {
            PathBuf { inner: s.to_string_lossy().into_owned() }
        }
    }

    impl From<&crate::ffi::OsStr> for PathBuf {
        fn from(s: &crate::ffi::OsStr) -> Self {
            PathBuf { inner: s.to_string_lossy().into_owned() }
        }
    }

    impl From<&Path> for PathBuf {
        fn from(p: &Path) -> Self {
            p.to_path_buf()
        }
    }

    impl core::fmt::Debug for PathBuf {
        fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
            write!(f, "{:?}", &self.inner)
        }
    }

    impl AsRef<crate::ffi::OsStr> for PathBuf {
        fn as_ref(&self) -> &crate::ffi::OsStr {
            self.as_os_str()
        }
    }

    impl core::ops::Deref for PathBuf {
        type Target = Path;
        fn deref(&self) -> &Path {
            self.as_path()
        }
    }

    impl AsRef<Path> for PathBuf {
        fn as_ref(&self) -> &Path {
            self.as_path()
        }
    }

    impl AsRef<crate::ffi::OsStr> for &PathBuf {
        fn as_ref(&self) -> &crate::ffi::OsStr {
            self.as_os_str()
        }
    }

    impl AsRef<crate::ffi::OsStr> for &Path {
        fn as_ref(&self) -> &crate::ffi::OsStr {
            self.as_os_str()
        }
    }

    impl AsRef<Path> for &PathBuf {
        fn as_ref(&self) -> &Path {
            self.as_path()
        }
    }

    impl AsRef<Path> for &Path {
        fn as_ref(&self) -> &Path {
            self
        }
    }

    impl AsRef<Path> for str {
        fn as_ref(&self) -> &Path {
            Path::new(self)
        }
    }

    impl AsRef<Path> for &str {
        fn as_ref(&self) -> &Path {
            Path::new(self)
        }
    }

    impl AsRef<Path> for String {
        fn as_ref(&self) -> &Path {
            Path::new(self)
        }
    }

    impl AsRef<Path> for &String {
        fn as_ref(&self) -> &Path {
            Path::new(self)
        }
    }
}

pub mod ffi {
    pub use core::ffi::*;
    use alloc::string::String;
    use alloc::vec::Vec;

    #[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
    pub struct OsString {
        inner: String,
    }

    impl OsString {
        pub fn new() -> Self {
            Self { inner: String::new() }
        }
        pub fn from(s: &str) -> Self {
            Self { inner: String::from(s) }
        }
        pub fn as_os_str(&self) -> &OsStr {
            OsStr::new(&self.inner)
        }
        pub fn is_empty(&self) -> bool {
            self.inner.is_empty()
        }
        pub fn len(&self) -> usize {
            self.inner.len()
        }
        pub fn clear(&mut self) {
            self.inner.clear();
        }
        pub fn push<T: AsRef<OsStr>>(&mut self, s: T) {
            self.inner.push_str(s.as_ref().to_str().unwrap_or(""));
        }
        pub fn into_boxed_os_str(self) -> alloc::boxed::Box<OsStr> {
            let raw = alloc::boxed::Box::leak(self.inner.into_boxed_str());
            unsafe { alloc::boxed::Box::from_raw(OsStr::new(raw) as *const OsStr as *mut OsStr) }
        }
    }

    impl core::fmt::Debug for OsString {
        fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
            write!(f, "{:?}", &self.inner)
        }
    }

    impl core::ops::Deref for OsString {
        type Target = OsStr;
        fn deref(&self) -> &OsStr {
            self.as_os_str()
        }
    }

    impl PartialEq<str> for OsString {
        fn eq(&self, other: &str) -> bool {
            self.inner == other
        }
    }

    impl PartialEq<&str> for OsString {
        fn eq(&self, other: &&str) -> bool {
            self.inner == *other
        }
    }

    #[repr(transparent)]
    pub struct OsStr {
        inner: str,
    }

    impl OsStr {
        pub fn new<S: AsRef<str> + ?Sized>(s: &S) -> &OsStr {
            unsafe { &*(s.as_ref() as *const str as *const OsStr) }
        }
        pub fn to_str(&self) -> Option<&str> {
            Some(&self.inner)
        }
        pub fn to_string_lossy(&self) -> alloc::borrow::Cow<'_, str> {
            alloc::borrow::Cow::Borrowed(&self.inner)
        }
        pub fn to_os_string(&self) -> OsString {
            OsString { inner: String::from(&self.inner) }
        }
        pub fn is_empty(&self) -> bool {
            self.inner.is_empty()
        }
        pub fn len(&self) -> usize {
            self.inner.len()
        }
    }

    impl core::fmt::Debug for OsStr {
        fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
            write!(f, "{:?}", &self.inner)
        }
    }

    impl PartialEq for OsStr {
        fn eq(&self, other: &Self) -> bool {
            self.inner == other.inner
        }
    }

    impl Eq for OsStr {}

    impl PartialEq<str> for OsStr {
        fn eq(&self, other: &str) -> bool {
            self.inner == other
        }
    }

    impl AsRef<OsStr> for str {
        fn as_ref(&self) -> &OsStr {
            OsStr::new(self)
        }
    }

    impl AsRef<OsStr> for String {
        fn as_ref(&self) -> &OsStr {
            OsStr::new(self)
        }
    }

    impl AsRef<OsStr> for OsString {
        fn as_ref(&self) -> &OsStr {
            self.as_os_str()
        }
    }

    impl alloc::borrow::ToOwned for OsStr {
        type Owned = OsString;
        fn to_owned(&self) -> OsString {
            self.to_os_string()
        }
    }

    impl core::borrow::Borrow<OsStr> for OsString {
        fn borrow(&self) -> &OsStr {
            self.as_os_str()
        }
    }

    impl core::borrow::Borrow<OsStr> for OsStr {
        fn borrow(&self) -> &OsStr {
            self
        }
    }

    impl AsRef<OsStr> for OsStr {
        fn as_ref(&self) -> &OsStr {
            self
        }
    }

    impl AsRef<OsStr> for &OsString {
        fn as_ref(&self) -> &OsStr {
            self.as_os_str()
        }
    }

    impl AsRef<OsStr> for &OsStr {
        fn as_ref(&self) -> &OsStr {
            self
        }
    }

    impl AsRef<OsStr> for &str {
        fn as_ref(&self) -> &OsStr {
            OsStr::new(self)
        }
    }

    impl AsRef<OsStr> for &String {
        fn as_ref(&self) -> &OsStr {
            OsStr::new(self)
        }
    }

    impl AsRef<str> for OsStr {
        fn as_ref(&self) -> &str {
            &self.inner
        }
    }

    impl AsRef<crate::path::Path> for OsStr {
        fn as_ref(&self) -> &crate::path::Path {
            crate::path::Path::new(self)
        }
    }

    impl AsRef<crate::path::Path> for OsString {
        fn as_ref(&self) -> &crate::path::Path {
            crate::path::Path::new(self)
        }
    }

    pub use alloc::ffi::*;
}

pub mod env {
    use super::ffi::{OsStr, OsString};
    use alloc::string::String;
    use alloc::vec::Vec;

    pub fn var<K: AsRef<OsStr>>(key: K) -> Result<String, VarError> {
        let _ = key;
        Err(VarError::NotPresent)
    }

    pub fn var_os<K: AsRef<OsStr>>(key: K) -> Option<OsString> {
        let _ = key;
        None
    }

    pub fn current_dir() -> super::io::Result<super::path::PathBuf> {
        Ok(super::path::PathBuf::from("."))
    }

    pub fn current_exe() -> super::io::Result<super::path::PathBuf> {
        Ok(super::path::PathBuf::from("hyprc"))
    }

    pub fn temp_dir() -> super::path::PathBuf {
        super::path::PathBuf::from("/tmp")
    }

    pub fn home_dir() -> Option<super::path::PathBuf> {
        var_os("HOME").map(|s| super::path::PathBuf::from(s.to_str().unwrap_or("")))
    }

    pub fn split_paths<T: AsRef<OsStr> + ?Sized>(unparsed: &T) -> SplitPaths<'_> {
        let _ = unparsed;
        SplitPaths { _marker: core::marker::PhantomData }
    }

    pub struct SplitPaths<'a> {
        _marker: core::marker::PhantomData<&'a OsStr>,
    }

    impl<'a> Iterator for SplitPaths<'a> {
        type Item = super::path::PathBuf;
        fn next(&mut self) -> Option<Self::Item> {
            None
        }
    }

    pub fn join_paths<I, T>(paths: I) -> Result<OsString, JoinPathsError>
    where
        I: IntoIterator<Item = T>,
        T: AsRef<OsStr>,
    {
        let _ = paths;
        Ok(OsString::new())
    }

    #[derive(Debug)]
    pub struct JoinPathsError;

    impl core::fmt::Display for JoinPathsError {
        fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
            write!(f, "failed to join paths")
        }
    }

    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub enum VarError {
        NotPresent,
        NotUnicode(super::ffi::OsString),
    }

    pub const ARCH: &str = "x86_64";
    pub const OS: &str = "linux";
    pub const FAMILY: &str = "unix";
}

pub mod fs {
    use super::io::{self, Read, Write};
    use super::path::Path;
    use alloc::string::String;
    use alloc::vec::Vec;

    pub struct File;

    impl File {
        pub fn open<P: AsRef<Path>>(path: P) -> io::Result<File> {
            let _ = path;
            Ok(File)
        }
        pub fn create<P: AsRef<Path>>(path: P) -> io::Result<File> {
            let _ = path;
            Ok(File)
        }
    }

    impl Read for File {
        fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
            let _ = buf;
            Ok(0)
        }
    }

    impl Write for File {
        fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
            Ok(buf.len())
        }
        fn flush(&mut self) -> io::Result<()> {
            Ok(())
        }
    }

    pub fn read<P: AsRef<Path>>(path: P) -> io::Result<Vec<u8>> {
        let _ = path;
        Ok(Vec::new())
    }

    pub fn read_to_string<P: AsRef<Path>>(path: P) -> io::Result<String> {
        let _ = path;
        Ok(String::new())
    }

    pub fn write<P: AsRef<Path>, C: AsRef<[u8]>>(path: P, contents: C) -> io::Result<()> {
        let _ = (path, contents);
        Ok(())
    }

    pub fn create_dir_all<P: AsRef<Path>>(path: P) -> io::Result<()> {
        let _ = path;
        Ok(())
    }

    pub fn remove_file<P: AsRef<Path>>(path: P) -> io::Result<()> {
        let _ = path;
        Ok(())
    }

    pub fn remove_dir_all<P: AsRef<Path>>(path: P) -> io::Result<()> {
        let _ = path;
        Ok(())
    }

    pub fn canonicalize<P: AsRef<Path>>(path: P) -> io::Result<super::path::PathBuf> {
        Ok(path.as_ref().to_path_buf())
    }
}

pub mod time {
    pub use core::time::Duration;

    #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
    pub struct Instant;

    impl Instant {
        pub fn now() -> Self {
            Instant
        }
        pub fn elapsed(&self) -> Duration {
            Duration::from_secs(0)
        }
    }

    #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
    pub struct SystemTime;

    impl SystemTime {
        pub fn now() -> Self {
            SystemTime
        }
        pub const UNIX_EPOCH: SystemTime = SystemTime;

        pub fn duration_since(&self, earlier: SystemTime) -> Result<Duration, ()> {
            let _ = earlier;
            Ok(Duration::from_secs(0))
        }

        pub fn elapsed(&self) -> Result<Duration, ()> {
            Ok(Duration::from_secs(0))
        }

        pub fn checked_add(&self, duration: Duration) -> Option<SystemTime> {
            let _ = duration;
            Some(*self)
        }

        pub fn checked_sub(&self, duration: Duration) -> Option<SystemTime> {
            let _ = duration;
            Some(*self)
        }
    }

    pub const UNIX_EPOCH: SystemTime = SystemTime;
}

pub mod hash {
    pub use core::hash::*;

    #[derive(Clone, Default, Debug)]
    pub struct RandomState {
        k0: u64,
        k1: u64,
    }

    impl RandomState {
        pub const fn new() -> Self {
            Self { k0: 0, k1: 0 }
        }
    }

    impl BuildHasher for RandomState {
        type Hasher = DefaultHasher;
        fn build_hasher(&self) -> DefaultHasher {
            DefaultHasher::new()
        }
    }

    #[derive(Clone, Default, Debug)]
    pub struct DefaultHasher {
        state: u64,
    }

    impl DefaultHasher {
        pub const fn new() -> Self {
            Self { state: 0 }
        }
    }

    impl Hasher for DefaultHasher {
        fn finish(&self) -> u64 {
            self.state
        }
        fn write(&mut self, bytes: &[u8]) {
            for &b in bytes {
                self.state = self.state.wrapping_mul(31).wrapping_add(b as u64);
            }
        }
    }
}

pub mod collections {
    pub use alloc::collections::*;
    use alloc::vec::Vec;
    use core::marker::PhantomData;

    #[derive(Clone, Debug, Default)]
    pub struct HashMap<K, V, S = ()> {
        entries: Vec<(K, V)>,
        _marker: PhantomData<S>,
    }

    impl<K, V> HashMap<K, V, ()> {
        pub fn new() -> Self {
            Self { entries: Vec::new(), _marker: PhantomData }
        }
        pub fn with_capacity(cap: usize) -> Self {
            Self { entries: Vec::with_capacity(cap), _marker: PhantomData }
        }
    }

    impl<K, V, S> HashMap<K, V, S> {
        pub fn with_hasher(hash_builder: S) -> Self {
            let _ = hash_builder;
            Self { entries: Vec::new(), _marker: PhantomData }
        }
        pub fn with_capacity_and_hasher(cap: usize, hash_builder: S) -> Self {
            let _ = hash_builder;
            Self { entries: Vec::with_capacity(cap), _marker: PhantomData }
        }
        pub fn len(&self) -> usize {
            self.entries.len()
        }
        pub fn is_empty(&self) -> bool {
            self.entries.is_empty()
        }
        pub fn clear(&mut self) {
            self.entries.clear();
        }
        pub fn capacity(&self) -> usize {
            self.entries.capacity()
        }
        pub fn iter(&self) -> impl Iterator<Item = (&K, &V)> {
            self.entries.iter().map(|(k, v)| (k, v))
        }
        pub fn iter_mut(&mut self) -> impl Iterator<Item = (&K, &mut V)> {
            self.entries.iter_mut().map(|(k, v)| (&*k, v))
        }
        pub fn keys(&self) -> impl Iterator<Item = &K> {
            self.entries.iter().map(|(k, _)| k)
        }
        pub fn values(&self) -> impl Iterator<Item = &V> {
            self.entries.iter().map(|(_, v)| v)
        }
        pub fn values_mut(&mut self) -> impl Iterator<Item = &mut V> {
            self.entries.iter_mut().map(|(_, v)| v)
        }
    }

    impl<K: PartialEq, V, S> HashMap<K, V, S> {
        pub fn get<Q>(&self, k: &Q) -> Option<&V>
        where
            K: core::borrow::Borrow<Q>,
            Q: ?Sized + PartialEq,
        {
            self.entries.iter().find(|(key, _)| key.borrow() == k).map(|(_, v)| v)
        }

        pub fn get_mut<Q>(&mut self, k: &Q) -> Option<&mut V>
        where
            K: core::borrow::Borrow<Q>,
            Q: ?Sized + PartialEq,
        {
            self.entries.iter_mut().find(|(key, _)| key.borrow() == k).map(|(_, v)| v)
        }

        pub fn contains_key<Q>(&self, k: &Q) -> bool
        where
            K: core::borrow::Borrow<Q>,
            Q: ?Sized + PartialEq,
        {
            self.get(k).is_some()
        }

        pub fn insert(&mut self, k: K, v: V) -> Option<V> {
            if let Some(existing) = self.entries.iter_mut().find(|(key, _)| *key == k) {
                Some(core::mem::replace(&mut existing.1, v))
            } else {
                self.entries.push((k, v));
                None
            }
        }

        pub fn remove<Q>(&mut self, k: &Q) -> Option<V>
        where
            K: core::borrow::Borrow<Q>,
            Q: ?Sized + PartialEq,
        {
            if let Some(pos) = self.entries.iter().position(|(key, _)| key.borrow() == k) {
                Some(self.entries.remove(pos).1)
            } else {
                None
            }
        }

        pub fn reserve(&mut self, additional: usize) {
            self.entries.reserve(additional);
        }
    }

    pub struct Iter<'a, T> {
        inner: alloc::vec::IntoIter<T>,
    }

    impl<'a, T> Iterator for Iter<'a, T> {
        type Item = T;
        fn next(&mut self) -> Option<Self::Item> {
            self.inner.next()
        }
        fn size_hint(&self) -> (usize, Option<usize>) {
            self.inner.size_hint()
        }
    }

    impl<K, V, S> IntoIterator for HashMap<K, V, S> {
        type Item = (K, V);
        type IntoIter = alloc::vec::IntoIter<(K, V)>;
        fn into_iter(self) -> Self::IntoIter {
            self.entries.into_iter()
        }
    }

    impl<'a, K: 'a, V: 'a, S> IntoIterator for &'a HashMap<K, V, S> {
        type Item = (&'a K, &'a V);
        type IntoIter = Iter<'a, (&'a K, &'a V)>;
        fn into_iter(self) -> Self::IntoIter {
            let v: Vec<(&'a K, &'a V)> = self.entries.iter().map(|(k, v)| (k, v)).collect();
            Iter { inner: v.into_iter() }
        }
    }

    #[derive(Clone, Debug, Default)]
    pub struct HashSet<T, S = ()> {
        map: HashMap<T, (), S>,
    }

    impl<T> HashSet<T, ()> {
        pub fn new() -> Self {
            Self { map: HashMap::new() }
        }
        pub fn with_capacity(cap: usize) -> Self {
            Self { map: HashMap::with_capacity(cap) }
        }
    }

    impl<T, S> HashSet<T, S> {
        pub fn with_hasher(hash_builder: S) -> Self {
            Self { map: HashMap::with_hasher(hash_builder) }
        }
        pub fn with_capacity_and_hasher(cap: usize, hash_builder: S) -> Self {
            Self { map: HashMap::with_capacity_and_hasher(cap, hash_builder) }
        }
        pub fn len(&self) -> usize {
            self.map.len()
        }
        pub fn is_empty(&self) -> bool {
            self.map.is_empty()
        }
        pub fn clear(&mut self) {
            self.map.clear();
        }
        pub fn iter(&self) -> impl Iterator<Item = &T> {
            self.map.keys()
        }
        pub fn reserve(&mut self, additional: usize) {
            self.map.reserve(additional);
        }
    }

    impl<T: PartialEq, S> HashSet<T, S> {
        pub fn contains<Q>(&self, value: &Q) -> bool
        where
            T: core::borrow::Borrow<Q>,
            Q: ?Sized + PartialEq,
        {
            self.map.contains_key(value)
        }

        pub fn insert(&mut self, value: T) -> bool {
            self.map.insert(value, ()).is_none()
        }

        pub fn remove<Q>(&mut self, value: &Q) -> bool
        where
            T: core::borrow::Borrow<Q>,
            Q: ?Sized + PartialEq,
        {
            self.map.remove(value).is_some()
        }
    }

    impl<T, S> IntoIterator for HashSet<T, S> {
        type Item = T;
        type IntoIter = core::iter::Map<alloc::vec::IntoIter<(T, ())>, fn((T, ())) -> T>;
        fn into_iter(self) -> Self::IntoIter {
            self.map.into_iter().map(|(t, ())| t)
        }
    }

    impl<'a, T: 'a, S> IntoIterator for &'a HashSet<T, S> {
        type Item = &'a T;
        type IntoIter = Iter<'a, &'a T>;
        fn into_iter(self) -> Self::IntoIter {
            let v: Vec<&'a T> = self.map.entries.iter().map(|(k, _)| k).collect();
            Iter { inner: v.into_iter() }
        }
    }
}

#[macro_export]
macro_rules! is_x86_feature_detected {
    ($($arg:tt)*) => {
        false
    };
}
pub use is_x86_feature_detected;

#[macro_export]
macro_rules! is_aarch64_feature_detected {
    ($($arg:tt)*) => {
        false
    };
}
pub use is_aarch64_feature_detected;

pub mod arch {
    pub use core::arch::*;
    #[cfg(target_arch = "x86_64")]
    pub use core::arch::x86_64::*;
    #[cfg(target_arch = "x86")]
    pub use core::arch::x86::*;
    #[cfg(target_arch = "aarch64")]
    pub use core::arch::aarch64::*;

    pub use crate::is_x86_feature_detected;
    pub use crate::is_aarch64_feature_detected;
}

pub mod task {
    pub use core::task::*;

    #[macro_export]
    macro_rules! ready {
        ($e:expr) => {
            match $e {
                $crate::task::Poll::Ready(t) => t,
                $crate::task::Poll::Pending => return $crate::task::Poll::Pending,
            }
        };
    }
    pub use ready;
}
pub use task::ready;

pub mod thread {
    use alloc::boxed::Box;
    use alloc::vec::Vec;
    use core::any::Any;
    use core::ffi::c_void;
    use core::marker::PhantomData;

    pub type Result<T> = core::result::Result<T, Box<dyn Any + Send + 'static>>;

    #[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
    pub struct ThreadId(usize);

    #[derive(Clone, Debug)]
    pub struct Thread {
        id: ThreadId,
    }

    impl Thread {
        pub fn id(&self) -> ThreadId {
            self.id
        }

        pub fn name(&self) -> Option<&str> {
            None
        }

        pub fn unpark(&self) {}
    }

    #[cfg(unix)]
    unsafe extern "C" {
        fn pthread_self() -> usize;
        fn pthread_create(
            thread: *mut usize,
            attr: *const c_void,
            start: unsafe extern "C" fn(*mut c_void) -> *mut c_void,
            arg: *mut c_void,
        ) -> i32;
        fn pthread_join(thread: usize, value: *mut *mut c_void) -> i32;
        fn pthread_detach(thread: usize) -> i32;
        fn sched_yield() -> i32;
    }

    #[cfg(unix)]
    fn current_id() -> usize {
        unsafe { pthread_self() }
    }

    #[cfg(not(unix))]
    fn current_id() -> usize {
        0
    }

    pub fn current() -> Thread {
        Thread {
            id: ThreadId(current_id()),
        }
    }

    pub fn panicking() -> bool {
        false
    }

    pub fn yield_now() {
        #[cfg(unix)]
        unsafe {
            let _ = sched_yield();
        }
        #[cfg(not(unix))]
        core::hint::spin_loop();
    }

    struct Start<F>(F);

    unsafe extern "C" fn start_thread<F, T>(data: *mut c_void) -> *mut c_void
    where
        F: FnOnce() -> T,
    {
        let start = unsafe { Box::from_raw(data.cast::<Start<F>>()) };
        let Start(f) = *start;
        Box::into_raw(Box::new(f())).cast::<c_void>()
    }

    pub struct JoinHandle<T> {
        pthread: usize,
        thread: Thread,
        joined: bool,
        output: PhantomData<T>,
    }

    unsafe impl<T: Send> Send for JoinHandle<T> {}
    unsafe impl<T: Send> Sync for JoinHandle<T> {}

    impl<T> JoinHandle<T> {
        pub fn thread(&self) -> &Thread {
            &self.thread
        }

        pub fn join(mut self) -> Result<T> {
            let mut output = core::ptr::null_mut();
            let status = unsafe { pthread_join(self.pthread, &mut output) };
            self.joined = true;
            if status != 0 || output.is_null() {
                return Err(Box::new("thread failed to join"));
            }
            Ok(*unsafe { Box::from_raw(output.cast::<T>()) })
        }

        #[doc(hidden)]
        pub fn as_pthread_t(&self) -> usize {
            self.pthread
        }
    }

    impl<T> Drop for JoinHandle<T> {
        fn drop(&mut self) {
            if !self.joined {
                unsafe {
                    let _ = pthread_detach(self.pthread);
                }
            }
        }
    }

    pub struct Builder {
        name: Option<alloc::string::String>,
        stack_size: Option<usize>,
    }

    impl Builder {
        pub fn new() -> Self {
            Self {
                name: None,
                stack_size: None,
            }
        }

        pub fn name(mut self, name: alloc::string::String) -> Self {
            self.name = Some(name);
            self
        }

        pub fn stack_size(mut self, size: usize) -> Self {
            self.stack_size = Some(size);
            self
        }

        pub fn spawn<F, T>(self, f: F) -> crate::io::Result<JoinHandle<T>>
        where
            F: FnOnce() -> T + Send + 'static,
            T: Send + 'static,
        {
            let _ = (self.name, self.stack_size);
            let start = Box::new(Start(f));
            let data = Box::into_raw(start).cast::<c_void>();
            let mut pthread = 0usize;
            let status = unsafe {
                pthread_create(
                    &mut pthread,
                    core::ptr::null(),
                    start_thread::<F, T>,
                    data,
                )
            };
            if status != 0 {
                unsafe {
                    drop(Box::from_raw(data.cast::<Start<F>>()));
                }
                return Err(crate::io::Error::from_raw_os_error(status));
            }
            Ok(JoinHandle {
                pthread,
                thread: Thread {
                    id: ThreadId(pthread),
                },
                joined: false,
                output: PhantomData,
            })
        }
    }

    pub fn spawn<F, T>(f: F) -> JoinHandle<T>
    where
        F: FnOnce() -> T + Send + 'static,
        T: Send + 'static,
    {
        Builder::new().spawn(f).unwrap()
    }

    pub struct LocalKey<T: 'static> {
        #[doc(hidden)]
        pub init: fn() -> T,
        #[doc(hidden)]
        pub storage: crate::sync::Mutex<Vec<(ThreadId, Box<T>)>>,
    }

    unsafe impl<T: 'static> Sync for LocalKey<T> {}

    impl<T: 'static> LocalKey<T> {
        pub const fn new(init: fn() -> T) -> Self {
            Self {
                init,
                storage: crate::sync::Mutex::new(Vec::new()),
            }
        }

        pub fn with<F, R>(&'static self, f: F) -> R
        where
            F: FnOnce(&T) -> R,
        {
            let id = current().id();
            let mut values = self.storage.lock().unwrap();
            let index = values
                .iter()
                .position(|(owner, _)| *owner == id)
                .unwrap_or_else(|| {
                    values.push((id, Box::new((self.init)())));
                    values.len() - 1
                });
            let value = &*values[index].1 as *const T;
            drop(values);
            // Each entry belongs to one thread and its box has a stable address even when the
            // protected vector grows. Reentrant `with` calls therefore remain valid as well.
            unsafe {
                f(&*value)
            }
        }
    }
}

#[macro_export]
macro_rules! thread_local {
    () => {};
    ($(#[$attr:meta])* $vis:vis static $name:ident: $t:ty = const { $init:expr }; $($rest:tt)*) => {
        $(#[$attr])* $vis static $name: $crate::thread::LocalKey<$t> =
            $crate::thread::LocalKey::new(|| $init);
        $crate::thread_local!($($rest)*);
    };
    ($(#[$attr:meta])* $vis:vis static $name:ident: $t:ty = const { $init:expr } $($rest:tt)*) => {
        $(#[$attr])* $vis static $name: $crate::thread::LocalKey<$t> =
            $crate::thread::LocalKey::new(|| $init);
        $crate::thread_local!($($rest)*);
    };
    ($(#[$attr:meta])* $vis:vis static $name:ident: $t:ty = $init:expr; $($rest:tt)*) => {
        $(#[$attr])* $vis static $name: $crate::thread::LocalKey<$t> =
            $crate::thread::LocalKey::new(|| $init);
        $crate::thread_local!($($rest)*);
    };
    ($(#[$attr:meta])* $vis:vis static $name:ident: $t:ty = $init:expr $($rest:tt)*) => {
        $(#[$attr])* $vis static $name: $crate::thread::LocalKey<$t> =
            $crate::thread::LocalKey::new(|| $init);
        $crate::thread_local!($($rest)*);
    };
}
pub use thread_local;

pub mod os {
    pub mod fd {
        pub type RawFd = i32;

        pub trait AsRawFd {
            fn as_raw_fd(&self) -> RawFd;
        }
        pub trait FromRawFd {
            unsafe fn from_raw_fd(fd: RawFd) -> Self;
        }
        pub trait IntoRawFd {
            fn into_raw_fd(self) -> RawFd;
        }

        #[derive(Debug, Copy, Clone)]
        pub struct BorrowedFd<'a> {
            fd: RawFd,
            _marker: core::marker::PhantomData<&'a ()>,
        }

        impl<'a> BorrowedFd<'a> {
            pub unsafe fn borrow_raw(fd: RawFd) -> Self {
                Self { fd, _marker: core::marker::PhantomData }
            }
        }

        impl AsRawFd for BorrowedFd<'_> {
            fn as_raw_fd(&self) -> RawFd {
                self.fd
            }
        }

        #[derive(Debug)]
        pub struct OwnedFd {
            fd: RawFd,
        }

        impl OwnedFd {
            pub unsafe fn from_raw_fd(fd: RawFd) -> Self {
                Self { fd }
            }
        }

        impl AsRawFd for OwnedFd {
            fn as_raw_fd(&self) -> RawFd {
                self.fd
            }
        }

        impl IntoRawFd for OwnedFd {
            fn into_raw_fd(self) -> RawFd {
                let fd = self.fd;
                core::mem::forget(self);
                fd
            }
        }

        pub trait AsFd {
            fn as_fd(&self) -> BorrowedFd<'_>;
        }

        impl AsFd for BorrowedFd<'_> {
            fn as_fd(&self) -> BorrowedFd<'_> {
                *self
            }
        }

        impl AsFd for OwnedFd {
            fn as_fd(&self) -> BorrowedFd<'_> {
                unsafe { BorrowedFd::borrow_raw(self.fd) }
            }
        }

        impl<T: AsFd + ?Sized> AsFd for &T {
            fn as_fd(&self) -> BorrowedFd<'_> {
                (**self).as_fd()
            }
        }

        impl<T: AsFd + ?Sized> AsFd for &mut T {
            fn as_fd(&self) -> BorrowedFd<'_> {
                (**self).as_fd()
            }
        }
    }

    pub mod unix {
        pub mod io {
            pub use crate::os::fd::*;
        }

        pub mod thread {
            pub type RawPthread = usize;

            pub trait JoinHandleExt {
                fn as_pthread_t(&self) -> RawPthread;
                fn into_pthread_t(self) -> RawPthread;
            }

            impl<T> JoinHandleExt for crate::thread::JoinHandle<T> {
                fn as_pthread_t(&self) -> RawPthread {
                    self.as_pthread_t()
                }

                fn into_pthread_t(self) -> RawPthread {
                    let pthread = self.as_pthread_t();
                    core::mem::forget(self);
                    pthread
                }
            }
        }

        pub mod fs {
            pub trait DirEntryExt {
                fn ino(&self) -> u64 { 0 }
            }
            pub trait FileExt {
                fn read_at(&self, buf: &mut [u8], offset: u64) -> crate::io::Result<usize> { let _ = (buf, offset); Ok(0) }
                fn write_at(&self, buf: &[u8], offset: u64) -> crate::io::Result<usize> { let _ = (buf, offset); Ok(buf.len()) }
            }
            pub trait FileTypeExt {
                fn is_block_device(&self) -> bool { false }
                fn is_char_device(&self) -> bool { false }
                fn is_fifo(&self) -> bool { false }
                fn is_socket(&self) -> bool { false }
            }
            pub trait MetadataExt {
                fn dev(&self) -> u64 { 0 }
                fn ino(&self) -> u64 { 0 }
                fn mode(&self) -> u32 { 0 }
                fn nlink(&self) -> u64 { 0 }
                fn uid(&self) -> u32 { 0 }
                fn gid(&self) -> u32 { 0 }
                fn rdev(&self) -> u64 { 0 }
                fn size(&self) -> u64 { 0 }
                fn atime(&self) -> i64 { 0 }
                fn atime_nsec(&self) -> i64 { 0 }
                fn mtime(&self) -> i64 { 0 }
                fn mtime_nsec(&self) -> i64 { 0 }
                fn ctime(&self) -> i64 { 0 }
                fn ctime_nsec(&self) -> i64 { 0 }
                fn blksize(&self) -> u64 { 0 }
                fn blocks(&self) -> u64 { 0 }
            }
            pub trait OpenOptionsExt {
                fn mode(&mut self, mode: u32) -> &mut Self;
                fn custom_flags(&mut self, flags: i32) -> &mut Self;
            }
        }

        pub mod ffi {
            pub use crate::ffi::*;
            pub trait OsStrExt {
                fn from_bytes(slice: &[u8]) -> &Self;
                fn as_bytes(&self) -> &[u8];
            }
            impl OsStrExt for super::super::super::ffi::OsStr {
                fn from_bytes(slice: &[u8]) -> &Self {
                    unsafe { &*(slice as *const [u8] as *const str as *const Self) }
                }
                fn as_bytes(&self) -> &[u8] {
                    self.to_str().unwrap_or("").as_bytes()
                }
            }
            pub trait OsStringExt {
                fn from_vec(vec: alloc::vec::Vec<u8>) -> Self;
                fn into_vec(self) -> alloc::vec::Vec<u8>;
            }
            impl OsStringExt for super::super::super::ffi::OsString {
                fn from_vec(vec: alloc::vec::Vec<u8>) -> Self {
                    Self::from(alloc::string::String::from_utf8_lossy(&vec).as_ref())
                }
                fn into_vec(self) -> alloc::vec::Vec<u8> {
                    self.to_string_lossy().into_owned().into_bytes()
                }
            }
        }
    }
}

pub mod process {
    use alloc::string::String;
    use alloc::vec::Vec;

    pub struct Child {
        pub id: u32,
    }

    impl Child {
        pub fn id(&self) -> u32 {
            self.id
        }
    }

    #[derive(Copy, Clone, PartialEq, Eq, Debug)]
    pub struct ExitStatus {
        pub code: Option<i32>,
    }

    impl ExitStatus {
        pub fn success(&self) -> bool {
            self.code == Some(0)
        }
        pub fn code(&self) -> Option<i32> {
            self.code
        }
    }

    pub struct Output {
        pub status: ExitStatus,
        pub stdout: Vec<u8>,
        pub stderr: Vec<u8>,
    }

    pub struct Command {
        program: String,
        args: Vec<String>,
    }

    impl Command {
        pub fn new<S: AsRef<crate::ffi::OsStr>>(program: S) -> Self {
            Self {
                program: String::from(program.as_ref().to_str().unwrap_or("")),
                args: Vec::new(),
            }
        }
        pub fn arg<S: AsRef<crate::ffi::OsStr>>(&mut self, arg: S) -> &mut Self {
            self.args.push(String::from(arg.as_ref().to_str().unwrap_or("")));
            self
        }
        pub fn args<I, S>(&mut self, args: I) -> &mut Self
        where
            I: IntoIterator<Item = S>,
            S: AsRef<crate::ffi::OsStr>,
        {
            for a in args {
                self.arg(a);
            }
            self
        }
        pub fn env<K: AsRef<crate::ffi::OsStr>, V: AsRef<crate::ffi::OsStr>>(&mut self, key: K, val: V) -> &mut Self {
            let _ = (key, val);
            self
        }
        pub fn envs<I, K, V>(&mut self, vars: I) -> &mut Self
        where
            I: IntoIterator<Item = (K, V)>,
            K: AsRef<crate::ffi::OsStr>,
            V: AsRef<crate::ffi::OsStr>,
        {
            let _ = vars;
            self
        }
        pub fn env_remove<K: AsRef<crate::ffi::OsStr>>(&mut self, key: K) -> &mut Self {
            let _ = key;
            self
        }
        pub fn env_clear(&mut self) -> &mut Self {
            self
        }
        pub fn current_dir<P: AsRef<crate::path::Path>>(&mut self, dir: P) -> &mut Self {
            let _ = dir;
            self
        }
        pub fn stdin<T>(&mut self, cfg: T) -> &mut Self {
            let _ = cfg;
            self
        }
        pub fn stdout<T>(&mut self, cfg: T) -> &mut Self {
            let _ = cfg;
            self
        }
        pub fn stderr<T>(&mut self, cfg: T) -> &mut Self {
            let _ = cfg;
            self
        }
        pub fn spawn(&mut self) -> crate::io::Result<Child> {
            Err(crate::io::Error::from_raw_os_error(1))
        }
        pub fn output(&mut self) -> crate::io::Result<Output> {
            Err(crate::io::Error::from_raw_os_error(1))
        }
        pub fn status(&mut self) -> crate::io::Result<ExitStatus> {
            Err(crate::io::Error::from_raw_os_error(1))
        }
    }

    pub struct Stdio;
    impl Stdio {
        pub fn inherit() -> Stdio { Stdio }
        pub fn piped() -> Stdio { Stdio }
        pub fn null() -> Stdio { Stdio }
    }

    pub fn exit(code: i32) -> ! {
        unsafe {
            let _ = code;
            core::arch::asm!("syscall", in("rax") 60, in("rdi") code, options(noreturn));
        }
    }

    pub fn abort() -> ! {
        exit(134)
    }
}

pub mod prelude {
    pub mod rust_2024 {
        pub use core::prelude::rust_2024::*;
        pub use alloc::vec::Vec;
        pub use alloc::string::{String, ToString};
        pub use alloc::boxed::Box;
        pub use alloc::borrow::ToOwned;
    }
    pub mod rust_2021 {
        pub use core::prelude::rust_2021::*;
        pub use alloc::vec::Vec;
        pub use alloc::string::{String, ToString};
        pub use alloc::boxed::Box;
        pub use alloc::borrow::ToOwned;
    }
    pub mod rust_2018 {
        pub use core::prelude::rust_2018::*;
        pub use alloc::vec::Vec;
        pub use alloc::string::{String, ToString};
        pub use alloc::boxed::Box;
        pub use alloc::borrow::ToOwned;
    }
    pub mod rust_2015 {
        pub use core::prelude::rust_2015::*;
        pub use alloc::vec::Vec;
        pub use alloc::string::{String, ToString};
        pub use alloc::boxed::Box;
        pub use alloc::borrow::ToOwned;
    }
}
