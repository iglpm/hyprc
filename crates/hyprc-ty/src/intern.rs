//! A process-wide, thread-safe interner for any hashable value: equal values get the same
//! `u32`, and looking a value up by its id takes no lock.

use std::hash::{BuildHasher, Hash};
use std::mem::MaybeUninit;
use std::sync::Mutex;
use std::sync::atomic::{AtomicPtr, AtomicU32, Ordering};

const SHARDS: usize = 64;
const FIRST_CHUNK_BITS: u32 = 10;
const CHUNKS: usize = 32 - FIRST_CHUNK_BITS as usize;

/// Append-only storage with stable addresses: chunk `k` holds `FIRST << k` entries.
pub struct AppendVec<T> {
    chunks: [AtomicPtr<MaybeUninit<T>>; CHUNKS],
    len: AtomicU32,
}

impl<T> AppendVec<T> {
    pub fn new() -> Self {
        AppendVec {
            chunks: std::array::from_fn(|_| AtomicPtr::new(std::ptr::null_mut())),
            len: AtomicU32::new(0),
        }
    }

    #[inline]
    fn locate(idx: u32) -> (usize, usize) {
        let x = idx as u64 + (1u64 << FIRST_CHUNK_BITS);
        let k = 63 - x.leading_zeros() - FIRST_CHUNK_BITS;
        (k as usize, (x - (1u64 << (k + FIRST_CHUNK_BITS))) as usize)
    }

    pub fn push(&self, v: T) -> u32 {
        let idx = self.len.fetch_add(1, Ordering::Relaxed);
        let (k, off) = Self::locate(idx);
        let mut chunk = self.chunks[k].load(Ordering::Acquire);
        if chunk.is_null() {
            let size = 1usize << (k as u32 + FIRST_CHUNK_BITS);
            let fresh = Box::into_raw(Box::<[T]>::new_uninit_slice(size)) as *mut MaybeUninit<T>;
            match self.chunks[k].compare_exchange(
                std::ptr::null_mut(),
                fresh,
                Ordering::AcqRel,
                Ordering::Acquire,
            ) {
                Ok(_) => chunk = fresh,
                Err(existing) => {
                    // SAFETY: `fresh` came from `Box::into_raw` of `size` uninitialized slots
                    // and was never shared.
                    drop(unsafe { Box::from_raw(std::ptr::slice_from_raw_parts_mut(fresh, size)) });
                    chunk = existing;
                }
            }
        }
        // SAFETY: `idx` belongs to this call alone and lies within chunk `k`.
        unsafe { (*chunk.add(off)).write(v) };
        idx
    }

    /// The value at `idx`. Only ids returned by `push` may be passed.
    #[inline]
    pub fn get(&self, idx: u32) -> &T {
        let (k, off) = Self::locate(idx);
        let chunk = self.chunks[k].load(Ordering::Acquire);
        // SAFETY: an id exists only after `push` wrote its slot, and the thread holding it
        // synchronized with that write; slots are never moved or freed.
        unsafe { (*chunk.add(off)).assume_init_ref() }
    }

    pub fn len(&self) -> u32 {
        self.len.load(Ordering::Relaxed)
    }
}

impl<T> Default for AppendVec<T> {
    fn default() -> Self {
        Self::new()
    }
}

pub struct Interner<T> {
    shards: [Mutex<hashbrown::HashTable<u32>>; SHARDS],
    items: AppendVec<T>,
}

fn hash_of<T: Hash>(v: &T) -> u64 {
    rustc_hash::FxBuildHasher.hash_one(v)
}

impl<T: Hash + Eq> Interner<T> {
    pub fn new() -> Self {
        Interner {
            shards: std::array::from_fn(|_| Mutex::new(hashbrown::HashTable::new())),
            items: AppendVec::new(),
        }
    }

    pub fn intern(&self, v: T) -> u32 {
        let hash = hash_of(&v);
        let shard = &self.shards[(hash >> 52) as usize % SHARDS];
        let mut table = shard.lock().unwrap_or_else(|e| e.into_inner());
        let items = &self.items;
        if let Some(&idx) = table.find(hash, |&idx| *items.get(idx) == v) {
            return idx;
        }
        let idx = items.push(v);
        table.insert_unique(hash, idx, |&idx| hash_of(items.get(idx)));
        idx
    }

    #[inline]
    pub fn get(&self, idx: u32) -> &T {
        self.items.get(idx)
    }
}

impl<T: Hash + Eq> Default for Interner<T> {
    fn default() -> Self {
        Self::new()
    }
}
