#![feature(result_contains_err)]
#![feature(atomic_from_mut)]
#![feature(array_methods)]

#![allow(dead_code)]

use std::{fmt, hint};
use std::sync::atomic::{fence, AtomicU32, Ordering};

mod memzone;

use crate::memzone::{Memzone, MemzoneError};

pub mod flags {
    pub const SP_ENQ: u32 = 0x0001;
    pub const SC_DEQ: u32 = 0x0002;
    pub const EXACT_SZ: u32 = 0x0004;
}

#[derive(Debug, PartialEq)]
pub enum Error {
    InvalidIntialCount,
    DequeueFromEmptyRing,
    Alloc(MemzoneError),
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum SyncType {
    MultiThread,
    SingleThread,
}

#[derive(Debug, PartialEq)]
pub enum Behavior {
    QueueFixed,
}

struct HeadTail {
    head: u32,
    tail: u32,
    sync_type: SyncType,
}

impl HeadTail {
    fn new(st: SyncType) -> Self {

        Self { head: 0, tail: 0, sync_type: st }
    }

    fn new_producer(flags: u32) -> Self {
        let st = if flags & flags::SP_ENQ != 0 {
            SyncType::SingleThread
        } else {
            SyncType::MultiThread
        };
        HeadTail::new(st)
    }

    fn new_consumer(flags: u32) -> Self {
        let st = if flags & flags::SC_DEQ != 0 {
            SyncType::SingleThread
        } else { SyncType::MultiThread
        };
        HeadTail::new(st)
    }

    fn reset(&mut self) {
        self.head = 0;
        self.tail = 0;
    }

    fn update_tail(&mut self, old_val: u32, new_val: u32, sync_type: SyncType) {
        let tail = AtomicU32::from_mut(&mut self.tail);
        if sync_type == SyncType::MultiThread {
            while tail.load(Ordering::Relaxed) != old_val {
                hint::spin_loop();
            }
        }
        tail.store(new_val, Ordering::Release);
    }
}

struct Ring<T>
    where T: Default + Copy
{

    flags: u32,
    size: u32,
    mask: u32,
    capacity: u32,

    prod: HeadTail,
    cons: HeadTail,

    mem: Memzone<T>,
}

impl<T> Ring<T>
    where T: Default + Copy
{

    pub const SIZE_MASK: u32 = 0x7fffffffu32;

    pub fn new(mut count: u32, flags: u32) -> Result<Self, Error> {
        let capacity: u32;
        if flags & flags::EXACT_SZ != 0 {
            capacity = count;
            count = (count + 1).next_power_of_two();
        } else {
            if !count.is_power_of_two() || count > Self::SIZE_MASK {
                return Err(Error::InvalidIntialCount);
            }
            capacity = count - 1;
        }

        let mem = Memzone::<T>::new(count as usize).map_err(|e| Error::Alloc(e))?;
        Ok(Self {
            flags: flags,
            size: count,
            mask: count - 1,
            capacity: capacity,
            prod: HeadTail::new_producer(flags),
            cons: HeadTail::new_consumer(flags),
            mem: mem,
        })
    }

    pub fn count(&self) -> u32 {
        let prod_tail = self.prod.tail;
        let cons_tail = self.cons.tail;
        let count = (prod_tail - cons_tail) & self.mask;
        if count > self.capacity {
            self.capacity
        } else {
            count
        }
    }

    pub fn free_count(&self) -> u32 {
        // TODO: test
        self.capacity - self.count()
    }

    pub fn full(&self) -> bool {
        // TODO: test
        self.free_count() == 0
    }

    pub fn empty(&self) -> bool {
        // TODO: test
        self.prod.tail == self.cons.tail
    }

    pub fn capacity(&self) -> u32 {
        self.capacity
    }

    pub fn reset(&mut self) {
        // TODO: test
        self.prod.reset();
        self.cons.reset();
    }

    pub fn enqueue(&mut self, el: T) -> bool {
        self.enqueue_bulk(std::slice::from_ref(&el))
    }

    pub fn enqueue_bulk(&mut self, els: &[T]) -> bool {
        match self.prod.sync_type {
            SyncType::MultiThread => self.enqueue_bulk_sp(els),
            SyncType::SingleThread => self.enqueue_bulk_mp(els),
        }
    }

    pub fn enqueue_bulk_mp(&mut self, els: &[T]) -> bool {
        self.enqueue_bulk_impl(els, SyncType::MultiThread)
    }

    pub fn enqueue_bulk_sp(&mut self, els: &[T]) -> bool {
        self.enqueue_bulk_impl(els, SyncType::SingleThread)
    }

    fn enqueue_bulk_impl(&mut self, els: &[T], st: SyncType) -> bool {
        let (n, prod_head, prod_next) = self.move_prod_head(els.len() as u32, st, Behavior::QueueFixed);
        if n == 0 {
            return false;
        }

        self.enqueue_elems(prod_head, els);

        self.prod.update_tail(prod_head, prod_next, st);
        return true;
    }

    fn move_prod_head(&mut self, mut n: u32, st: SyncType, behavior: Behavior) -> (u32, u32, u32) {
        let capacity = self.capacity;
        let max = n;

        let old_head = AtomicU32::from_mut(&mut self.prod.head).load(Ordering::Relaxed);
        let mut new_head: u32;
        loop {
            /* Reset n to the initial burst count */
            n = max;

            /* Ensure the head is read before tail */
            fence(Ordering::Acquire);

            /* load-acquire synchronize with store-release of ht->tail
            * in update_tail.
            */
            let cons_tail = AtomicU32::from_mut(&mut self.cons.tail).load(Ordering::Acquire);

            /* The subtraction is done between two unsigned 32bits value
            * (the result is always modulo 32 bits even if we have
            * *old_head > cons_tail). So 'free_entries' is always between 0
            * and capacity (which is < size).
            */
            let free_entries: u32 = capacity + cons_tail - old_head;

            /* check that we have enough room in ring */
            if n > free_entries {
                n = if behavior == Behavior::QueueFixed {
                    0
                } else {
                    free_entries
                }
            }

            if n == 0 {
                return (0, 0, 0);
            }

            new_head = old_head + n;
            let success = if st == SyncType::SingleThread {
                self.prod.head = new_head;
                true
            } else {
                /* on failure, *old_head is updated */
                AtomicU32::from_mut(&mut self.prod.head)
                    .compare_exchange(old_head, new_head, Ordering::Relaxed, Ordering::Relaxed)
                    .is_ok()
            };
            if success {
                break;
            }
        };
        return (n, old_head, new_head)
    }

    fn enqueue_elems(&mut self, prod_head: u32, els: &[T]) {
        unsafe { std::ptr::copy_nonoverlapping(els.as_ptr(), self.mem.as_ptr().add(prod_head as usize), els.len()); }
    }

    pub fn dequeue(&mut self) -> Option<T> {
        let mut el = std::mem::MaybeUninit::uninit();
        let mut els = unsafe { std::slice::from_raw_parts_mut(el.as_mut_ptr(), 1) };
        self.dequeue_bulk(&mut els)
            .then(|| {
                unsafe { el.assume_init() }
            })
    }

    pub fn dequeue_bulk(&mut self, els: &mut [T]) -> bool {
        match self.prod.sync_type {
            SyncType::MultiThread => self.dequeue_bulk_sc(els),
            SyncType::SingleThread => self.dequeue_bulk_mc(els),
        }
    }

    pub fn dequeue_bulk_mc(&mut self, els: &mut [T]) -> bool {
        self.dequeue_bulk_impl(els, SyncType::MultiThread)
    }

    pub fn dequeue_bulk_sc(&mut self, els: &mut [T]) -> bool {
        self.dequeue_bulk_impl(els, SyncType::SingleThread)
    }

    fn dequeue_bulk_impl(&mut self, els: &mut [T], st: SyncType) -> bool {
        let (n, cons_head, cons_next) = self.move_cons_head(els.len() as u32, st, Behavior::QueueFixed);
        if n == 0 {
            return false;
        }
        self.dequeue_elems(cons_head, els);
        self.cons.update_tail(cons_head, cons_next, st);
        return true;
    }

    fn move_cons_head(&mut self, mut n: u32, st: SyncType, behavior: Behavior) -> (u32, u32, u32) {
        let max = n;

        // Move cons.head atomically.
        let old_head = AtomicU32::from_mut(&mut self.cons.head).load(Ordering::Relaxed);
        let mut new_head: u32;
        loop {
            // Restore n as it may change every loop.
            n = max;

            // Ensure the head is read before tail.
            fence(Ordering::Acquire);

            // This load-acquire synchronize with store-release of ht->tail
            // in update_tail.
            let prod_tail = AtomicU32::from_mut(&mut self.prod.tail).load(Ordering::Acquire);

            // The subtraction is done between two unsigned 32bits value
            // (the result is always modulo 32 bits even if we have
            // cons_head > prod_tail). So 'entries' is always between 0
            // and size(ring)-1.
            let entries: u32 = prod_tail - old_head;

            // Set the actual entries for dequeue.
            if n > entries {
                n = if behavior == Behavior::QueueFixed {
                    0
                } else {
                    entries
                }
            }

            if n == 0 {
                return (0, 0, 0);
            }

            new_head = old_head + n;
            let success = if st == SyncType::SingleThread {
                self.cons.head = new_head;
                true
            } else {
                // On failure, *old_head will be updated.
                AtomicU32::from_mut(&mut self.cons.head)
                    .compare_exchange(old_head, new_head, Ordering::Relaxed, Ordering::Relaxed)
                    .is_ok()
            };
            if success {
                break;
            }
        };
        return (n, old_head, new_head)
    }

    fn dequeue_elems(&mut self, cons_head: u32, els: &mut [T]) {
        unsafe { std::ptr::copy_nonoverlapping(self.mem.as_ptr().add(cons_head as usize), els.as_mut_ptr(), els.len()); }
    }
}

impl<T> fmt::Display for Ring<T>
    where T: Default + Copy
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "ring")?;
        write!(f, "  flags={}\n", self.flags)?;
        write!(f, "  size={}\n", self.size)?;
        write!(f, "  capacity={}\n", self.capacity)?;
        write!(f, "  ct={}\n", self.cons.tail)?;
        write!(f, "  ch={}\n", self.cons.head)?;
        write!(f, "  pt={}\n", self.prod.tail)?;
        write!(f, "  ph={}\n", self.prod.head)?;
        write!(f, "  used={}\n", self.count())?;
        write!(f, "  avail={}\n", self.free_count())?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn ring_new_f(count: u32, flags: u32) -> Ring::<i32> {
        Ring::<i32>::new(count, flags).unwrap()
    }

    fn ring_new(count: u32) -> Ring::<i32> {
        ring_new_f(count, 0)
    }

    #[test]
    fn new_set_count_and_capacity() {
        let r = ring_new(4);
        assert_eq!(r.count(), 0);
        assert_eq!(r.capacity(), 3);

        let r = ring_new_f(4, flags::EXACT_SZ);
        assert_eq!(r.count(), 0);
        assert_eq!(r.capacity(), 4);
    }

    #[test]
    fn new_size_should_be_power_of_2() {
        let res = Ring::<i32>::new(3, flags::EXACT_SZ);
        assert_eq!(res.contains_err(&Error::InvalidIntialCount), false);
        let res = Ring::<i32>::new(3, 0);
        assert_eq!(res.contains_err(&Error::InvalidIntialCount), true);
    }

    #[test]
    fn new_size_should_be_limited_from_above() {
        let res = Ring::<i32>::new(Ring::<i32>::SIZE_MASK + 1, 0);
        assert_eq!(res.contains_err(&Error::InvalidIntialCount), true);
    }

    #[test]
    fn enqueue_single_element_chages_size() {
        let mut r = ring_new(4);
        assert_eq!(r.enqueue(1), true);
        assert_eq!(r.count(), 1);
        assert_eq!(r.capacity(), 3);
    }

    #[test]
    fn enqueue_bulk() {
        let mut r = ring_new(4);
        assert_eq!(r.enqueue_bulk(&[1, 2, 3]), true);
        assert_eq!(r.count(), 3);
    }

    #[test]
    fn reset() {
        let mut r = ring_new(4);
        assert_eq!(r.enqueue_bulk(&[1, 2]), true);
        assert_eq!(r.count(), 2);

        r.reset();

        assert_eq!(r.count(), 0);
        assert_eq!(r.capacity(), 3);
    }

    #[test]
    fn dequeue_from_empty_ring_raise_error() {
        let mut r = ring_new(4);

        assert_eq!(r.dequeue(), None);
    }

    #[test]
    fn enqueue_dequeue() {
        let mut r = ring_new(4);
        r.enqueue(5);

        let res = r.dequeue();

        assert_eq!(res, Some(5));
    }

    #[test]
    fn enqueue_dequeue_bulk() {
        let mut r = ring_new(4);
        assert_eq!(r.enqueue_bulk(&[2, 3]), true);
        let mut els = [0; 2];
        assert_eq!(r.dequeue_bulk(&mut els), true);
        assert_eq!(vec![2, 3], els);
    }
}
