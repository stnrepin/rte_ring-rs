//! Wrapper around raw pointer.

use std::alloc::{alloc, Layout};
use std::ptr::NonNull;

#[derive(Debug, PartialEq)]
pub enum MemzoneError {
    InvalidLayout,
    AllocReturnedNull,
}

pub struct Memzone<T> {
    len: usize,
    addr: NonNull<T>,
}

impl<T> Memzone<T> {
    pub fn new(len: usize) -> Result<Self, MemzoneError> {
        let layout = match Layout::array::<T>(len) {
            Ok(layout) => layout,
            Err(_) => return Err(MemzoneError::InvalidLayout),
        };

        let ptr = unsafe { alloc(layout) };
        if ptr.is_null() {
            return Err(MemzoneError::AllocReturnedNull);
        }

        Ok(Self {
            len: len,
            addr: unsafe { NonNull::new_unchecked(ptr.cast()) },
        })
    }

    pub fn len(&self) -> usize {
        self.len
    }

    pub unsafe fn as_ptr_at(&self, pos: usize) -> *const T {
        self.addr.as_ptr().add(pos)
    }

    pub unsafe fn as_mut_ptr_at(&self, pos: usize) -> *mut T {
        self.addr.as_ptr().add(pos).as_mut().unwrap()
    }

    // Все методы должны быть immutable
    pub fn read_at(&self, pos: usize, els: &mut [T]) {
        unsafe {
            std::ptr::copy_nonoverlapping(self.as_ptr_at(pos), els.as_mut_ptr(), els.len());
        }
    }

    pub fn write_at(&self, pos: usize, els: &[T]) {
        #[cfg(debug_assertions)]
        if pos > self.len() {
            panic!("invalid write at {} (len={})", pos, self.len());
        }

        unsafe {
            std::ptr::copy_nonoverlapping(els.as_ptr(), self.as_mut_ptr_at(pos), els.len());
        }
    }
}

#[cfg(test)]
mod tests {
    // @todo
}
