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

    pub fn as_ptr(&mut self) -> *mut T {
        self.addr.as_ptr()
    }
}

#[cfg(test)]
mod tests {
    // @todo
}
