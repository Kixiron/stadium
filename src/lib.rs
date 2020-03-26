#![no_std]

//! A small `no_std` arena allocator

extern crate alloc;

use alloc::{
    alloc::{alloc, dealloc, Layout},
    vec::Vec,
};
use core::{
    fmt,
    marker::PhantomData,
    mem,
    num::NonZeroUsize,
    ops::Deref,
    ptr::{self, NonNull},
    slice,
};

pub struct Stadium<'a, T: Sized> {
    buckets: Vec<Bucket<T>>,
    capacity: NonZeroUsize,
    __lifetime: PhantomData<&'a ()>,
}

impl<'a, T: Sized> Stadium<'a, T> {
    #[inline]
    pub fn with_capacity(capacity: NonZeroUsize) -> Self {
        Self {
            // Leave space for a single bucket
            buckets: Vec::with_capacity(1),
            capacity,
            __lifetime: PhantomData,
        }
    }

    #[inline]
    pub fn alloc(&mut self, item: T) -> Ticket<'a, T> {
        if let Some(bucket) = self.buckets.last_mut().filter(|bucket| !bucket.is_full()) {
            return bucket.push(item);
        }

        let mut bucket = Bucket::with_capacity(self.capacity);

        let ticket = bucket.push(item);
        self.buckets.push(bucket);

        ticket
    }

    #[inline]
    pub fn alloc_slice(&mut self, slice: &[T]) -> Ticket<'a, [T]> {
        if let Some(bucket) = self.buckets.last_mut().filter(|bucket| !bucket.is_full()) {
            return bucket.push_slice(slice);
        }

        let mut bucket = Bucket::with_capacity(self.capacity);

        let ticket = bucket.push_slice(slice);
        self.buckets.push(bucket);

        ticket
    }
}

impl<'a> Stadium<'a, u8> {
    #[inline]
    pub fn alloc_str(&mut self, string: &str) -> Ticket<'a, str> {
        if let Some(bucket) = self.buckets.last_mut().filter(|bucket| !bucket.is_full()) {
            return bucket.push_str(string);
        }

        let mut bucket = Bucket::with_capacity(self.capacity);

        let ticket = bucket.push_str(string);
        self.buckets.push(bucket);

        ticket
    }
}

struct Bucket<T: Sized> {
    index: usize,
    items: NonNull<T>,
    capacity: NonZeroUsize,
}

impl<T: Sized> Drop for Bucket<T> {
    fn drop(&mut self) {
        unsafe {
            let items = self.items.as_ptr();
            for i in 0..self.index {
                ptr::drop_in_place(items.add(i));
            }

            dealloc(
                items as *mut u8,
                Layout::from_size_align_unchecked(
                    mem::size_of::<T>() * self.capacity.get(),
                    mem::align_of::<T>(),
                ),
            );
        }
    }
}

impl<T: Sized> Bucket<T> {
    #[inline]
    pub fn with_capacity(capacity: NonZeroUsize) -> Self {
        unsafe {
            let layout = Layout::from_size_align_unchecked(
                mem::size_of::<T>() * capacity.get(),
                mem::align_of::<T>(),
            );

            Self {
                index: 0,
                capacity: capacity.clone(),
                items: NonNull::new(alloc(layout))
                    .expect("Bucket alloc out of memory")
                    .cast(),
            }
        }
    }

    #[inline]
    pub const fn is_full(&self) -> bool {
        self.index == self.capacity.get()
    }

    #[inline]
    pub fn push<'a>(&mut self, item: T) -> Ticket<'a, T> {
        debug_assert!(!self.is_full());

        unsafe {
            let ptr = self.items.as_ptr().add(self.index);
            ptr.write(item);

            self.index += 1;

            Ticket {
                ptr: NonNull::new_unchecked(ptr),
                _lifetime: PhantomData,
            }
        }
    }

    #[inline]
    pub fn push_slice<'a>(&mut self, slice: &[T]) -> Ticket<'a, [T]> {
        debug_assert!(!self.is_full());
        assert!(slice.len() < self.capacity.get() - self.index);

        unsafe {
            let ptr = self.items.as_ptr().add(self.index);
            ptr::copy_nonoverlapping(slice.as_ptr(), ptr, slice.len());

            self.index += slice.len();

            let slice_ptr = slice::from_raw_parts_mut(ptr, slice.len()) as *mut [T];
            Ticket {
                ptr: NonNull::new_unchecked(slice_ptr),
                _lifetime: PhantomData,
            }
        }
    }
}

impl Bucket<u8> {
    #[inline]
    pub fn push_str<'a>(&mut self, string: &str) -> Ticket<'a, str> {
        debug_assert!(!self.is_full());

        let bytes = string.as_bytes();
        assert!(bytes.len() < self.capacity.get() - self.index);

        unsafe {
            let ptr = self.items.as_ptr().add(self.index);
            ptr::copy_nonoverlapping(bytes.as_ptr(), ptr, bytes.len());

            self.index += bytes.len();

            let slice_ptr = slice::from_raw_parts_mut(ptr, bytes.len()) as *mut [u8] as *mut str;
            Ticket {
                ptr: NonNull::new_unchecked(slice_ptr),
                _lifetime: PhantomData,
            }
        }
    }
}

#[derive(Copy, Clone)]
pub struct Ticket<'a, T: ?Sized> {
    ptr: NonNull<T>,
    _lifetime: PhantomData<&'a T>,
}

impl<T> fmt::Pointer for Ticket<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:p}", self.ptr)
    }
}

impl<T: fmt::Debug> fmt::Debug for Ticket<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", &*self)
    }
}

impl<T: fmt::Display> fmt::Display for Ticket<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", &*self)
    }
}

impl<T: PartialEq> PartialEq for Ticket<'_, T> {
    fn eq(&self, other: &Ticket<'_, T>) -> bool {
        &*self == &*other
    }
}

impl<T: Eq> Eq for Ticket<'_, T> {}

impl<'a, T> Deref for Ticket<'a, T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        unsafe { self.ptr.as_ref() }
    }
}

impl<'a, T> Deref for Ticket<'a, [T]> {
    type Target = [T];

    fn deref(&self) -> &Self::Target {
        unsafe { self.ptr.as_ref() }
    }
}

impl<'a> Deref for Ticket<'a, str> {
    type Target = str;

    fn deref(&self) -> &Self::Target {
        unsafe { self.ptr.as_ref() }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn works() {
        let mut stadium = Stadium::with_capacity(NonZeroUsize::new(100).unwrap());

        for _ in 0..200 {
            let one = stadium.alloc(10_000usize);
            assert_eq!(&*one, &10_000usize);

            assert_eq!(&*stadium.alloc(10_000usize), &10_000usize);

            let two = stadium.alloc(10_000usize);
            assert_eq!(&*two, &10_000usize);
        }
    }

    #[test]
    fn slice() {
        let mut stadium: Stadium<i32> = Stadium::with_capacity(NonZeroUsize::new(10).unwrap());

        let slice = stadium.alloc_slice(&[100, 200, 300, 400]);

        assert_eq!(&*slice, &[100, 200, 300, 400]);
    }

    #[test]
    fn string() {
        let mut stadium = Stadium::with_capacity(NonZeroUsize::new(10).unwrap());

        let slice = stadium.alloc_str("test");

        assert_eq!(&*slice, "test");
    }
}
