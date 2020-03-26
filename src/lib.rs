#![no_std]

extern crate alloc;

use alloc::{boxed::Box, vec, vec::Vec};
use core::{cell::RefCell, marker::PhantomData, mem::MaybeUninit, ops, ptr::NonNull};

pub struct Stadium<'a, T> {
    buckets: RefCell<Vec<Bucket<T>>>,
    default_capacity: usize,
    __lifetime: PhantomData<&'a ()>,
}

impl<'a, T: Sized> Stadium<'a, T> {
    #[inline]
    pub fn with_capacity(capacity: usize) -> Self {
        assert!(capacity > 0);

        Self {
            buckets: RefCell::new(vec![Bucket::with_capacity(capacity)]),
            default_capacity: capacity,
            __lifetime: PhantomData,
        }
    }

    #[inline]
    pub fn alloc(&mut self, item: T) -> Ticket<'a, T> {
        let mut buckets = self.buckets.borrow_mut();

        // TODO: Maybe use a try_borrow just in case?
        let needs_alloc = if let Some(latest) = buckets.last() {
            latest.is_full()
        } else {
            true
        };

        if needs_alloc {
            buckets.push(Bucket::with_capacity(self.default_capacity));
        }

        let ptr = buckets
            .last_mut()
            .unwrap_or_else(|| unreachable!())
            .push(item)
            .unwrap_or_else(|| unreachable!());

        Ticket::new(ptr)
    }
}

impl<'a, T: Clone> Stadium<'a, T> {
    pub fn alloc_slice(&mut self, slice: &[T]) -> Ticket<'a, [T]> {
        let mut buckets = self.buckets.borrow_mut();

        // TODO: Maybe use a try_borrow just in case?
        let needs_alloc = if let Some(latest) = buckets.last() {
            latest.is_full()
        } else {
            true
        };

        if needs_alloc {
            buckets.push(Bucket::with_capacity(self.default_capacity));
        }

        let ptr = buckets
            .last_mut()
            .unwrap_or_else(|| unreachable!())
            .push_slice(slice)
            .unwrap_or_else(|| unreachable!());

        Ticket::new(ptr)
    }
}

impl<'a> Stadium<'a, u8> {
    pub fn alloc_str(&mut self, string: &str) -> Ticket<'a, str> {
        let mut buckets = self.buckets.borrow_mut();

        // TODO: Maybe use a try_borrow just in case?
        let needs_alloc = if let Some(latest) = buckets.last() {
            latest.is_full()
        } else {
            true
        };

        if needs_alloc {
            buckets.push(Bucket::with_capacity(self.default_capacity));
        }

        let ptr = buckets
            .last_mut()
            .unwrap_or_else(|| unreachable!())
            .push_str(string)
            .unwrap_or_else(|| unreachable!());

        Ticket::new(ptr)
    }
}

struct Bucket<T> {
    index: usize,
    data: Box<[MaybeUninit<T>]>,
}

impl<T> Bucket<T> {
    #[inline]
    pub const fn is_full(&self) -> bool {
        self.index + 1 == self.data.len()
    }
}

impl<T: Sized> Bucket<T> {
    #[inline]
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            index: 0,
            data: core::iter::repeat_with(|| MaybeUninit::zeroed())
                .take(capacity)
                .collect::<Vec<_>>()
                .into_boxed_slice(),
        }
    }

    #[inline]
    pub fn push(&mut self, item: T) -> Option<NonNull<T>> {
        if self.is_full() {
            None
        } else {
            self.index += 1;
            self.data[self.index] = MaybeUninit::new(item);

            NonNull::new(self.data[self.index].as_mut_ptr())
        }
    }
}

impl<T: Clone> Bucket<T> {
    #[inline]
    pub fn push_slice(&mut self, slice: &[T]) -> Option<NonNull<[T]>> {
        if self.is_full() {
            None
        } else {
            self.index += 1;

            let raw_slice = &self.data[self.index..self.index + slice.len()]
                as *const [MaybeUninit<T>] as *mut [T];
            self.index += slice.len();

            unsafe {
                (&mut *raw_slice).clone_from_slice(slice);
            }

            NonNull::new(raw_slice)
        }
    }
}

impl Bucket<u8> {
    #[inline]
    pub fn push_str(&mut self, string: &str) -> Option<NonNull<str>> {
        if self.is_full() {
            None
        } else {
            self.index += 1;

            let slice = &self.data[self.index..self.index + string.len()]
                as *const [MaybeUninit<u8>] as *mut [u8];
            self.index += string.len();

            unsafe {
                (&mut *slice).copy_from_slice(string.as_bytes());
            }

            NonNull::new(slice as *mut str)
        }
    }
}

#[derive(Debug, Copy, Clone)]
pub struct Ticket<'a, T: ?Sized> {
    ptr: NonNull<T>,
    __lifetime: PhantomData<&'a ()>,
}

impl<'a, T: ?Sized> Ticket<'a, T> {
    pub(crate) fn new(ptr: NonNull<T>) -> Self {
        Self {
            ptr,
            __lifetime: PhantomData,
        }
    }
}

impl<'a, T: ?Sized> ops::Deref for Ticket<'a, T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        // Safety: The only pointers that should be in a Ticket are pointers into a
        // live stadium.
        unsafe { self.ptr.as_ref() }
    }
}

impl<'a, T: ?Sized> ops::DerefMut for Ticket<'a, T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        // Safety: The only pointers that should be in a Ticket are pointers into a
        // live stadium.
        unsafe { self.ptr.as_mut() }
    }
}

#[test]
fn test() {
    let mut stadium = Stadium::with_capacity(100);

    for _ in 0..200 {
        let one = stadium.alloc(10_000usize);

        assert_eq!(&*one, &10_000usize);

        assert_eq!(&*stadium.alloc(10_000usize), &10_000usize);

        let two = stadium.alloc(10_000usize);

        assert_eq!(&*two, &10_000usize);
    }
}
