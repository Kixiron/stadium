#![no_std]

extern crate alloc;

use alloc::{boxed::Box, vec, vec::Vec};
use core::{cell::RefCell, marker::PhantomData, mem::MaybeUninit, ops, ptr::NonNull};

pub struct Stadium<'a, T: Sized> {
    buckets: RefCell<Vec<Bucket<T>>>,
    default_capacity: usize,
    __lifetime: PhantomData<&'a ()>,
}

impl<'a, T: Sized> Stadium<'a, T> {
    #[inline]
    pub fn with_capacity(capacity: usize) -> Self {
        assert!(capacity > 0);
        debug_assert!(capacity < u16::max_value() as usize);

        Self {
            buckets: RefCell::new(vec![Bucket::with_capacity(capacity)]),
            default_capacity: capacity,
            __lifetime: PhantomData,
        }
    }

    #[inline]
    pub fn alloc(&self, item: T) -> Ticket<T> {
        // TODO: Maybe use a try_borrow just in case?
        let needs_alloc = if let Some(latest) = self.buckets.borrow().last() {
            latest.is_full()
        } else {
            true
        };

        if needs_alloc {
            self.buckets
                .borrow_mut()
                .push(Bucket::with_capacity(self.default_capacity));
        }

        let ptr = self
            .buckets
            .borrow_mut()
            .last_mut()
            .unwrap_or_else(|| unreachable!())
            .push(item)
            .unwrap_or_else(|| unreachable!());

        Ticket::new(ptr)
    }
}

struct Bucket<T: Sized> {
    index: usize,
    data: Box<[MaybeUninit<T>]>,
}

impl<T: Sized> Bucket<T> {
    #[inline]
    pub const fn is_full(&self) -> bool {
        self.index + 1 == self.data.len()
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

    #[inline]
    pub fn with_capacity(capacity: usize) -> Self {
        debug_assert!(capacity < u16::max_value() as usize);

        Self {
            index: 0,
            data: core::iter::repeat_with(|| MaybeUninit::zeroed())
                .take(capacity)
                .collect::<Vec<_>>()
                .into_boxed_slice(),
        }
    }
}

#[derive(Debug, Copy, Clone)]
pub struct Ticket<'a, T> {
    ptr: NonNull<T>,
    __lifetime: PhantomData<&'a T>,
}

impl<'a, T> Ticket<'a, T> {
    pub(crate) fn new(ptr: NonNull<T>) -> Self {
        Self {
            ptr,
            __lifetime: PhantomData,
        }
    }
}

impl<'a, T> ops::Deref for Ticket<'a, T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        // Safety: The only pointers that should be in a Ticket are pointers into a
        // live stadium.
        unsafe { self.ptr.as_ref() }
    }
}

#[test]
fn test() {
    let stadium = Stadium::with_capacity(100);

    for _ in 0..200 {
        let one = stadium.alloc(10_000usize);

        assert_eq!(&*one, &10_000usize);

        assert_eq!(&*stadium.alloc(10_000usize), &10_000usize);

        let two = stadium.alloc(10_000usize);

        assert_eq!(&*two, &10_000usize);
    }
}
