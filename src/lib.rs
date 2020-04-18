//! A small `no_std` arena allocator
#![no_std]

extern crate alloc;

use alloc::{
    alloc::{alloc, dealloc, Layout},
    vec::Vec,
};
use core::{
    cell::RefCell,
    cmp, fmt, hash,
    marker::PhantomData,
    mem,
    num::NonZeroUsize,
    ops::Deref,
    ptr::{self, NonNull},
    slice,
};

/// An arena allocator that dynamically grows in size when needed, allocating memory in large chunks
pub struct Stadium<'a, T: Sized> {
    /// All the internal buckets, storing all allocated and unallocated items
    buckets: RefCell<Vec<Bucket<T>>>,
    /// The default capacity of each bucket
    capacity: NonZeroUsize,
    __lifetime: PhantomData<&'a T>,
}

impl<'a, T: Sized> Stadium<'a, T> {
    /// Create a new stadium with the default bucket size of 1024 items
    ///
    /// Note: When used with ZSTs, the bucket size will always be 1
    ///
    #[inline]
    pub fn new() -> Self {
        let capacity = if mem::size_of::<T>() == 0 {
            // Only make buckets of size 1 for zsts
            unsafe { NonZeroUsize::new_unchecked(1) }
        } else {
            unsafe { NonZeroUsize::new_unchecked(1024) }
        };

        Self {
            // Leave space for a single bucket
            buckets: RefCell::new(Vec::with_capacity(1)),
            capacity,
            __lifetime: PhantomData,
        }
    }

    /// Create a new stadium with a custom bucket size
    ///
    /// Note: When used with ZSTs, the bucket size will always be 1
    ///
    #[inline]
    pub fn with_capacity(capacity: NonZeroUsize) -> Self {
        let capacity = if mem::size_of::<T>() == 0 {
            // Only make buckets of size 1 for zsts
            unsafe { NonZeroUsize::new_unchecked(1) }
        } else {
            capacity
        };

        Self {
            // Leave space for a single bucket
            buckets: RefCell::new(Vec::with_capacity(1)),
            capacity,
            __lifetime: PhantomData,
        }
    }

    /// Store an item in the stadium
    #[inline]
    pub fn store(&'a self, item: T) -> Ticket<'a, T> {
        // Return aligned but dangling tickets for zsts
        if mem::size_of::<T>() == 0 {
            return Ticket::dangling();
        }

        let mut buckets = self.buckets.borrow_mut();

        // TODO: If a large slice is stored that requires a new bucket, all remaining items in the preceding bucket will
        //       never be used and are effectively leaked, how to solve this without losing speed
        if let Some(bucket) = buckets.last_mut().filter(|bucket| !bucket.is_full()) {
            // Safety: The found bucket isn't empty and therefore has room for an item
            return unsafe { bucket.push(item) };
        }

        let mut bucket = Bucket::with_capacity(self.capacity);

        // Safety: The new bucket has room for an item
        let ticket = unsafe { bucket.push(item) };
        buckets.push(bucket);

        ticket
    }

    /// Store a slice in the stadium
    #[inline]
    pub fn store_slice(&'a self, slice: &[T]) -> Ticket<'a, [T]> {
        // Return aligned but dangling tickets for empty slices
        if slice.is_empty() {
            return Ticket::dangling_slice();
        }

        let mut buckets = self.buckets.borrow_mut();

        if let Some(bucket) = buckets
            .last_mut()
            .filter(|bucket| bucket.free_elements() >= slice.len())
        {
            // Safety: The bucket found has enough room for the slice
            return unsafe { bucket.push_slice(slice) };
        }

        // Safety: Slices of length 0 have already been handled
        let mut bucket = Bucket::with_capacity(cmp::max(self.capacity, unsafe {
            NonZeroUsize::new_unchecked(slice.len())
        }));

        // Safety: The new bucket will have enough room for the slice
        let ticket = unsafe { bucket.push_slice(slice) };
        buckets.push(bucket);

        ticket
    }
}

impl<'a> Stadium<'a, u8> {
    /// Store a string in the stadium
    #[inline]
    pub fn store_str(&'a self, string: &str) -> Ticket<'a, str> {
        let len = if string.is_empty() {
            // Return aligned but dangling tickets for empty strings
            return Ticket::dangling_str();
        } else {
            string.as_bytes().len()
        };

        let mut buckets = self.buckets.borrow_mut();

        if let Some(bucket) = buckets
            .last_mut()
            .filter(|bucket| bucket.free_elements() >= len)
        {
            // Safety: The bucket found has enough room for the string
            return unsafe { bucket.push_str(string) };
        }

        // Safety: Strings of length 0 have already been handled
        let mut bucket = Bucket::with_capacity(cmp::max(self.capacity, unsafe {
            NonZeroUsize::new_unchecked(len)
        }));

        // Safety: The new bucket will have enough room for the string
        let ticket = unsafe { bucket.push_str(string) };
        buckets.push(bucket);

        ticket
    }
}

impl<'a, T> Default for Stadium<'a, T> {
    fn default() -> Self {
        Self::new()
    }
}

/// A bucket to hold a number of stored items
struct Bucket<T: Sized> {
    /// The start of uninitialized memory within `items`
    index: usize,
    /// A pointer to the start of the data
    items: NonNull<T>,
    /// The total number of Ts that can be stored
    capacity: NonZeroUsize,
}

impl<T: Sized> Drop for Bucket<T> {
    fn drop(&mut self) {
        // Safety: Only valid items are dropped, and then all memory is deallocated.
        // All pointers are valid.
        unsafe {
            let items = self.items.as_ptr();

            // Drop all initialized items
            for i in 0..self.index {
                ptr::drop_in_place(items.add(i));
            }

            // Deallocate all memory that the bucket allocated
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
    /// Allocates a bucket with space for `capacity` items
    #[inline]
    pub(crate) fn with_capacity(capacity: NonZeroUsize) -> Self {
        unsafe {
            let layout = Layout::from_size_align_unchecked(
                mem::size_of::<T>() * capacity.get(),
                mem::align_of::<T>(),
            );

            Self {
                index: 0,
                capacity: capacity.clone(),
                items: NonNull::new(alloc(layout))
                    .expect("Failed to allocate a new bucket, process out of memory")
                    .cast(),
            }
        }
    }

    /// Get the number of avaliable slots for the current bucket
    #[inline]
    pub(crate) const fn free_elements(&self) -> usize {
        self.capacity.get() - self.index
    }

    /// Returns whether the current bucket is full
    #[inline]
    pub(crate) const fn is_full(&self) -> bool {
        self.index == self.capacity.get()
    }

    /// Push an element to the current bucket, returning a pointer to it
    ///
    /// # Safety
    ///
    /// The current bucket must not be full
    ///
    #[inline]
    pub(crate) unsafe fn push<'a>(&mut self, item: T) -> Ticket<'a, T> {
        debug_assert!(!self.is_full());

        let ptr = self.items.as_ptr().add(self.index);
        ptr.write(item);

        self.index += 1;

        // Safety: The pointer is not null and points to valid internal memory
        Ticket::new(NonNull::new_unchecked(ptr))
    }

    /// Push a slice to the current bucket, returning a pointer to it
    ///
    /// # Safety
    ///
    /// The current bucket must have room for all elements of the slice
    ///
    #[inline]
    pub(crate) unsafe fn push_slice<'a>(&mut self, slice: &[T]) -> Ticket<'a, [T]> {
        debug_assert!(!self.is_full());
        debug_assert!(slice.len() <= self.capacity.get() - self.index);

        let ptr = self.items.as_ptr().add(self.index);
        ptr::copy_nonoverlapping(slice.as_ptr(), ptr, slice.len());

        self.index += slice.len();

        let slice_ptr = slice::from_raw_parts_mut(ptr, slice.len()) as *mut [T];

        // Safety: The pointer is not null and points to valid internal memory
        Ticket::new(NonNull::new_unchecked(slice_ptr))
    }
}

impl Bucket<u8> {
    /// Push a string to the current bucket, returning a pointer to it
    ///
    /// # Safety
    ///
    /// The current bucket must have room for all bytes of the string
    ///
    #[inline]
    pub(crate) unsafe fn push_str<'a>(&mut self, string: &str) -> Ticket<'a, str> {
        debug_assert!(!self.is_full());

        let bytes = string.as_bytes();
        debug_assert!(bytes.len() <= self.capacity.get() - self.index);

        let ptr = self.items.as_ptr().add(self.index);
        ptr::copy_nonoverlapping(bytes.as_ptr(), ptr, bytes.len());

        self.index += bytes.len();

        let str_ptr = slice::from_raw_parts_mut(ptr, bytes.len()) as *mut [u8] as *mut str;

        // Safety: The pointer is not null and points to valid internal memory
        Ticket::new(NonNull::new_unchecked(str_ptr))
    }
}

/// A reference to an item stored in a [`Stadium`]
///
/// [`Stadium`]: crate::Stadium
#[derive(Copy, Clone)]
pub struct Ticket<'a, T: ?Sized> {
    ptr: NonNull<T>,
    __lifetime: PhantomData<&'a T>,
}

impl<'a, T: ?Sized> Ticket<'a, T> {
    /// Create a new `Ticket` from a `NonNull` pointer
    ///
    /// # Safety
    ///
    /// The given pointer must be valid and well aligned. For ZSTs, use
    /// [`dangling`], [`dangling_slice`] or [`dangling_str`]
    ///
    /// [`dangling`]: crate::Ticket::dangling
    /// [`dangling_slice`]: crate::Ticket::dangling_slice
    /// [`dangling_str`]: crate::Ticket::dangling_str
    pub(crate) const unsafe fn new(ptr: NonNull<T>) -> Self {
        Self {
            ptr,
            __lifetime: PhantomData,
        }
    }
}

impl<'a, T> Ticket<'a, T> {
    /// Create a dangling but well aligned `Ticket`
    pub(crate) const fn dangling() -> Self {
        Self {
            ptr: NonNull::dangling(),
            __lifetime: PhantomData,
        }
    }

    /// Create a dangling but well aligned `Ticket` slice
    pub(crate) fn dangling_slice() -> Ticket<'a, [T]> {
        Ticket {
            ptr: unsafe {
                NonNull::new_unchecked(NonNull::<[T; 0]>::dangling().as_ptr() as *mut [T])
            },
            __lifetime: PhantomData,
        }
    }
}

impl<'a> Ticket<'a, str> {
    /// Create a dangling but well aligned `Ticket` str
    pub(crate) fn dangling_str() -> Ticket<'a, str> {
        Ticket {
            ptr: unsafe {
                NonNull::new_unchecked(
                    NonNull::<[u8; 0]>::dangling().as_ptr() as *mut [u8] as *mut str
                )
            },
            __lifetime: PhantomData,
        }
    }
}

impl<T: fmt::Debug> fmt::Debug for Ticket<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(self.deref(), f)
    }
}

impl<T: fmt::Display> fmt::Display for Ticket<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self.deref(), f)
    }
}

/// Displays the pointer to the stored data, not the underlying data
impl<T> fmt::Pointer for Ticket<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Pointer::fmt(&self.ptr, f)
    }
}

/// Displays the pointer to the stored data, not the underlying data
impl<T> fmt::LowerHex for Ticket<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::LowerHex::fmt(&(self.ptr.as_ptr() as usize), f)
    }
}

/// Displays the pointer to the stored data, not the underlying data
impl<T> fmt::UpperHex for Ticket<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::UpperHex::fmt(&(self.ptr.as_ptr() as usize), f)
    }
}

/// Displays the pointer to the stored data, not the underlying data
impl<T> fmt::Octal for Ticket<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Octal::fmt(&(self.ptr.as_ptr() as usize), f)
    }
}

/// Displays the pointer to the stored data, not the underlying data
impl<T> fmt::Binary for Ticket<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Binary::fmt(&(self.ptr.as_ptr() as usize), f)
    }
}

impl<T: fmt::LowerExp> fmt::LowerExp for Ticket<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::LowerExp::fmt(self.deref(), f)
    }
}

impl<T: fmt::UpperExp> fmt::UpperExp for Ticket<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::UpperExp::fmt(self.deref(), f)
    }
}

impl<T: PartialEq> PartialEq for Ticket<'_, T> {
    fn eq(&self, other: &Ticket<'_, T>) -> bool {
        self.deref() == other.deref()
    }
}

impl<T: Eq> Eq for Ticket<'_, T> {}

impl<T: PartialEq> PartialEq<T> for Ticket<'_, T> {
    fn eq(&self, other: &T) -> bool {
        self.deref() == other
    }
}

impl<T: PartialOrd> cmp::PartialOrd for Ticket<'_, T> {
    fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> {
        self.deref().partial_cmp(other.deref())
    }
}

impl<T: PartialOrd> cmp::PartialOrd<T> for Ticket<'_, T> {
    fn partial_cmp(&self, other: &T) -> Option<cmp::Ordering> {
        self.deref().partial_cmp(other)
    }
}

impl<T: Ord + PartialOrd> Ord for Ticket<'_, T> {
    fn cmp(&self, other: &Self) -> cmp::Ordering {
        self.deref().cmp(other.deref())
    }
}

impl<'a, T> Deref for Ticket<'a, T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        // Safety: All pointers should be valid
        unsafe { self.ptr.as_ref() }
    }
}

impl<'a, T> Deref for Ticket<'a, [T]> {
    type Target = [T];

    fn deref(&self) -> &Self::Target {
        // Safety: All pointers should be valid
        unsafe { self.ptr.as_ref() }
    }
}

impl<'a> Deref for Ticket<'a, str> {
    type Target = str;

    fn deref(&self) -> &Self::Target {
        // Safety: All pointers should be valid
        unsafe { self.ptr.as_ref() }
    }
}

impl<T: hash::Hash> hash::Hash for Ticket<'_, T> {
    fn hash<H: hash::Hasher>(&self, state: &mut H) {
        self.deref().hash(state);
    }
}

unsafe impl<T: Send> Send for Ticket<'_, T> {}
unsafe impl<T: Sync> Sync for Ticket<'_, T> {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn create_stadium() {
        let _: Stadium<Stadium<u8>> = Stadium::new();
        let _: Stadium<Stadium<u8>> = Stadium::with_capacity(NonZeroUsize::new(100).unwrap());

        struct Zst;

        let _: Stadium<Zst> = Stadium::new();
        let _: Stadium<Zst> = Stadium::with_capacity(NonZeroUsize::new(100).unwrap());
    }

    #[test]
    fn works() {
        let stadium = Stadium::new();

        for _ in 0..200 {
            let one = stadium.store(10_000usize);
            assert_eq!(&*one, &10_000usize);

            assert_eq!(&*stadium.store(10_000usize), &10_000usize);

            let two = stadium.store(10_000usize);
            assert_eq!(&*two, &10_000usize);
        }
    }

    #[test]
    fn slice() {
        let stadium: Stadium<i32> = Stadium::new();

        let slice = stadium.store_slice(&[100, 200, 300, 400]);

        assert_eq!(&*slice, &[100, 200, 300, 400]);
    }

    #[test]
    fn string() {
        let stadium = Stadium::new();

        let slice = stadium.store_str("test");

        assert_eq!(&*slice, "test");
    }

    #[test]
    fn handle_large_slice() {
        let stadium = Stadium::with_capacity(NonZeroUsize::new(10).unwrap());

        let slice: &[u64] = &[1000; 100];
        let big_slice = stadium.store_slice(slice);

        assert_eq!(&*big_slice, slice);
    }

    #[test]
    fn handle_large_str() {
        let stadium = Stadium::with_capacity(NonZeroUsize::new(10).unwrap());

        let string: &str = "really really really really really really really really really really really really really really really really long string";
        let big_string = stadium.store_str(string);

        assert_eq!(&*big_string, string);
    }

    #[test]
    fn zst() {
        #[derive(Debug, PartialEq, Eq)]
        struct Zst;

        let stadium = Stadium::new();

        let zst = stadium.store(Zst);
        let zst1 = stadium.store(Zst);
        let zst2 = stadium.store(Zst);
        let zst3 = stadium.store(Zst);

        assert_eq!(&*zst, &Zst);
        assert_eq!(&*zst1, &Zst);
        assert_eq!(&*zst2, &Zst);
        assert_eq!(&*zst3, &Zst);
    }

    #[test]
    fn zst_slice() {
        #[derive(Debug, PartialEq, Eq)]
        struct Zst;

        let stadium = Stadium::new();

        let slice: &[Zst] = &[Zst, Zst, Zst, Zst];
        let zst = stadium.store(slice);
        let zst1 = stadium.store(slice);
        let zst2 = stadium.store(slice);

        assert_eq!(&*zst, &slice);
        assert_eq!(&*zst1, &slice);
        assert_eq!(&*zst2, &slice);
    }

    #[test]
    fn empty_slice() {
        let stadium = Stadium::new();

        let slice: &[u32] = &[];
        let zst = stadium.store_slice(slice);
        let zst1 = stadium.store_slice(slice);
        let zst2 = stadium.store_slice(slice);

        assert_eq!(&*zst, slice);
        assert_eq!(&*zst1, slice);
        assert_eq!(&*zst2, slice);
    }

    #[test]
    fn empty_str() {
        let stadium = Stadium::new();

        let zst = stadium.store_str("");
        let zst1 = stadium.store_str("");
        let zst2 = stadium.store_str("");

        assert_eq!(&*zst, "");
        assert_eq!(&*zst1, "");
        assert_eq!(&*zst2, "");
    }

    #[test]
    fn trait_impls_dont_crash() {
        use alloc::format;

        let stadium = Stadium::new();
        let allocated = stadium.store(100u32);

        assert_eq!(allocated.deref(), &100u32);
        assert_eq!(allocated.deref(), allocated.deref());

        assert!(allocated.deref() < &1000u32);
        assert!(!(allocated.deref() > allocated.deref()));

        let _ = format!("{:#?}", allocated);
        let _ = format!("{:?}", allocated);
        let _ = format!("{}", allocated);
        let _ = format!("{:p}", allocated);
        let _ = format!("{:X}", allocated);
        let _ = format!("{:x}", allocated);
        let _ = format!("{:o}", allocated);
        let _ = format!("{:b}", allocated);

        let stadium = Stadium::new();
        let allocated = stadium.store(10.0f32);

        let _ = format!("{:e}", allocated);
        let _ = format!("{:E}", allocated);
    }
}
