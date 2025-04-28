// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
#![rr::import("ace.theories.page_allocator", "page")]
use crate::core::architecture::PageSize;
use crate::core::control_data::{DigestType, MeasurementDigest};
use crate::core::memory_layout::{ConfidentialMemoryAddress, MemoryLayout, NonConfidentialMemoryAddress};
use crate::error::Error;
use alloc::vec::Vec;
use core::marker::PhantomData;
use core::mem;
use core::ops::Range;

pub trait PageState {}

pub struct UnAllocated {}
pub struct Allocated {}

impl PageState for UnAllocated {}
impl PageState for Allocated {}

#[derive(Debug)]
/// Specification:
/// Mathematically, we model a `Page` as a triple `(page_loc, page_sz, page_val)`, where:
/// - `page_loc` is the start address in memory,
/// - `page_sz` is the size of the page,
/// - and `page_val` is the sequence of bytes currently stored in the page.
#[rr::refined_by("p" : "page")]

/// Invariant: As an invariant, a `Page` *exclusively owns* this memory region, and ascribes the value `v` to it.
#[rr::invariant(#type "p.(page_loc)" : "<#> p.(page_val)" @ "array_t (page_size_in_words_nat p.(page_sz)) (int usize_t)")]

/// Invariant: The page is well-formed.
#[rr::invariant("page_wf p")]

/// We require the page to be in this bounded memory region.
#[rr::invariant("(page_end_loc p).2 ≤ MAX_PAGE_ADDR")]

/// We require the memory layout to have been initialized.
#[rr::context("onceG Σ memory_layout")]
#[rr::exists("MEMORY_CONFIG")]
/// Invariant: The MEMORY_LAYOUT Once instance has been initialized to MEMORY_CONFIG.
#[rr::invariant(#iris "once_status \"MEMORY_LAYOUT\" (Some MEMORY_CONFIG)")]
/// Invariant: ...and according to that layout, this page resides in confidential memory.
#[rr::invariant("MEMORY_CONFIG.(conf_start).2 ≤ p.(page_loc).2")]
#[rr::invariant("p.(page_loc).2 + (page_size_in_bytes_nat p.(page_sz)) < MEMORY_CONFIG.(conf_end).2")]
pub struct Page<S: PageState> {
    /// Specification: the `address` has mathematical value `l`.
    #[rr::field("p.(page_loc)")]
    address: ConfidentialMemoryAddress,
    /// Specification: the `size` has mathematical value `sz`.
    #[rr::field("p.(page_sz)")]
    size: PageSize,
    /// Specification: the `_marker` has no relevance for the verification.
    #[rr::field("tt")]
    _marker: PhantomData<S>,
}

#[rr::context("onceG Σ memory_layout")]
#[rr::context("onceG Σ gname")]
impl Page<UnAllocated> {
    /// Creates a page token at the given address in the confidential memory.
    ///
    /// # Safety
    ///
    /// The caller must guarantee that he owns the memory region defined by the address and size
    /// and his ownership is given to the page token.
    ///
    /// # Specification:
    #[rr::params("l", "sz", "v", "MEMORY_CONFIG")]
    /// The mathematical values of the two arguments are a memory location `l` and a size `sz`.
    #[rr::args("l", "sz")]

    /// Precondition: We require ownership of the memory region starting at `l` for size `sz`.
    /// Moreover, `l` needs to be properly aligned for a page of size `sz`, and contain valid integers.
    #[rr::requires(#type "l" : "<#> v" @ "array_t (page_size_in_words_nat sz) (int usize_t)")]

    /// Precondition: The page needs to be sufficiently aligned.
    #[rr::requires("l `aligned_to` (page_size_align sz)")]

    /// Precondition: The page is located in a bounded memory region.
    #[rr::requires("l.2 + page_size_in_bytes_Z sz ≤ MAX_PAGE_ADDR")]

    /// Precondition: The memory layout is initialized.
    #[rr::requires(#iris "once_status \"MEMORY_LAYOUT\" (Some MEMORY_CONFIG)")]
    /// Precondition: The page is entirely contained in the confidential memory range.
    #[rr::requires("MEMORY_CONFIG.(conf_start).2 ≤ l.2")]
    #[rr::requires("l.2 + (page_size_in_bytes_nat sz) < MEMORY_CONFIG.(conf_end).2")]
    /// Then, we get a properly initialized page starting at `l` of size `sz` with some value `v`.
    #[rr::returns("mk_page l sz v")]
    pub(super) unsafe fn init(address: ConfidentialMemoryAddress, size: PageSize) -> Self {
        Self { address, size, _marker: PhantomData }
    }

    /// Specification:
    #[rr::only_spec]
    #[rr::params("p")]
    #[rr::args("p")]
    /// We return a page starting at `l` with size `sz`, but with all bytes initialized to zero.
    #[rr::returns("mk_page p.(page_loc) p.(page_sz) (zero_page p.(page_sz))")]
    pub fn zeroize(mut self) -> Page<Allocated> {
        self.clear();
        // TODO: fix automation for consuming values
        Page { address: self.address, size: self.size, _marker: PhantomData }
    }

    /// Moves a page to the Allocated state after filling its content with the
    /// content of a page located in the non-confidential memory.
    #[rr::only_spec]
    #[rr::params("v2", "MEMORY_CONFIG")]
    /// Precondition: We need to know the current memory layout.
    #[rr::requires(#iris "once_initialized π \"MEMORY_LAYOUT\" (Some MEMORY_CONFIG)")]
    /// Precondition: The region we are copying from is in non-confidential memory.
    #[rr::requires("MEMORY_CONFIG.(non_conf_start).2 ≤ address.2")]
    #[rr::requires("address.2 + page_size_in_bytes_Z self.(page_sz) ≤ MEMORY_CONFIG.(non_conf_end).2")]
    /// Precondition: We require ownership over the memory region.
    #[rr::requires(#type "address" : "<#> v2" @ "array_t (page_size_in_words_nat self.(page_sz)) (int usize_t)")]
    /// Postcondition: We return ownership over the memory region.
    #[rr::ensures(#type "address" : "<#> v2" @ "array_t (page_size_in_words_nat self.(page_sz)) (int usize_t)")]
    /// Postcondition: We get a correctly initialized page token with the copied contents.
    #[rr::returns("Ok (mk_page self.(page_loc) self.(page_sz) v2)")]
    // TODO this needs to be unsafe
    pub fn copy_from_non_confidential_memory(mut self, mut address: NonConfidentialMemoryAddress) -> Result<Page<Allocated>, Error> {
        self.offsets().into_iter().try_for_each(|offset_in_bytes| {
            let non_confidential_address = MemoryLayout::read()
                .non_confidential_address_at_offset(&mut address, offset_in_bytes)
                .map_err(|_| Error::AddressNotInNonConfidentialMemory())?;
            // TODO: describe why below unsafe block is safe in this invocation.
            let data_to_copy = unsafe { non_confidential_address.read() };
            self.write(offset_in_bytes, data_to_copy)?;
            Ok::<(), Error>(())
        })?;
        Ok(Page { address: self.address, size: self.size, _marker: PhantomData })
    }

    /// Returns a collection of all smaller pages that fit within the current page and
    /// are correctly aligned. If this page is the smallest page (4KiB for RISC-V), then
    /// the same page is returned.
    #[rr::only_spec]
    #[rr::params("x" : "memory_layout")]
    /// Precondition: The memory layout needs to have been initialized.
    #[rr::requires(#iris "once_initialized π \"MEMORY_LAYOUT\" (Some x)")]
    /// Postcondition: We get the subdivided pages.
    #[rr::returns("subdivide_page self")]
    pub fn divide(mut self) -> Vec<Page<UnAllocated>> {
        let smaller_page_size = self.size.smaller().unwrap_or(self.size);
        let number_of_smaller_pages = self.size.in_bytes() / smaller_page_size.in_bytes();
        let page_end = self.end_address_ptr();
        // NOTE: this needs the invariant to already be open
        let memory_layout = MemoryLayout::read();

        // own the memory region of the bigger token `self`

        // 1. Create a sequence 0.. number_of_smaller_pages
        // 2. Make it into an iterator
        // 3. Call map and pass the closure <- consumes ownership. How ownership is split should be specified here.
        // 4. Then consume iterator (in collect)

        (0..number_of_smaller_pages)
            // it_state = (cur_index, max_index = number_of_smaller_pages)
            // Inv := λ seq_state _,
            //            [∗ list] i ∈ seq_state.cur_index .. seq_state.max_index :
            //                  l +ₗ (i * smaller_size) ◁ₗ "<#> take smaller_size (drop (smaller_size * i) p.(page_val))" @ "array_t (int usize_t) smaller_size
            .map(
                #[rr::skip]
                #[rr::params("i", "l", "smaller_size", "bounds", "bound", "v")]
                #[rr::args("i")]
                // clos_state: (&self.address, &page_end, &smaller_page_size, ..)
                /// Capture: the start address of the big page
                #[rr::capture("self.address" : "l")]
                /// Capture: the last address in the bigger page
                #[rr::capture("page_end" : "bound")]
                /// Capture: the size of the smaller pages
                #[rr::capture("smaller_page_size" : "smaller_size")]
                /// Capture: the global memory layout
                #[rr::capture("memory_layout" : "bounds")]

                /// Precondition: the page bound is in confidential memory
                #[rr::requires("bound.2 ≤ bounds.(conf_end).2")]
                /// Precondition: the offset is within the bound
                #[rr::requires("l.2 + i * smaller_size ≤ bound.2")]

                /// Precondition: ownership of this token's memory region
                #[rr::requires(#type "l +ₗ (i * smaller_size)" : "<#> v" @ "array_t smaller_size (int usize_t)")]

                /// Postcondition: return new smaller page
                #[rr::returns("mk_page (l +ₗ (i * smaller_size)) smaller_size v")]
                |i: usize| {
                    let offset_in_bytes = i * smaller_page_size.in_bytes();

                    // Safety: below unwrap is safe because a size of a larger page is a
                    // multiply of a smaller page size, thus we will never exceed the outer page boundary.
                    let smaller_page_start =
                        memory_layout.confidential_address_at_offset_bounded(&self.address, offset_in_bytes, page_end).unwrap();
                    // Safety: The below token creation is safe because the current page owns the entire memory
                    // associated with the page and within this function it partitions this memory into smaller
                    // disjoined pages, passing the ownership to these smaller memory regions to new tokens.
                    unsafe { Page::init(smaller_page_start, smaller_page_size) }
                },
            )
            .collect()
    }

    /// Merges a collection of contiguous pages into a single correctly aligned page.
    ///
    /// # Safety
    ///
    /// * Page is aligned to the new size
    /// * Merged pages are contiguous and cover the entire new size of the future page
    /// * Merged pages are of the same size
    /// * Merged pages are sorted
    pub unsafe fn merge(mut from_pages: Vec<Page<UnAllocated>>, new_size: PageSize) -> Self {
        assert!(from_pages.len() > 2);
        assert!(from_pages[0].address.is_aligned_to(new_size.in_bytes()));
        assert!(new_size.in_bytes() / from_pages[0].size.in_bytes() == from_pages.len());
        assert!(from_pages[0].start_address() + new_size.in_bytes() == from_pages[from_pages.len() - 1].end_address());
        Self::init(from_pages.swap_remove(0).address, new_size)
    }
}

#[rr::context("onceG Σ memory_layout")]
impl Page<Allocated> {
    /// Clears the entire memory content by writing 0s to it and then converts the Page from Allocated to UnAllocated so it can be returned
    /// to the page allocator.
    #[rr::only_spec]
    #[rr::returns("mk_page self.(page_loc) self.(page_sz) (zero_page self.(page_sz))")]
    pub fn deallocate(mut self) -> Page<UnAllocated> {
        self.clear();
        Page { address: self.address, size: self.size, _marker: PhantomData }
    }

    /// Reads data of size `size_of::<usize>` from a page at a given offset. Error is returned
    /// when an offset that exceeds page size is passed as an argument.
    ///
    /// # Arguments
    ///
    /// * `offset_in_bytes` is an offset from the beginning of the page to which a chunk of data
    /// will be read from the memory. This offset must be a multiply of size_of::(usize) and be
    /// within the page address range, otherwise an Error is returned.
    ///
    /// Specification:
    #[rr::ok]
    /// Precondition: the offset needs to be divisible by the size of usize.
    #[rr::requires("H_off" : "(ly_size usize_t | offset_in_bytes)%Z")]
    /// Precondition: we need to be able to fit a usize at the offset and not exceed the page bounds
    #[rr::requires("H_sz" : "(offset_in_bytes + ly_size usize_t ≤ page_size_in_bytes_Z self.(page_sz))%Z")]
    /// Postcondition:
    #[rr::exists("off'" : "nat")]
    /// ...where off is a multiple of usize
    #[rr::ensures("(offset_in_bytes = off' * ly_size usize_t)%Z")]
    /// ...the return value has been read from `v` at offset `off'`
    #[rr::ensures("self.(page_val) !! off' = Some ret")]
    pub fn read(&self, offset_in_bytes: usize) -> Result<usize, Error> {
        ensure!(offset_in_bytes % Self::ENTRY_SIZE == 0, Error::AddressNotAligned())?;
        let data = unsafe {
            // Safety: below add results in a valid confidential memory address because
            // we ensure that it is within the page boundary and page is guaranteed to
            // be entirely inside the confidential memory.
            let pointer = self.address.add(offset_in_bytes, self.end_address_ptr())?;
            // pointer is guaranteed to be in the range <0;self.size()-size_of::(usize)>

            pointer.read_volatile()
        };
        Ok(data)
    }
}

#[rr::context("onceG Σ memory_layout")]
impl<T: PageState> Page<T> {
    pub const ENTRY_SIZE: usize = mem::size_of::<usize>();

    #[rr::returns("self.(page_loc)")]
    pub fn address(&self) -> &ConfidentialMemoryAddress {
        &self.address
    }

    #[rr::returns("self.(page_loc).2")]
    pub fn start_address(&self) -> usize {
        self.address.as_usize()
    }

    #[rr::returns("self.(page_loc).2 + page_size_in_bytes_Z self.(page_sz)")]
    pub fn end_address(&self) -> usize {
        self.address.as_usize() + self.size.in_bytes()
    }

    // NOTE: round-trip casts are difficult to verify, need support in RefinedRust
    #[rr::only_spec]
    #[rr::params("l", "sz")]
    #[rr::args(#raw "( *[l; sz; tt])")]
    #[rr::returns("l +ₗ page_size_in_bytes_Z sz")]
    pub fn end_address_ptr(&self) -> *const usize {
        // TODO: ideally, use strict-provenance API
        self.end_address() as *const usize
    }

    #[rr::returns("self.(page_sz)")]
    pub fn size(&self) -> &PageSize {
        &self.size
    }

    /// Writes data to a page at a given offset. Error is returned if an invalid offset was passed
    /// as an argument.
    ///
    /// # Arguments
    ///
    /// * `offset_in_bytes` is an offset from the beginning of the page to which a chunk of data
    /// will be written to the memory. This offset must be a multiply of size_of::(usize) and be
    /// within the page address range, otherwise an Error is returned.
    /// Specification:
    /// Precondition: the offset needs to be divisible by the size of usize.
    #[rr::requires("(ly_size usize_t | offset_in_bytes)%Z")]
    /// Precondition: we need to be able to fit a usize at the offset and not exceed the page bounds
    #[rr::requires("(offset_in_bytes + ly_size usize_t ≤ page_size_in_bytes_Z self.cur.(page_sz))%Z")]
    #[rr::exists("off'" : "Z")]
    /// Postcondition: off is a multiple of usize
    #[rr::ensures("offset_in_bytes = (off' * ly_size usize_t)%Z")]
    /// Postcondition: self has been updated to contain the value `v2` at offset `off`
    // TODO only in the Ok case. We need good support for simplifying that.
    #[rr::observe("self.ghost": "mk_page self.cur.(page_loc) self.cur.(page_sz) (<[Z.to_nat off' := value]> self.cur.(page_val))")]
    #[rr::returns("Ok ()")]
    pub fn write(&mut self, offset_in_bytes: usize, value: usize) -> Result<(), Error> {
        ensure!(offset_in_bytes % Self::ENTRY_SIZE == 0, Error::AddressNotAligned())?;
        unsafe {
            // Safety: below add results in a valid confidential memory address because
            // we ensure that it is within the page boundary and page is guaranteed to
            // be entirely inside the confidential memory.
            let pointer = self.address.add(offset_in_bytes, self.end_address_ptr())?;
            // pointer is guaranteed to be in the range <0;self.size()-size_of::(usize)>
            pointer.write_volatile(value);
        };
        Ok(())
    }

    /// Extends the digest with the guest physical address and the content of the page.
    pub fn measure(&self, digest: &mut MeasurementDigest, guest_physical_address: usize) {
        use sha2::Digest;
        let mut hasher = DigestType::new_with_prefix(digest.clone());
        hasher.update(guest_physical_address.to_le_bytes());
        // below unsafe is ok because the page has been initialized and it owns the entire memory region.
        // We are creating a slice of bytes, so the number of elements in the slice is the same as the size of the page.
        let slice: &[u8] = unsafe { core::slice::from_raw_parts(self.address().to_ptr(), self.size().in_bytes()) };
        hasher.update(&slice);
        hasher.finalize_into(digest);
    }

    /// Returns all usize-aligned offsets within the page.
    #[rr::skip]
    #[rr::params("p")]
    #[rr::args("#p")]
    // the values that the iterator will yield?
    #[rr::returns("step_list 0 (ly_size usize_t) (page_size_in_bytes_nat p.(page_sz))")]
    pub fn offsets(&self) -> core::iter::StepBy<Range<usize>> {
        (0..self.size.in_bytes()).step_by(Self::ENTRY_SIZE)
    }

    #[rr::only_spec]
    /// Postcondition: The page has been zeroized.
    #[rr::observe("self.ghost": "mk_page self.cur.(page_loc) self.cur.(page_sz) (zero_page self.cur.(page_sz))")]
    fn clear(&mut self) {
        // Safety: below unwrap() is fine because we iterate over page's offsets and thus always
        // request a write to an offset within the page.
        self.offsets().for_each(
            #[rr::skip]
            #[rr::params("off", "p")]
            #[rr::args("off")]
            // this should be dispatched by knowing that each argument is an element of the
            // iterator, i.e. be implied by what for_each can guarantee
            #[rr::requires("(ly_size usize_t | off)%Z")]
            #[rr::requires("(off + ly_size usize_t ≤ page_size_in_bytes_Z p.(page_sz))%Z")]
            #[rr::exists("off'")]
            #[rr::ensures("off = (off' * ly_size usize_t)%Z")]
            #[rr::capture("self" : "p" -> "mk_page p.(page_loc) p.(page_sz) (<[Z.to_nat off' := 0]> p.(page_val))")]
            |offset_in_bytes| self.write(offset_in_bytes, 0).unwrap(),
        );
    }
}

// We declare Send+Sync on the `Page` because it stores internally a raw pointer, which is
// not safe to pass in a multi-threaded program. But in the case of the `Page` it is safe
// because the `Page` owns the memory associated with pointer and never exposes the raw pointer
// to the outside.
unsafe impl<S> Send for Page<S> where S: PageState {}
unsafe impl<S> Sync for Page<S> where S: PageState {}
