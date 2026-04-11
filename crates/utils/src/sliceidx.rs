use std::collections::VecDeque;

pub trait IdxFromSlice<Idx> {
    type Item;
    fn get_index(&self, ptr: &Self::Item) -> Option<Idx>;
    /// # Safety
    /// ptr must be 'part' of self
    unsafe fn get_index_unchecked(&self, ptr: &Self::Item) -> Idx;
}

impl<T> IdxFromSlice<usize> for [T] {
    type Item = T;

    fn get_index(&self, ptr: &Self::Item) -> Option<usize> {
        self.as_ptr_range()
            .contains(&(ptr as *const _))
            .then(|| unsafe { self.get_index_unchecked(ptr) })
    }

    /// Safety: ptr must be 'part' of self
    #[inline]
    unsafe fn get_index_unchecked(&self, ptr: &Self::Item) -> usize {
        // Safety, ptr is in self, there part of the same allocation and 'after' `self.as_ptr()`
        (ptr as *const Self::Item).offset_from_unsigned(self.as_ptr())
    }
}

impl<T> IdxFromSlice<usize> for Vec<T> {
    type Item = T;

    fn get_index(&self, ptr: &Self::Item) -> Option<usize> {
        self.as_slice().get_index(ptr)
    }

    unsafe fn get_index_unchecked(&self, ptr: &Self::Item) -> usize {
        self.as_slice().get_index_unchecked(ptr)
    }
}

impl<T> IdxFromSlice<usize> for VecDeque<T> {
    type Item = T;

    fn get_index(&self, ptr: &Self::Item) -> Option<usize> {
        let (bottom, top) = self.as_slices();
        match bottom.get_index(ptr) {
            None => top.get_index(ptr),
            x => x,
        }
    }

    /// shouldn't be used: virtually no gains over the safe method
    unsafe fn get_index_unchecked(&self, ptr: &Self::Item) -> usize {
        let (bottom, top) = self.as_slices();
        if bottom.as_ptr() as usize >= (ptr as *const _) as usize {
            bottom.get_index_unchecked(ptr)
        } else {
            top.get_index_unchecked(ptr)
        }
    }
}
