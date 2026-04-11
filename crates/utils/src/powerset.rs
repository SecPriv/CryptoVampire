//! Vibe coded powerset iterator

use std::iter::FusedIterator;

/// Iterator over the powerset of a vector, starting from the largest subset.
///
/// This iterator generates all possible subsets of the input vector, starting
/// from the complete set and working down to the empty set. Each subset is
/// yielded as a new `Vec<T>` (with elements cloned).
///
/// # Examples
///
/// ```
/// use utils::powerset::powerset_reverse;
///
/// let vec = vec!["a", "b"];
/// let powerset: Vec<Vec<&str>> = powerset_reverse(vec).collect();
///
/// // Yields: ["a", "b"], ["a"], ["b"], []
/// assert_eq!(powerset[0], vec!["a", "b"]);
/// assert_eq!(powerset[3], Vec::<&str>::new());
/// ```
///
/// # Complexity
///
/// - Creating the iterator: O(1)
/// - Iterating through all subsets: O(2^n) (as expected for any powerset iterator)
pub struct PowersetReverse<T> {
    elements: Vec<T>,
    end: u64,
    start: u64,
}

impl<T: Clone> PowersetReverse<T> {
    /// Creates a new `PowersetReverse` iterator from a vector.
    ///
    /// # Arguments
    ///
    /// * `elements` - The vector to generate the powerset from
    pub fn new(elements: Vec<T>) -> Self {
        let len = elements.len();
        assert!(len < 64, "supports at most 64 elememts");
        Self {
            elements,
            end: 1 << len,
            start: 0,
        }
    }
}

impl<T> Iterator for PowersetReverse<T>
where
    T: Clone,
{
    type Item = Vec<T>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.end <= self.start {
            return None;
        }

        let mask = !self.start & ((1 << self.elements.len()) - 1);

        let mut ret = Vec::with_capacity(mask.count_ones() as usize);

        for (i, e) in self.elements.iter().enumerate() {
            if (mask & (1 << i)) != 0 {
                ret.push(e.clone());
            }
        }

        self.start += 1;
        Some(ret)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let remaining = self.end - self.start;
        match remaining.try_into() {
            Ok(remaining) => (remaining, Some(remaining)),
            _ => (usize::MAX, None),
        }
    }
}

impl<T> FusedIterator for PowersetReverse<T> where T: Clone {}

/// Iterator over the powerset of a slice, yielding iterators for each subset.
///
/// This iterator generates all possible subsets of the input slice, starting
/// from the complete set and working down to the empty set. Unlike
/// `PowersetReverse`, this version yields individual iterators for each subset
/// rather than cloning elements into new vectors. This is more efficient when
/// you only need to iterate over the elements of each subset once.
///
/// # Examples
///
/// ```
/// use utils::powerset::powerset_reverse_iter;
///
/// let vec = vec!["a", "b", "c"];
/// let powerset = powerset_reverse_iter(&vec);
///
/// // Each yielded value is an iterator over references
/// for subset in powerset {
///     let subset_vec: Vec<&str> = subset.copied().collect();
///     println!("{:?}", subset_vec);
/// }
/// ```
///
/// # Complexity
///
/// - Creating the iterator: O(1)
/// - Iterating through all subsets: O(2^n) (as expected for any powerset iterator)
pub struct PowersetReverseIter<'a, T> {
    elements: &'a [T],
    mask: u64,
}

impl<'a, T> PowersetReverseIter<'a, T> {
    /// Creates a new `PowersetReverseIter` iterator from a slice.
    ///
    /// # Arguments
    ///
    /// * `elements` - The slice to generate the powerset from
    pub fn new(elements: &'a [T]) -> Self {
        let len = elements.len();
        assert!(len < 64, "supports at most 64 elememts");
        Self {
            elements,
            mask: 1 << len,
        }
    }
}

impl<'a, T> Iterator for PowersetReverseIter<'a, T> {
    type Item = SubsetIter<'a, T>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.mask == 0 {
            return None;
        }

        self.mask -= 1;
        Some(SubsetIter::new(self.elements, self.mask))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let remaining: Result<usize, _> = self.mask.try_into();
        match remaining {
            Ok(remaining) => (remaining, Some(remaining)),
            _ => (usize::MAX, None),
        }
    }
}

impl<'a, T> FusedIterator for PowersetReverseIter<'a, T> {}

/// Iterator over a single subset of elements from a powerset.
///
/// This struct is yielded by `PowersetReverseIter` and allows iterating over
/// the elements of a single subset without cloning. It uses a bitmask to
/// determine which elements belong to the subset.
///
/// # Examples
///
/// ```
/// use utils::powerset::{PowersetReverseIter, SubsetIter};
///
/// let vec = vec!["a", "b", "c"];
/// let mut powerset = PowersetReverseIter::new(&vec);
///
/// // Get the first subset (should be ["a", "b", "c"])
/// if let Some(subset) = powerset.next() {
///     let items: Vec<&str> = subset.copied().collect();
///     assert_eq!(items, vec!["a", "b", "c"]);
/// }
/// ```
pub struct SubsetIter<'a, T> {
    elements: &'a [T],
    mask: u64,
    index: usize,
}

impl<'a, T> SubsetIter<'a, T> {
    /// Creates a new `SubsetIter` from a slice and a bitmask.
    ///
    /// The bitmask determines which elements are included in the subset:
    /// element `i` is included iff bit `i` of the mask is set.
    ///
    /// # Arguments
    ///
    /// * `elements` - The slice to iterate over
    /// * `mask` - The bitmask determining which elements to include
    fn new(elements: &'a [T], mask: u64) -> Self {
        Self {
            elements,
            mask,
            index: 0,
        }
    }
}

impl<'a, T> Iterator for SubsetIter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        while self.index < self.elements.len() {
            let i = self.index;
            self.index += 1;
            if (self.mask >> i) & 1 == 1 {
                return Some(&self.elements[i]);
            }
        }
        None
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        if self.index >= self.elements.len() {
            (0, Some(0))
        } else {
            // Count remaining set bits in the mask after current index
            let remaining_mask = self.mask >> self.index;
            let count = remaining_mask.count_ones() as usize;
            (count, Some(count))
        }
    }
}

/// Creates an iterator over the powerset of a vector, starting from the largest subset.
///
/// This function takes ownership of the vector and yields cloned vectors for each subset.
/// Use this when you need owned copies of each subset.
///
/// # Arguments
///
/// * `vec` - The vector to generate the powerset from
///
/// # Returns
///
/// An iterator that yields `Vec<T>` for each subset, starting with the complete set.
///
/// # Examples
///
/// ```
/// use utils::powerset::powerset_reverse;
///
/// let vec = vec![1, 2, 3];
/// let powerset: Vec<Vec<i32>> = powerset_reverse(vec).collect();
///
/// // First subset is the complete set
/// assert_eq!(powerset[0], vec![1, 2, 3]);
/// // Last subset is the empty set
/// assert_eq!(powerset.last().unwrap(), Vec::<i32>::new());
/// ```
pub fn powerset_reverse<T>(vec: Vec<T>) -> PowersetReverse<T>
where
    T: Clone,
{
    PowersetReverse::new(vec)
}

/// Creates an iterator over the powerset of a slice, yielding iterators for each subset.
///
/// This function takes a reference to a slice and yields iterators for each subset.
/// Use this when you want to avoid cloning and only need to iterate through each subset once.
///
/// # Arguments
///
/// * `slice` - The slice to generate the powerset from
///
/// # Returns
///
/// An iterator that yields `SubsetIter` for each subset, starting with the complete set.
/// Each `SubsetIter` can be used to iterate over references to the elements in that subset.
///
/// # Examples
///
/// ```
/// use utils::powerset::powerset_reverse_iter;
///
/// let vec = vec!["a", "b", "c"];
/// let powerset = powerset_reverse_iter(&vec);
///
/// // Collect all subsets into a vector of vectors
/// let result: Vec<Vec<&str>> = powerset.map(|subset| subset.copied().collect()).collect();
///
/// assert_eq!(result.len(), 8);
/// assert_eq!(result[0], vec!["a", "b", "c"]);
/// ```
pub fn powerset_reverse_iter<T>(slice: &[T]) -> PowersetReverseIter<'_, T> {
    PowersetReverseIter::new(slice)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_powerset_reverse() {
        let vec = vec!["a", "b", "c"];
        let powerset = powerset_reverse(vec);
        let result: Vec<Vec<&str>> = powerset.collect();

        assert_eq!(result.len(), 8);
        assert_eq!(result[0], vec!["a", "b", "c"]);
        assert_eq!(result.last().unwrap(), &Vec::<&str>::new());
    }

    #[test]
    fn test_powerset_reverse_empty() {
        let vec: Vec<i32> = vec![];
        let powerset = powerset_reverse(vec);
        let result: Vec<Vec<i32>> = powerset.collect();

        assert_eq!(result.len(), 1);
        assert_eq!(result[0], Vec::<i32>::new());
    }

    #[test]
    fn test_powerset_reverse_single() {
        let vec = vec![1];
        let powerset = powerset_reverse(vec);
        let result: Vec<Vec<i32>> = powerset.collect();

        assert_eq!(result.len(), 2);
        assert_eq!(result[0], vec![1]);
        assert_eq!(result[1], Vec::<i32>::new());
    }

    #[test]
    fn test_powerset_reverse_iter() {
        let vec = vec!["a", "b", "c"];
        let powerset = powerset_reverse_iter(&vec);
        let result: Vec<Vec<&str>> = powerset.map(|iter| iter.copied().collect()).collect();

        assert_eq!(result.len(), 8);
        assert_eq!(result[0], vec!["a", "b", "c"]);
        assert_eq!(result.last().unwrap(), &Vec::<&str>::new());
    }
}
