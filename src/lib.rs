//! A no-std friendly non-overlapping interval tree.
//!
//! The tree maintains a set of elements that can be indexed by key, where the key is a range.
//! Lookup queries return the value of a range if the lookup key is contained within the range.
//!
//! This tree requires all elements' ranges be non-overlapping, which is enforced by the
//! insert_replace function. As a result, the insert_replace function has some extra runtime
//! overhead, scaling with the number of current elements keyed by ranges that overlap with the
//! range we are inserting. For faster insert, an unsafe insert function exists, where the caller is
//! expected to ensure the non-overlapping property themselves.
//!
//! To use the no-std version, turn off default features.
//!
//! # Examples
//! ```
//! use nonoverlapping_interval_tree::NonOverlappingIntervalTree;
//! let mut it = NonOverlappingIntervalTree::new();
//! it.insert_replace(1..3, "hello");
//! assert_eq!(it.get(&2), Some(&"hello"));
//! assert_eq!(it.get(&7), None);
//! assert_eq!(it.get(&3), None); // Intervals are [1, 3)
//! ```

#![deny(
    missing_docs,
    missing_debug_implementations,
    missing_copy_implementations,
    trivial_casts,
    trivial_numeric_casts,
    unstable_features,
    unused_import_braces,
    unused_qualifications
)]
#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(feature = "std")]
use std::{
    collections::{
        btree_map::{Iter, IterMut},
        BTreeMap,
    },
    ops::{Deref, DerefMut, Range},
};

#[cfg(not(feature = "std"))]
extern crate alloc;
#[cfg(not(feature = "std"))]
use alloc::collections::{
    btree_map::{Iter, IterMut},
    BTreeMap,
};
#[cfg(not(feature = "std"))]
use alloc::{vec, vec::Vec};
#[cfg(not(feature = "std"))]
use core::ops::{Deref, DerefMut, Range};

#[cfg(not(feature = "std"))]
pub use alloc::collections::btree_map::Range as ValueRange;
#[cfg(not(feature = "std"))]
pub use alloc::collections::btree_map::RangeMut as ValueRangeMut;

#[cfg(feature = "std")]
pub use std::collections::btree_map::Range as ValueRange;
#[cfg(feature = "std")]
pub use std::collections::btree_map::RangeMut as ValueRangeMut;

#[derive(Clone, Debug, Copy, PartialEq, Eq)]
/// Tracks the size of intervals and owns values internally in the tree.
pub struct IntervalValue<K, V> {
    val: V,
    end: K,
}

impl<K, V> IntervalValue<K, V> {
    fn new(val: V, end: K) -> Self {
        Self { val, end }
    }

    /// Return a reference to the value associated with this interval value.
    pub fn value(&self) -> &V {
        &self.val
    }

    /// Return a mutable reference to the value associated with this interval value.
    pub fn value_mut(&mut self) -> &mut V {
        &mut self.val
    }

    /// Consume the IntervalValue and return the inner value.
    pub fn into_inner(self) -> V {
        self.val
    }

    /// Return the end of this interval.
    pub fn end(&self) -> &K {
        &self.end
    }

    /// Consume the IntervalValue and return the end.
    pub fn into_end(self) -> K {
        self.end
    }
}

impl<K, V> Deref for IntervalValue<K, V> {
    type Target = V;

    fn deref(&self) -> &Self::Target {
        self.value()
    }
}

impl<K, V> DerefMut for IntervalValue<K, V> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.value_mut()
    }
}

#[derive(Clone, Debug)]
/// An implementation of a non-overlapping interval tree.
///
/// Keys are ranges, Range<K>, and values are stored for a given range. Ranges inside the tree
/// map not overlap, and the insert function enforces this. Internally managed by a BTreeMap.
pub struct NonOverlappingIntervalTree<K, V> {
    tree: BTreeMap<K, IntervalValue<K, V>>,
}

impl<K, V> Default for NonOverlappingIntervalTree<K, V> {
    fn default() -> Self {
        Self::new()
    }
}

impl<K, V> NonOverlappingIntervalTree<K, V> {
    /// Construct a new non-overlapping interval tree.
    pub fn new() -> Self {
        Self {
            tree: BTreeMap::new(),
        }
    }
}

fn overlap<R: PartialOrd>(a: &Range<R>, b: &Range<R>) -> bool {
    a.start < b.end && b.start < a.end
}

impl<K: Ord + Clone, V> NonOverlappingIntervalTree<K, V> {
    /// Insert a value into the tree for a given range, not checking to see if any overlapping
    /// occurs. If there's an element whose range starts with `int`'s start, that element is removed
    /// and returned.
    ///
    /// # Note
    /// This function can potentially corrupt the tree, since the normal operation functions rely on
    /// there being no overlaps. Care must be taken when using this function to ensure the
    /// no-overlap property manually.
    pub fn insert(&mut self, int: Range<K>, val: V) -> Option<V> {
        self.tree
            .insert(int.start, IntervalValue::new(val, int.end))
            .map(|v| v.val)
    }
    /// Insert a value into the tree for a given range, removing and returning all K,V pairs that
    /// are in the tree that overlap with the inserted range.
    /// # Examples
    /// ```
    /// use nonoverlapping_interval_tree::NonOverlappingIntervalTree;
    /// let mut it = NonOverlappingIntervalTree::new();
    /// it.insert_replace(1..3, "hello");
    /// ```
    pub fn insert_replace(&mut self, int: Range<K>, val: V) -> Vec<(Range<K>, V)> {
        let mut removed = vec![];
        'outer: loop {
            let noderange = self.tree.range(..&int.end);
            let mut count = 0;
            for n in noderange.rev() {
                let thisrange = K::clone(n.0)..K::clone(&n.1.end);
                if int.start >= n.1.end {
                    break 'outer;
                }
                if overlap(&thisrange, &int) {
                    let rem = self.tree.remove(&thisrange.start).unwrap().val;
                    removed.push((thisrange, rem));
                    break;
                }
                count += 1;
            }
            if count == 0 {
                break;
            }
        }

        let key = int.start;
        if let Some(v) = self
            .tree
            .insert(K::clone(&key), IntervalValue::new(val, int.end))
        {
            removed.push((key..v.end, v.val));
        }
        removed
    }

    /// Get an immutable reference to the value of a single point in the interval tree, returning the value for a range that contains
    /// this point if one exists.
    pub fn get(&self, point: &K) -> Option<&V> {
        if let Some(v) = self.tree.get(point) {
            return Some(&v.val);
        }
        let noderange = self.tree.range(..point);
        if let Some(prev) = noderange.last() {
            let range = prev.0..&prev.1.end;
            if range.contains(&point) {
                return Some(&prev.1.val);
            }
        }
        None
    }

    /// Get a mutable reference to the value of a single point in the interval tree, returning the value for a range that contains
    /// this point if one exists.
    pub fn get_mut(&mut self, point: &K) -> Option<&mut V> {
        //if let Some(v) = self.tree.get_mut(point) {
        //   return Some(&mut v.val);
        //}
        let noderange = self.tree.range_mut(..=point);
        if let Some(prev) = noderange.last() {
            let range = prev.0..&prev.1.end;
            if range.contains(&point) {
                return Some(&mut prev.1.val);
            }
        }
        None
    }

    /// Remove the value associated with the range that contains the point argument. If one is
    /// present, it is removed and returned, otherwise None is returned.
    pub fn remove(&mut self, point: &K) -> Option<V> {
        if let Some(v) = self.tree.remove(point) {
            return Some(v.val);
        }
        let range = {
            self.tree
                .range(..point)
                .last()
                .map(|prev| K::clone(prev.0)..K::clone(&prev.1.end))
        };

        if let Some(range) = range {
            if range.contains(point) {
                return self.tree.remove(&range.start).map(|v| v.val);
            }
        }
        None
    }

    /// Returns a double-ended iterator over a sub-range of elements in the map. The resulting range
    /// may contain individual points that are not in the provided range if the stored ranges
    /// overlap with the terminating point. For example, if the tree contains [[1..3], [4..6]], and
    /// you call tree.range(1..5), you'll get back [[1..3], [4..6]], since the 4..6 range contains 4
    /// as requested by the call to range.
    pub fn range(&self, range: Range<K>) -> ValueRange<'_, K, IntervalValue<K, V>> {
        /* We might have to look at the element immediately preceeding range.start */
        let therange = {
            let start = range.start;
            self.tree
                .range(..K::clone(&start))
                .last()
                .map_or(start, |prev| K::clone(prev.0))..range.end
        };

        self.tree.range(therange)
    }

    /// Returns a mutable double-ended iterator over a sub-range of elements in the map. The resulting range
    /// may contain individual points that are not in the provided range if the stored ranges
    /// overlap with the terminating point. For example, if the tree contains [[1..3], [4..6]], and
    /// you call tree.range(1..5), you'll get back [[1..3], [4..6]], since the 4..6 range contains 4
    /// as requested by the call to range.
    pub fn range_mut(&mut self, range: Range<K>) -> ValueRangeMut<'_, K, IntervalValue<K, V>> {
        /* We might have to look at the element immediately preceeding range.start */
        let therange = {
            let start = range.start;
            self.tree
                .range(..K::clone(&start))
                .last()
                .map_or(start, |prev| K::clone(prev.0))..range.end
        };

        self.tree.range_mut(therange)
    }

    /// Remove all elements in the tree.
    pub fn clear(&mut self) {
        self.tree.clear()
    }

    /// Return an iterator for the tree, sorted by key.
    pub fn iter(&self) -> Iter<'_, K, IntervalValue<K, V>> {
        self.tree.iter()
    }

    /// Return an iterator for the tree, sorted by key.
    pub fn iter_mut(&mut self) -> IterMut<'_, K, IntervalValue<K, V>> {
        self.tree.iter_mut()
    }

    /// Returns the number of elements in the map.
    pub fn len(&self) -> usize {
        self.tree.len()
    }

    /// Returns true if the map contains no elements.
    pub fn is_empty(&self) -> bool {
        self.tree.is_empty()
    }
}

#[cfg(all(test, feature = "std"))]
mod tests {
    use std::vec;

    use crate::NonOverlappingIntervalTree;

    #[test]
    fn it_inserts() {
        let mut it = NonOverlappingIntervalTree::new();
        assert_eq!(it.insert_replace(0..5, "hello").len(), 0);
    }

    #[test]
    fn it_looksup() {
        let mut it = NonOverlappingIntervalTree::new();
        assert_eq!(it.insert_replace(1..3, "hello").len(), 0);
        assert_eq!(it.insert_replace(3..5, "world").len(), 0);
        assert_eq!(it.insert_replace(7..9, "foo").len(), 0);
        assert_eq!(it.insert_replace(100..101, "bar").len(), 0);
        let res = it.get(&1);
        assert_eq!(res, Some(&"hello"));
        let res = it.get(&2);
        assert_eq!(res, Some(&"hello"));
        let res = it.get(&10);
        assert_eq!(res, None);
        let res = it.get(&0);
        assert_eq!(res, None);
        let res = it.get(&3);
        assert_eq!(res, Some(&"world"));
        let res = it.get(&4);
        assert_eq!(res, Some(&"world"));
        let res = it.get(&5);
        assert_eq!(res, None);
        let res = it.get(&7);
        assert_eq!(res, Some(&"foo"));
        let res = it.get(&8);
        assert_eq!(res, Some(&"foo"));
        let res = it.get(&100);
        assert_eq!(res, Some(&"bar"));
        let res = it.get(&99);
        assert_eq!(res, None);
        let res = it.get(&101);
        assert_eq!(res, None);
    }

    #[test]
    fn it_looksup_mut() {
        let mut it = NonOverlappingIntervalTree::new();
        assert_eq!(it.insert_replace(1..3, "hello").len(), 0);
        assert_eq!(it.insert_replace(3..5, "world").len(), 0);
        assert_eq!(it.insert_replace(7..9, "foo").len(), 0);
        assert_eq!(it.insert_replace(100..101, "bar").len(), 0);
        let res = it.get_mut(&1);
        assert_eq!(res, Some(&mut "hello"));
        let res = it.get_mut(&2);
        assert_eq!(res, Some(&mut "hello"));
        let res = it.get_mut(&10);
        assert_eq!(res, None);
        let res = it.get_mut(&0);
        assert_eq!(res, None);
        let res = it.get_mut(&3);
        assert_eq!(res, Some(&mut "world"));
        let res = it.get_mut(&4);
        assert_eq!(res, Some(&mut "world"));
        let res = it.get_mut(&5);
        assert_eq!(res, None);
        let res = it.get_mut(&7);
        assert_eq!(res, Some(&mut "foo"));
        let res = it.get_mut(&8);
        assert_eq!(res, Some(&mut "foo"));
        let res = it.get_mut(&100);
        assert_eq!(res, Some(&mut "bar"));
        let res = it.get_mut(&99);
        assert_eq!(res, None);
        let res = it.get_mut(&101);
        assert_eq!(res, None);
    }

    #[test]
    fn it_removes() {
        let mut it = NonOverlappingIntervalTree::new();
        assert_eq!(it.insert_replace(1..3, "hello").len(), 0);
        assert_eq!(it.get(&2), Some(&"hello"));
        assert_eq!(it.remove(&2), Some("hello"));
        assert_eq!(it.get(&1), None);
        assert_eq!(it.get(&2), None);
        assert_eq!(it.get(&3), None);
    }

    #[test]
    fn it_does_ranges() {
        let mut it = NonOverlappingIntervalTree::new();
        assert_eq!(it.insert_replace(1..3, "hello").len(), 0);
        assert_eq!(it.insert_replace(4..6, "world").len(), 0);
        assert_eq!(it.insert_replace(10..12, "bad").len(), 0);
        let r: Vec<&str> = it.range(1..3).map(|r| *r.1.value()).collect();
        assert_eq!(r, vec!["hello"]);
        let r: Vec<&str> = it.range(1..5).map(|r| *r.1.value()).collect();
        assert_eq!(r, vec!["hello", "world"]);
        let r: Vec<&str> = it.range(2..8).map(|r| *r.1.value()).collect();
        assert_eq!(r, vec!["hello", "world"]);
        let r: Vec<&str> = it.range(1..80).map(|r| *r.1.value()).collect();
        assert_eq!(r, vec!["hello", "world", "bad"]);
        let r: Vec<&str> = it.range(11..12).map(|r| *r.1.value()).collect();
        assert_eq!(r, vec!["bad"]);
    }

    #[test]
    fn it_replaces() {
        let mut it = NonOverlappingIntervalTree::new();
        assert_eq!(it.insert_replace(1..4, "hello").len(), 0);
        assert_eq!(it.insert_replace(2..3, "world"), vec![(1..4, "hello")]);
        assert_eq!(it.get(&1), None);
        assert_eq!(it.get(&2), Some(&"world"));
        assert_eq!(it.get(&3), None);

        let mut it = NonOverlappingIntervalTree::new();
        assert_eq!(it.insert_replace(1..3, "hello").len(), 0);
        assert_eq!(it.insert_replace(2..3, "world"), vec![(1..3, "hello")]);
        assert_eq!(it.get(&1), None);
        assert_eq!(it.get(&2), Some(&"world"));
        assert_eq!(it.get(&3), None);

        let mut it = NonOverlappingIntervalTree::new();
        assert_eq!(it.insert_replace(2..4, "hello").len(), 0);
        assert_eq!(it.insert_replace(1..3, "world"), vec![(2..4, "hello")]);
        assert_eq!(it.get(&1), Some(&"world"));
        assert_eq!(it.get(&2), Some(&"world"));
        assert_eq!(it.get(&3), None);

        let mut it = NonOverlappingIntervalTree::new();
        assert_eq!(it.insert_replace(2..3, "hello").len(), 0);
        assert_eq!(it.insert_replace(1..4, "world"), vec![(2..3, "hello")]);
        assert_eq!(it.get(&1), Some(&"world"));
        assert_eq!(it.get(&2), Some(&"world"));
        assert_eq!(it.get(&3), Some(&"world"));
    }
}
