use std::{collections::BTreeMap, ops::Range};

#[derive(Clone, Debug, Copy, PartialEq, Eq)]
struct IntervalValue<K, V> {
    val: V,
    end: K,
}

impl<K, V> IntervalValue<K, V> {
    fn new(val: V, end: K) -> Self {
        Self { val, end }
    }
}

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
    pub fn insert_replace(&mut self, int: Range<K>, val: V) -> Vec<(Range<K>, V)> {
        let mut removed = vec![];
        'outer: loop {
            let noderange = self.tree.range(..&int.end);
            let mut count = 0;
            for n in noderange.rev() {
                let thisrange = K::clone(&n.0)..K::clone(&n.1.end);
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

    pub fn lookup(&self, point: &K) -> Option<&V> {
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
}

#[cfg(test)]
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
        let res = it.lookup(&1);
        assert_eq!(res, Some(&"hello"));
        let res = it.lookup(&2);
        assert_eq!(res, Some(&"hello"));
        let res = it.lookup(&10);
        assert_eq!(res, None);
        let res = it.lookup(&0);
        assert_eq!(res, None);
        let res = it.lookup(&3);
        assert_eq!(res, Some(&"world"));
        let res = it.lookup(&4);
        assert_eq!(res, Some(&"world"));
        let res = it.lookup(&5);
        assert_eq!(res, None);
        let res = it.lookup(&7);
        assert_eq!(res, Some(&"foo"));
        let res = it.lookup(&8);
        assert_eq!(res, Some(&"foo"));
        let res = it.lookup(&100);
        assert_eq!(res, Some(&"bar"));
        let res = it.lookup(&99);
        assert_eq!(res, None);
        let res = it.lookup(&101);
        assert_eq!(res, None);
    }

    #[test]
    fn it_removes() {
        let mut it = NonOverlappingIntervalTree::new();
        assert_eq!(it.insert_replace(1..3, "hello").len(), 0);
        assert_eq!(it.lookup(&2), Some(&"hello"));
        assert_eq!(it.remove(&2), Some("hello"));
        assert_eq!(it.lookup(&1), None);
        assert_eq!(it.lookup(&2), None);
        assert_eq!(it.lookup(&3), None);
    }

    #[test]
    fn it_replaces() {
        let mut it = NonOverlappingIntervalTree::new();
        assert_eq!(it.insert_replace(1..4, "hello").len(), 0);
        assert_eq!(it.insert_replace(2..3, "world"), vec![(1..4, "hello")]);
        assert_eq!(it.lookup(&1), None);
        assert_eq!(it.lookup(&2), Some(&"world"));
        assert_eq!(it.lookup(&3), None);

        let mut it = NonOverlappingIntervalTree::new();
        assert_eq!(it.insert_replace(1..3, "hello").len(), 0);
        assert_eq!(it.insert_replace(2..3, "world"), vec![(1..3, "hello")]);
        assert_eq!(it.lookup(&1), None);
        assert_eq!(it.lookup(&2), Some(&"world"));
        assert_eq!(it.lookup(&3), None);

        let mut it = NonOverlappingIntervalTree::new();
        assert_eq!(it.insert_replace(2..4, "hello").len(), 0);
        assert_eq!(it.insert_replace(1..3, "world"), vec![(2..4, "hello")]);
        assert_eq!(it.lookup(&1), Some(&"world"));
        assert_eq!(it.lookup(&2), Some(&"world"));
        assert_eq!(it.lookup(&3), None);

        let mut it = NonOverlappingIntervalTree::new();
        assert_eq!(it.insert_replace(2..3, "hello").len(), 0);
        assert_eq!(it.insert_replace(1..4, "world"), vec![(2..3, "hello")]);
        assert_eq!(it.lookup(&1), Some(&"world"));
        assert_eq!(it.lookup(&2), Some(&"world"));
        assert_eq!(it.lookup(&3), Some(&"world"));
    }
}
