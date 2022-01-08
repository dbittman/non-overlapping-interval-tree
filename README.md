# Non-overlapping Interval Tree

Simple library for a map data structure that contains elements keyed on ranges, whose keys cannot
overlap. Lookup queries can lookup a specific point in a range, and get back the value for that
range.

This library supports no_std (but requires core and the alloc crate). To enable no_std, disable
default features.