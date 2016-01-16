1.1.0
-----

 * Switch to a four-heap instead of a two-heap, and to a three-pivot quicksort
   instead of a two-pivot one. Both improve the cache locality on large lists.
 * Fix soundness problems in the heapsort, if the comparison function panics
   while sorting.


1.0.0
-----

 * Forked from [veddan/rust-introsort], because it didn't run on stable Rust.

[veddan/rust-introsort]: https://github.com/veddan/rust-introsort
