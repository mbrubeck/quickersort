use std::cmp::Ordering;
use std::cmp::Ordering::*;
use std::cmp::{min, max};
use std::mem::{forget, size_of, swap};
use std::ptr;
use std::slice;
use unreachable::UncheckedOptionExt;

/// The smallest number of elements that may be quicksorted.
/// Must be at least 14.
const MIN_QUICKSORT_ELEMS: usize = 14;

/// The maximum number of elements to be insertion sorted.
const MAX_INSERTION_SORT_ELEMS: usize = 42;

/// Controls the number of elements to be insertion sorted.
/// Higher values give more insertion sorted elements.
const INSERTION_SORT_FACTOR: usize = 450;

/// Sort using a custom ordering.
pub fn sort_by<T, C: Fn(&T, &T) -> Ordering>(v: &mut [T], compare: &C) {
    let heapsort_depth = (3 * log2(v.len())) / 2;
    introsort(v, compare, 0, heapsort_depth);
}

/// Sort, if the elements have an intrinsic ordering.
pub fn sort<T: Ord>(v: &mut [T]) {
    sort_by(v, &|a, b| a.cmp(b));
}

/// The general quick sort algorithm, that tries to handle all kinds of arrays sensibly
///
///  * For arrays with very few elements, it just switches to insertion sort.
///  * For most random arrays, it partitions the array into four partitions using three pivots.
///  * For arrays with the same element may times, it partitions the array into three partitions
///    using that element as the pivot.
///  * For arrays that cause it to recurse too may times, it switches to heapsort.
fn introsort<T, C: Fn(&T, &T) -> Ordering>(mut v: &mut [T], compare: &C, mut rec: u32, heapsort_depth: u32) {
    loop {
        if maybe_insertion_sort(v, compare) { return };
        if rec > heapsort_depth { return heapsort(v, compare) };
        let n = v.len();
        // Pivot selection.
        macro_rules! maybe_swap(
            ($compare: expr, $v: expr, $a: expr, $b: expr) => {
                if compare_idxs($v, *$a, *$b, $compare) == Greater {
                    swap($a, $b);
                }
            }
        );
        // Medians-of-seven pivot selection.
        let mut e3 = n / 2;
        let mut e1 = e3 / 2;
        let mut e0 = e1 / 2;
        let mut e5 = e3 + e1;
        let mut e2 = e1 + e0;
        let mut e4 = e3 + e0;
        let mut e6 = e5 + e0;
        unsafe {
            maybe_swap!(compare, v, &mut e0, &mut e4);
            maybe_swap!(compare, v, &mut e1, &mut e5);
            maybe_swap!(compare, v, &mut e2, &mut e6);
            maybe_swap!(compare, v, &mut e0, &mut e2);
            maybe_swap!(compare, v, &mut e1, &mut e3);
            maybe_swap!(compare, v, &mut e4, &mut e6);
            maybe_swap!(compare, v, &mut e2, &mut e4);
            maybe_swap!(compare, v, &mut e3, &mut e5);
            maybe_swap!(compare, v, &mut e0, &mut e1);
            maybe_swap!(compare, v, &mut e2, &mut e3);
            maybe_swap!(compare, v, &mut e4, &mut e5);
            maybe_swap!(compare, v, &mut e1, &mut e4);
            maybe_swap!(compare, v, &mut e3, &mut e6);
            maybe_swap!(compare, v, &mut e1, &mut e2);
            maybe_swap!(compare, v, &mut e3, &mut e4);
            maybe_swap!(compare, v, &mut e5, &mut e6);
        }
        // Thin or fat partitioning?
        let mut equal = None;
        if compare(&v[e1], &v[e3]) == Equal {
            equal = Some(e1);
        }
        if compare(&v[e3], &v[e5]) == Equal {
            equal = Some(e5);
        }
        // The quicksort algorithm, complete with fake recursion optimization.
        let v_ = v;
        v = if let Some(pivot) = equal {
            let (va, vb) = fat_partition(v_, pivot, compare);
            if va.len() > vb.len() {
                introsort(vb, compare, rec + 1, heapsort_depth);
                va
            } else {
                introsort(va, compare, rec + 1, heapsort_depth);
                vb
            }
        } else {
            let (mut va, mut vb, mut vc, mut vd) = thin_partition(v_, e1, e3, e5, compare);
            macro_rules! maybe_swap_len(
                ($a: expr, $b: expr) => {
                    if $a.len() > $b.len() {
                        swap($a, $b);
                    }
                }
            );
            maybe_swap_len!(&mut va, &mut vb);
            maybe_swap_len!(&mut vc, &mut vd);
            maybe_swap_len!(&mut va, &mut vc);
            maybe_swap_len!(&mut vb, &mut vd);
            maybe_swap_len!(&mut vb, &mut vc);
            introsort(va, compare, rec + 1, heapsort_depth);
            introsort(vb, compare, rec + 1, heapsort_depth);
            introsort(vc, compare, rec + 1, heapsort_depth);
            vd
        };
        rec += 1;
    }
}

/// Three-pivot partition, based on http://epubs.siam.org/doi/pdf/10.1137/1.9781611973198.6
///
/// Partition elements, using `p`, `q`, and `r` all as pivots.
/// After partitioning, the array looks like the following:
///
/// `aaabbbbccccdddd`
///
/// where `a` is less than or equal to `p`, `b` is between `p` and `q` inclusive, `c` is between
/// `q` and `r` inclusive, and `d` is greater than or equal to `r`. Notice that we don't try to
/// handle arrays with a lot of elements equal to the pivot intelligently; that's what the fat
/// partition algorithm is for.
fn thin_partition<'a, T, C: Fn(&T, &T) -> Ordering>(v: &'a mut [T], p: usize, q: usize, r: usize, compare: &C) -> (&'a mut [T], &'a mut [T], &'a mut [T], &'a mut [T])  {
    let n = v.len();
    // Perform the partition.
    let (a, b, d) = unsafe {
        unsafe_swap(v, p, 0);
        unsafe_swap(v, q, 1);
        unsafe_swap(v, r, n - 1);
        // I ♡ noalias on &T. It ends with my pivots being stored in registers.
        let p = &*(v.get_unchecked(0) as *const T);
        let q = &*(v.get_unchecked(1) as *const T);
        let r = &*(v.get_unchecked(n - 1) as *const T);
        // The debug asserts are commented out because they give spurious errors when testing with
        // a broken comparator. Uncomment them, and comment out the broken comparator tests, if
        // stuff's broken.
        //debug_assert!(compare(v.get_unchecked(p), q) != Greater);
        //debug_assert!(compare(v.get_unchecked(q), r) != Greater);
        let (mut a, mut b, mut c, mut d) = (2, 2, n - 2, n - 2);
        'outer: while b <= c {
            if compare(v.get_unchecked(b), q) == Greater {
                while compare(v.get_unchecked(c), q) == Greater {
                    if compare(v.get_unchecked(c), r) == Greater {
                        unsafe_swap(v, c, d);
                        d -= 1;
                    }
                    //debug_assert!(compare(v.get_unchecked(c), q) == Greater);
                    c -= 1;
                    if b > c {
                        break 'outer;
                    }
                }
                if compare(v.get_unchecked(b), r) == Greater {
                    let x = ptr::read(v.get_unchecked(b));
                    copy(v.get_unchecked(c), v.get_unchecked_mut(b));
                    copy(v.get_unchecked(d), v.get_unchecked_mut(c));
                    copy(&x, v.get_unchecked_mut(d));
                    forget(x);
                    d -= 1;
                } else {
                    unsafe_swap(v, b, c);
                }
                //debug_assert!(compare(v.get_unchecked(c), q) == Greater);
                c -= 1;
                if b > c {
                    break 'outer;
                }
            }
            if compare(v.get_unchecked(b), p) == Less {
                unsafe_swap(v, a, b);
                a += 1;
            }
            //debug_assert!(compare(v.get_unchecked(b), q) != Greater);
            b += 1;
        }
        // And swap the pivots into place.
        a -= 1;
        unsafe_swap(v, a, 1);
        d += 1;
        unsafe_swap(v, d, n - 1);
        (a, b, d)
    };
    // Slice them up.
    unsafe {
        let (vabc, vd) = unsafe_split_at_mut(v, d + 1);
        let (vab, vc) = unsafe_split_at_mut(vabc, b);
        let (va, vb) = unsafe_split_at_mut(vab, a);
        (va, vb, vc, vd)
    }
}

/// Partitions elements, using the element at `pivot` as pivot.
/// After partitioning, the array looks as following:
///
/// `<<<<<==>>>`
fn fat_partition<'a, T, C: Fn(&T, &T) -> Ordering>(v: &'a mut [T], pivot: usize, compare: &C) -> (&'a mut [T], &'a mut [T])  {
    let mut a = 0;
    let mut b = a;
    let mut c = v.len() - 1;
    let mut d = c;
    v.swap(0, pivot);
    loop {
        while b <= c {
            let r = compare_idxs_safe(v, b, 0, compare);
            if r == Greater { break; }
            if r == Equal {
                unsafe { unsafe_swap(v, a, b); }
                a += 1;
            }
            b += 1;
        }
        while c >= b {
            let r = compare_idxs_safe(v, c, 0, compare);
            if r == Less { break; }
            if r == Equal {
                unsafe { unsafe_swap(v, c, d); }
                d -= 1;
            }
            c -= 1;
        }
        if b > c { break; }
        unsafe { unsafe_swap(v, b, c); }
        b += 1;
        c -= 1;
    }

    let n = v.len();
    let l = min(a, b - a);
    unsafe { swap_many(v, 0, b - l, l); }
    let r = min(d - c, n - 1 - d);
    unsafe { swap_many(v, b, n - r, r); }

    unsafe {
        let vb = unsafe_split_at_mut(v, n - (d - c));
        let va = unsafe_split_at_mut(vb.0, b - a);
        (va.0, vb.1)
    }
}

/// Insertion sort, if the slice is very small.
fn maybe_insertion_sort<T, C: Fn(&T, &T) -> Ordering>(v: &mut [T], compare: &C) -> bool {
    let n = v.len();
    if n <= 1 {
        return true;
    }

    let threshold = min(MAX_INSERTION_SORT_ELEMS,
                        max(MIN_QUICKSORT_ELEMS, INSERTION_SORT_FACTOR / size_of::<T>()));
    if n <= threshold {
        insertion_sort(v, compare);
        return true;
    }
    return false;
}

/// Sort the array with a constant space usage, slowly if it happens to be a very large array.
pub fn insertion_sort<T, C: Fn(&T, &T) -> Ordering>(v: &mut [T], compare: &C) {
    let mut i = 1;
    let n = v.len();
    while i < n {
        let mut j = i;
        while j > 0 && unsafe { compare_idxs(v, j-1, j, compare) } == Greater {
            unsafe { unsafe_swap(v, j, j-1); }
            j -= 1;
        }
        i += 1;
    }
}

/// Sort using the heap sort algorithm; the dumb sorting algorithm that has no pathological case.
#[cold]
#[inline(never)]
pub fn heapsort<T, C: Fn(&T, &T) -> Ordering>(v: &mut [T], compare: &C) {
    let mut end = v.len() as isize;
    heapify(v, compare);
    while end > 0 {
        end -= 1;
        v.swap(0, end as usize);
        Siftdown::siftdown_range(v, 0, end as usize, compare);
    }
}

fn heapify<T, C: Fn(&T, &T) -> Ordering>(v: &mut [T], compare: &C) {
    let mut n = (v.len() as isize).wrapping_sub(1) / 4;
    while n >= 0 {
        Siftdown::siftdown(v, n as usize, compare);
        n -= 1;
    }
}

struct Siftup<'a, T: 'a> {
    new: Option<T>,
    v: &'a mut [T],
    pos: usize,
}

impl<'a, T: 'a> Siftup<'a, T> {
    fn siftup<C: Fn(&T, &T) -> Ordering>(v_: &mut [T], start: usize, pos_: usize, compare: &C) {
        unsafe {
            let mut this = Siftup{
                new: Some(ptr::read(v_.get_unchecked_mut(pos_))),
                v: v_,
                pos: pos_,
            };
            let mut parent = this.pos.wrapping_sub(1) / 4;
            while this.pos > start && compare(this.new.as_ref().unchecked_unwrap(), this.v.get_unchecked(parent)) == Greater {
                copy(this.v.get_unchecked(parent), this.v.get_unchecked_mut(this.pos));
                this.pos = parent;
                parent = this.pos.wrapping_sub(1) / 4;
            }
            // siftup dropped here
        }
    }
}

impl<'a, T: 'a> Drop for Siftup<'a, T> {
    fn drop(&mut self) {
        unsafe {
            copy(self.new.as_ref().unchecked_unwrap(), self.v.get_unchecked_mut(self.pos));
            ptr::write(&mut self.new, None);
        }
    }
}

struct Siftdown<'a, T: 'a> {
    new: Option<T>,
    v: &'a mut [T],
    pos: usize,
}

impl<'a, T: 'a> Siftdown<'a, T> {
    fn siftdown_range<C: Fn(&T, &T) -> Ordering>(v_: &mut [T], pos_: usize, end: usize, compare: &C) {
        let pos = unsafe {
            let mut this = Siftdown{
                new: Some(ptr::read(v_.get_unchecked_mut(pos_))),
                v: v_,
                pos: pos_,
            };

            let mut m_left = 4 * this.pos + 2;
            while m_left < end {
                let left = m_left - 1;
                let m_right = m_left + 1;
                let right = m_left + 2;
                let largest_left = if compare_idxs(this.v, left, m_left, compare) == Less {
                    m_left
                } else {
                    left
                };
                let largest_right = if right < end && compare_idxs(this.v, m_right, right, compare) == Less {
                    right
                } else {
                    m_right
                };
                let child = if m_right < end && compare_idxs(this.v, largest_left, largest_right, compare) == Less {
                    largest_right
                } else {
                    largest_left
                };
                copy(this.v.get_unchecked(child), this.v.get_unchecked_mut(this.pos));
                this.pos = child;
                m_left = 4 * this.pos + 2;
            }
            let left = m_left - 1;
            if left < end {
                copy(this.v.get_unchecked(left), this.v.get_unchecked_mut(this.pos));
                this.pos = left;
            }

            this.pos
            // this dropped here
        };
        Siftup::siftup(v_, pos_, pos, compare);
    }

    fn siftdown<C: Fn(&T, &T) -> Ordering>(v: &mut [T], pos: usize, compare: &C) {
        let len = v.len();
        Siftdown::siftdown_range(v, pos, len, compare);
    }
}

impl<'a, T: 'a> Drop for Siftdown<'a, T> {
    fn drop(&mut self) {
        unsafe {
            copy(self.new.as_ref().unchecked_unwrap(), self.v.get_unchecked_mut(self.pos));
            ptr::write(&mut self.new, None);
        }
    }
}

// Utilities.

unsafe fn swap_many<T>(v: &mut [T], a: usize, b: usize, n: usize) {
    let mut i = 0;
    while i < n {
        unsafe_swap(v, a + i, b + i);
        i += 1;
    }
}

fn log2(x: usize) -> u32 {
    if x <= 1 { return 0; }
    let n = x.leading_zeros();
    size_of::<usize>() as u32 * 8 - n
}

#[inline(always)]
unsafe fn compare_idxs<T, C: Fn(&T, &T) -> Ordering>(v: &[T], a: usize, b: usize, compare: &C) -> Ordering {
    let x = v.get_unchecked(a);
    let y = v.get_unchecked(b);
    compare(x, y)
}

#[inline(always)]
fn compare_idxs_safe<T, C: Fn(&T, &T) -> Ordering>(v: &[T], a: usize, b: usize, compare: &C) -> Ordering {
    compare(&v[a], &v[b])
}

#[inline(always)]
unsafe fn unsafe_swap<T>(v: &mut[T], a: usize, b: usize) {
    ptr::swap(v.get_unchecked_mut(a) as *mut T, v.get_unchecked_mut(b) as *mut T);
}

#[inline(always)]
unsafe fn copy<T>(a: *const T, b: *mut T) {
    ptr::write(b, ptr::read(a))
}

#[inline(always)]
unsafe fn unsafe_split_at_mut<T>(v: &mut [T], pos: usize) -> (&mut [T], &mut [T]) {
    (
        slice::from_raw_parts_mut(v.get_unchecked_mut(0) as *mut T, pos),
        slice::from_raw_parts_mut(v.get_unchecked_mut(pos) as *mut T, v.len().wrapping_sub(pos)),
    )
}

