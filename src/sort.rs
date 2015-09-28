use std::cmp::Ordering;
use std::cmp::Ordering::*;
use std::cmp::{min, max};
use std::mem::{size_of, swap, forget};
use std::ops::{Deref, DerefMut};
use std::ptr;
use unreachable::{UncheckedOptionExt, unreachable};

#[inline(always)]
unsafe fn copy<T>(a: *const T, b: *mut T) {
    ptr::write(b, ptr::read(a))
}

/// The smallest number of elements that may be quicksorted.
/// Must be at least 9.
const MIN_QUICKSORT_ELEMS: usize = 10;

/// The maximum number of elements to be insertion sorted.
const MAX_INSERTION_SORT_ELEMS: usize = 42;

/// Controls the number of elements to be insertion sorted.
/// Higher values give more insertion sorted elements.
const INSERTION_SORT_FACTOR: usize = 450;

pub fn sort_by<T, C: Fn(&T, &T) -> Ordering>(v: &mut [T], compare: &C) {
    if maybe_insertion_sort(v, compare) { return; }
    let heapsort_depth = (3 * log2(v.len())) / 2;
    do_introsort(v, compare, 0, heapsort_depth);
}

pub fn sort<T: Ord>(v: &mut [T]) {
    sort_by(v, &|a, b| a.cmp(b));
}

fn introsort<T, C: Fn(&T, &T) -> Ordering>(v: &mut [T], compare: &C, rec: u32, heapsort_depth: u32) {
    if maybe_insertion_sort(v, compare) { return; }
    do_introsort(v, compare, rec, heapsort_depth);
}

fn do_introsort<T, C: Fn(&T, &T) -> Ordering>(v: &mut [T], compare: &C, rec: u32, heapsort_depth: u32) {
    macro_rules! maybe_swap(
        ($v: expr, $a: expr, $b: expr, $compare: expr) => {
            if compare_idxs($v, *$a, *$b, $compare) == Greater {
                swap($a, $b);
            }
        }
    );

    if rec > heapsort_depth {
        heapsort(v, compare);
        return;
    }

    let n = v.len();

    // Pivot selection algorithm based on Java's DualPivotQuicksort.

    // Fast approximation of n / 7
    let seventh = (n / 8) + (n / 64) + 1;

    // Pick five element evenly spaced around the middle (inclusive) of the slice.
    let mut e3 = n / 2;
    let mut e2 = e3 - seventh;
    let mut e1 = e3 - 2*seventh;
    let mut e4 = e3 + seventh;
    let mut e5 = e3 + 2*seventh;

    // Sort them with a sorting network.
    unsafe {
        maybe_swap!(v, &mut e1, &mut e2, compare);
        maybe_swap!(v, &mut e4, &mut e5, compare);
        maybe_swap!(v, &mut e3, &mut e5, compare);
        maybe_swap!(v, &mut e3, &mut e4, compare);
        maybe_swap!(v, &mut e2, &mut e5, compare);
        maybe_swap!(v, &mut e1, &mut e4, compare);
        maybe_swap!(v, &mut e1, &mut e3, compare);
        maybe_swap!(v, &mut e2, &mut e4, compare);
        maybe_swap!(v, &mut e2, &mut e3, compare);
    }

    if unsafe { compare_idxs(v, e1, e2, compare) != Equal &&
                compare_idxs(v, e2, e3, compare) != Equal &&
                compare_idxs(v, e3, e4, compare) != Equal &&
                compare_idxs(v, e4, e5, compare) != Equal } {
        // No consecutive pivot candidates are the same, meaning there is some variaton.
        dual_pivot_sort(v, (e1, e2, e3, e4, e5), compare, rec, heapsort_depth);
    } else {
        // Two consecutive pivots candidates where the same.
        // There are probably many similar elements.
        single_pivot_sort(v, e3, compare, rec, heapsort_depth);
    }
}

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

struct DualPivotSortData<'a, T: 'a> {
    v: &'a mut [T],
    less: usize,
    great: usize,
    pivot1: T,
    pivot2: T,
}

enum DualPivotSort<'a, T: 'a> {
    None,
    Some(DualPivotSortData<'a, T>),
}

impl<'a, T: 'a> DualPivotSort<'a, T> {
    #[inline(always)]
    fn new(this: DualPivotSortData<'a, T>) -> Self {
        DualPivotSort::Some(this)
    }

    #[inline(always)]
    fn done(&mut self) {
        let n = self.v.len();
        unsafe {
            let mut this: &mut DualPivotSortData<'a, T> = &mut *self;
            copy(this.v.get_unchecked(this.less - 1), this.v.get_unchecked_mut(0));
            copy(&this.pivot1, this.v.get_unchecked_mut(this.less - 1));
            copy(this.v.get_unchecked(this.great + 1), this.v.get_unchecked_mut(n - 1));
            copy(&this.pivot2, this.v.get_unchecked_mut(this.great + 1));
        }
    }
}

impl<'a, T: 'a> Deref for DualPivotSort<'a, T> {
    type Target = DualPivotSortData<'a, T>;
    #[inline(always)]
    fn deref(&self) -> &DualPivotSortData<'a, T> {
        match self {
            &DualPivotSort::None => unsafe { unreachable() },
            &DualPivotSort::Some(ref x) => x,
        }
    }
}

impl<'a, T: 'a> DerefMut for DualPivotSort<'a, T> {
    #[inline(always)]
    fn deref_mut(&mut self) -> &mut DualPivotSortData<'a, T> {
        match self {
            &mut DualPivotSort::None => unsafe { unreachable() },
            &mut DualPivotSort::Some(ref mut x) => x,
        }
    }
}

impl<'a, T: 'a> Drop for DualPivotSort<'a, T> {
    #[inline(always)]
    fn drop(&mut self) {
        self.done();
        unsafe {
            ptr::write(self, DualPivotSort::None);
        }
    }
}

fn dual_pivot_sort<T, C: Fn(&T, &T) -> Ordering>(v: &mut [T], pivots: (usize, usize, usize, usize, usize),
                                                 compare: &C, rec: u32, heapsort_depth: u32) {
    let n = v.len();
    let (_, p1, _, p2, _) = pivots;
    let (less, great);

    unsafe {
        let mut this = DualPivotSort::new(DualPivotSortData{
            pivot1: ptr::read(v.get_unchecked(p1)),
            pivot2: ptr::read(v.get_unchecked(p2)),
            less: 0,
            great: n - 1,
            v: v,
        });
        {
            let mut this: &mut DualPivotSortData<T> = &mut *this;

            // The first and last elements to be sorted are moved to the locations formerly occupied by the
            // pivots. When partitioning is complete, they are swapped back, and not sorted again.
            copy(this.v.get_unchecked(this.less), this.v.get_unchecked_mut(p1));
            copy(this.v.get_unchecked(this.great), this.v.get_unchecked_mut(p2));

            // Skip elements which are less or greater than the pivot values.
            this.less += 1;
            this.great -= 1;
            while compare(this.v.get_unchecked(this.less), &this.pivot1) == Less { this.less += 1; }
            while compare(this.v.get_unchecked(this.great), &this.pivot2) == Greater { this.great -= 1; }

            // Partitioning
            let mut k = this.less;
            while k <= this.great {
                if compare(this.v.get_unchecked(k), &this.pivot1) == Less {
                    unsafe_swap(this.v, this.less, k);
                    this.less += 1;
                } else if compare(this.v.get_unchecked(k), &this.pivot2) == Greater {
                    if compare(this.v.get_unchecked(this.great), &this.pivot1) == Less {
                        let vk = ptr::read(this.v.get_unchecked(k));
                        copy(this.v.get_unchecked(this.less), this.v.get_unchecked_mut(k));
                        copy(this.v.get_unchecked(this.great), this.v.get_unchecked_mut(this.less));
                        copy(&vk, this.v.get_unchecked_mut(this.great));
                        forget(vk);
                        this.less += 1;
                    } else {
                        unsafe_swap(this.v, this.great, k);
                    }
                    this.great -= 1;
                    while k < this.great && compare(this.v.get_unchecked(this.great), &this.pivot2) == Greater { this.great -= 1; }
                }
                k += 1;
            }
            less = this.less;
            great = this.great;
        }
        this.done();
        forget(this);
    }

    // Sort the left, right, and center parts.
    introsort(&mut v[..less - 1], compare, rec + 1, heapsort_depth);
    introsort(&mut v[less..great + 1], compare, rec + 1, heapsort_depth);
    introsort(&mut v[great + 2..], compare, rec + 1, heapsort_depth);
}

fn single_pivot_sort<T, C: Fn(&T, &T) -> Ordering>(v: &mut [T], pivot: usize, compare: &C, rec: u32, heapsort_depth: u32) {
    let (l, r) = fat_partition(v, pivot, compare);
    let n = v.len();
    if l > 1 {
        introsort(&mut v[..l], compare, rec + 1, heapsort_depth);
    }
    if r > 1 {
        introsort(&mut v[n - r..], compare, rec + 1, heapsort_depth);
    }
}

/// Partitions elements, using the element at `pivot` as pivot.
/// After partitioning, the array looks as following:
/// <<<<<==>>>
/// Return (number of < elements, number of > elements)
fn fat_partition<T, C: Fn(&T, &T) -> Ordering>(v: &mut [T], pivot: usize, compare: &C) -> (usize, usize)  {
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

    return (b - a, d - c);
}

unsafe fn swap_many<T>(v: &mut [T], a: usize, b: usize, n: usize) {
    let mut i = 0;
    while i < n {
        unsafe_swap(v, a + i, b + i);
        i += 1;
    }
}

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
