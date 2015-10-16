use std::cmp::Ordering;
use std::cmp::Ordering::*;
use std::cmp::{min, max};
use std::mem::{size_of, swap, forget, replace};
use std::ops::{Deref, DerefMut};
use std::ptr;
use std::usize;
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
    let n = v.len();
    unsafe {
        let (start, end) = get_pivots(v, compare, 0, 1, n, n);
        quicksort(v, 0, start, end, n, compare, rec, heapsort_depth);
    }
}

unsafe fn get_pivots<T, C: Fn(&T, &T) -> Ordering>(v: &mut [T], compare: &C, start_less: usize, start: usize, start_greater: usize, end_greater: usize) -> (usize, usize) {
    // Ideal pivot selection based on: http://users.aims.ac.za/~mackay/sorting/sorting.html
    let n_tot = end_greater - start_less;
    let n_unsorted = start_greater - start;
    let m_needed = max(sqrt(n_tot / log2(n_tot) as usize), 7);
    let m_curr = n_tot - n_unsorted;
    let mut ret_start = start;
    let mut ret_end = start_greater;
    if m_curr < m_needed {
        let m_missing = m_needed - m_curr;
        for i in 0 .. m_missing {
            let pos = start + (((ret_end - ret_start) / m_missing) * i);
            if compare_idxs(v, pos, ret_start - 1, compare) == Greater {
                unsafe_swap(v, pos, ret_end - 1);
                let mut n = ret_end;
                ret_end -= 1;
                while n < end_greater && compare_idxs(v, n - 1, n, compare) == Greater {
                    unsafe_swap(v, n - 1, n);
                    n += 1;
                }
            } else {
                unsafe_swap(v, pos, ret_start);
                let mut n = ret_start;
                ret_start += 1;
                while n > start_less && compare_idxs(v, n, n - 1, compare) == Less {
                    unsafe_swap(v, n, n - 1);
                    n -= 1;
                }
            }
        }
    }
    let even_mask = usize::MAX - 1;
    while (end_greater - ret_end) & even_mask < (ret_start - start_less) & even_mask {
        unsafe_swap(v, ret_start - 1, ret_end - 1);
        ret_start -= 1;
        ret_end -= 1;
    }
    while end_greater - ret_end > ret_start - start_less {
        unsafe_swap(v, ret_start, ret_end);
        ret_start += 1;
        ret_end += 1;
    }
    (ret_start, ret_end)
}

// Quicksort the list, assuming the pivot is right before the numbers to be
// sorted. That is, the list has this structure:
// [NNNN][___][NNN]
// ^     ^    ^   ^
// |     start|   |
// start_less end end_greater
// Where the N's are already sorted.
unsafe fn quicksort<T, C: Fn(&T, &T) -> Ordering>(v: &mut [T], start_less: usize, start: usize, end: usize, end_greater: usize, compare: &C, rec: u32, heapsort_depth: u32) {
    if rec > heapsort_depth {
        heapsort(v, compare);
    } else if compare_idxs(v, start-1, end, compare) == Equal {
        fat_quicksort(v, start_less, start, end, end_greater, compare, rec, heapsort_depth);
    } else {
        double_quicksort(v, start_less, start, end, end_greater, compare, rec, heapsort_depth);
    }
}

// Quicksort the list, using two pivots:
// [LLLP][___][QGGG]
// ^     ^    ^   ^
// |     start|   |
// start_less end end_greater
unsafe fn double_quicksort<T, C: Fn(&T, &T) -> Ordering>(v: &mut [T], start_less: usize, start: usize, end: usize, end_greater: usize, compare: &C, rec: u32, heapsort_depth: u32) {
    let pivot1 = ((start - start_less) / 2) + start_less;
    let pivot2 = ((end_greater - end) / 2) + end;
    let mut less = start;
    let mut greater = end - 1;
    while less <= greater && compare_idxs(v, less, pivot1, compare) == Less {
        less += 1;
    }
    while less <= greater && compare_idxs(v, greater, pivot2, compare) == Greater {
        greater -= 1;
    }
    let mut k = less;
    while k <= greater {
        if compare_idxs(v, k, pivot1, compare) == Less {
            unsafe_swap(v, k, less);
            less += 1;
        } else if compare_idxs(v, k, pivot2, compare) == Greater {
            if compare_idxs(v, greater, pivot1, compare) == Less {
                let vk = ptr::read(v.get_unchecked(k));
                copy(v.get_unchecked(less), v.get_unchecked_mut(k));
                copy(v.get_unchecked(greater), v.get_unchecked_mut(less));
                copy(&vk, v.get_unchecked_mut(greater));
                forget(vk);
                less += 1;
            } else {
                unsafe_swap(v, k, greater);
            }
            greater -= 1;
            while k < greater && compare_idxs(v, greater, pivot2, compare) == Greater {
                greater -= 1;
            }
        }
        k += 1;
    }
    for i in pivot1 .. start {
        let j = start - i + pivot1 - 1;
        unsafe_swap(v, j, less + j - start);
    }
    less -= start - pivot1;
    for i in end .. pivot2 {
        unsafe_swap(v, i, i + greater - end + 1);
    }
    greater += pivot2 - end;
    if !maybe_insertion_sort(&mut v[start_less..less], compare) {
        let (new_start, new_end) = get_pivots(v, compare, start_less, pivot1, less, less);
        quicksort(v, start_less, new_start, new_end, less, compare, rec + 1, heapsort_depth);
    }
    if !maybe_insertion_sort(&mut v[less..greater + 1], compare) {
        let (new_start, new_end) = get_pivots(v, compare, less, less + (start - pivot1), greater + 1 - (pivot2 - end), greater + 1);
        quicksort(v, less, new_start, new_end, greater + 1, compare, rec + 1, heapsort_depth);
    }
    if !maybe_insertion_sort(&mut v[greater + 1..end_greater], compare) {
        let (new_start, new_end) = get_pivots(v, compare, greater + 1, greater + 1, pivot2, end_greater);
        quicksort(v, greater + 1, new_start, new_end, end_greater, compare, rec + 1, heapsort_depth);
    }
}

// Quicksort the list, assuming the pivot is right before the numbers to be
// sorted. That is, the list has this structure:
// [LLLP][___][PGGG]
// ^     ^    ^   ^
// |     start|   |
// start_less end end_greater
// Where both P's are equal.
unsafe fn fat_quicksort<T, C: Fn(&T, &T) -> Ordering>(v: &mut [T], start_less: usize, start: usize, end: usize, end_greater: usize, compare: &C, rec: u32, heapsort_depth: u32) {
    let pivot = start - 1;
    let (mut less, equal, greater) = fat_partition(v, pivot, start, end, compare, rec, heapsort_depth);
    unsafe_swap(v, pivot, less - 1);
    less -= 1;
    if !maybe_insertion_sort(&mut v[start_less..less], compare) {
        let mut middle_lo = ((pivot - start_less) / 2) + start_less;
        for i in middle_lo + 1 .. pivot {
            unsafe_swap(v, i, i - (middle_lo + 1) + less - (pivot - (middle_lo + 1)));
        }
        let (new_start, new_end) = get_pivots(v, compare, start_less, middle_lo + 1, less - (pivot - (middle_lo + 1)), less);
        quicksort(v, start_less, new_start, new_end, less, compare, rec + 1, heapsort_depth);
    }
    if !maybe_insertion_sort(&mut v[equal..end_greater], compare) {
        let mut middle_hi = end + ((pivot - start_less) / 2);
        for i in end .. (middle_hi + 1) {
            unsafe_swap(v, i, i - end + equal);
        }
        let (new_start, new_end) = get_pivots(v, compare, equal, middle_hi + equal + 1 - end, middle_hi + 1, end_greater);
        quicksort(v, equal, new_start, new_end, end_greater, compare, rec + 1, heapsort_depth);
    }
}

// Partition a list based on a out-of-band pivot. Return values correspond to
// this fat partition scheme: (less, equal, greater)
//
// [LLL][EEE][GGG]
//      ^   ^^
//      |   ||
//      less|equal
//          |
//          greater
//
//   less: index of the first number that is not < than the pivot
//   equal: index of the first number that is not <= the pivot
//   greater: index of the last number that is not > the pivot
unsafe fn fat_partition<T, C: Fn(&T, &T) -> Ordering>(v: &mut [T], pivot: usize, start: usize, end: usize, compare: &C, rec: u32, heapsort_depth: u32) -> (usize, usize, usize) {
    let mut equal = start;
    let mut less = start;
    let mut greater = end - 1;
    while equal <= greater && compare_idxs(v, greater, pivot, compare) == Greater {
        greater -= 1;
    }
    while equal <= greater {
        match compare_idxs(v, equal, pivot, compare) {
            Equal => {
                equal += 1;
            }
            Less => {
                unsafe_swap(v, equal, less);
                less += 1;
                equal += 1;
            },
            Greater => {
                unsafe_swap(v, equal, greater);
                greater -= 1;
                while equal <= greater && compare_idxs(v, greater, pivot, compare) == Greater {
                    greater -= 1;
                }
            }
        }
    }
    (less, equal, greater)
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

fn sqrt(x: usize) -> usize {
    (x as f64).sqrt() as usize
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
