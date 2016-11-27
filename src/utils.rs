use std::fmt;

use tag::*;

// This is a separate function to reduce the code size of .expect() itself.
#[inline(never)]
#[cold]
pub fn expect_failed(msg: &str) -> ! {
    panic!("{}", msg)
}

/// Untags a value and returns it
#[inline]
pub fn untag<TM, C, T>(v: TagWrapper<T, TM>) -> T
where C: TagOptions, T: TaggableValue<TM, C> {
    TaggableValue::untag(v)
}

/// Get's the tag associated with a value
#[inline]
pub fn get_tag<TM, C, T>(v: &TagWrapper<T, TM>) -> C
where C: TagOptions, T: TaggableValue<TM, C> {
    TaggableValue::get_tag(v)
}

/// Tags a presently untagged value.
#[inline]
pub fn tag<TM, C, T>(v: T, o: C) -> TagWrapper<T, TM>
where C: TagOptions, T: TaggableValue<TM, C> {
    TaggableValue::tag(v, o)
}

/// Untags a value in place
#[inline]
pub fn borrow_untagged<TM, C, T, F, R>(v: &mut TagWrapper<T, TM>, f: F) -> R
where C: TagOptions, T: TaggableValue<TM, C>, F: FnOnce(C, &mut T) -> R {
    let tag = get_tag(v);
    TaggableValue::untag_in_place(v);
    let r = f(tag, &mut v.1);
    TaggableValue::tag_in_place(v, tag);
    debug_assert_eq!(tag, get_tag(v));
    r
}

/// Changes the tag on a value. This is an unsafe operation because it changes the meaning
/// of some associated memory, meaing this is essentially a transmute
#[inline]
pub unsafe fn change_tag<TM, C, T>(v: &mut TagWrapper<T, TM>, o: C)
where C: TagOptions, T: TaggableValue<TM, C> {
    TaggableValue::change_tag(v, o);
    debug_assert_eq!(get_tag(v), o);
}

/// Returns a tagged (but otherwise uninitialized) value
pub unsafe fn uninitialized_from_tag<TM, C, T>(o: C) -> TagWrapper<T, TM>
where C: TagOptions, T: TaggableValue<TM, C> {
    let v = TaggableValue::uninitialized_from_tag(o);
    debug_assert_eq!(get_tag(&v), o);
    v
}


/// A helper debug printing a value as though it weren't tagged
#[inline]
pub fn fmt_untagged<TM, C, T>(v: &TagWrapper<T, TM>, f: &mut fmt::Formatter) -> fmt::Result
where C: TagOptions, T: TaggableValue<TM, C> + fmt::Debug {
    TaggableValue::fmt_untagged(v, f)
}

/// A helper testing equality between tagged items
#[inline]
pub fn eq<TM, C, T>(a: &TagWrapper<T, TM>, b: &TagWrapper<T, TM>) -> bool
where C: TagOptions, T: TaggableValue<TM, C> + PartialEq {
    TaggableValue::eq(a, b)
}

/// A helper testing inequality between tagged items
#[inline]
pub fn ne<TM, C, T>(a: &TagWrapper<T, TM>, b: &TagWrapper<T, TM>) -> bool
where C: TagOptions, T: TaggableValue<TM, C> + PartialEq {
    TaggableValue::ne(a, b)
}
