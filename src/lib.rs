//! Space-efficient enum values.
//!
//! For the moment only option types are implemented, as true enums would require something
//! like a `const fn` version of `size_of`.

use std::fmt;
use std::hash::{Hash, Hasher};
use std::marker::PhantomData;
use std::mem::{replace,size_of,uninitialized};
use std::ptr::{read,write};

/// A struct for representing enums with 2 options
pub struct Two;

/// A trait for getting the number of options associated with a `TaggableValue` of a specific size
pub trait TagOptions { type Options: Copy+Eq+fmt::Debug; }

/// An enum with 2 options
#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub enum TwoOptions {Zero,One,}
impl TagOptions for Two { type Options = TwoOptions; }

/// A trait representing a value which can have some space dedicated to use for tagging a union
pub unsafe trait TaggableValue<TaggingMethod, Count: TagOptions> {
    /// Untags a value and returns it
    #[inline]
    fn untag(self) -> Self;
    /// Untags a value in place
    #[inline]
    fn untag_in_place(&mut self);
    /// Get's the tag associated with a value
    #[inline]
    fn get_tag(&self) -> Count::Options;
    /// A helper for changing the tag of a value
    #[inline]
    fn change_tag_helper(v: &mut Self, o: Count::Options);
    /// A helper for initializing the tag of a value
    #[inline]
    fn tag_helper(v: &mut Self, o: Count::Options) {
        TaggableValue::change_tag_helper(v, o);
    }

    /// A helper debug printing a value as though it weren't tagged
    #[inline]
    fn fmt_untagged(a: &Self, f: &mut fmt::Formatter) -> fmt::Result
    where Self: fmt::Debug;

    /// A helper testing equality between tagged items
    #[inline]
    fn eq(a: &Self, b: &Self) -> bool
    where Self: PartialEq;

    /// A helper testing inequality between tagged items
    #[inline]
    fn ne(a: &Self, b: &Self) -> bool
    where Self: PartialEq;
}

/// Tags a value
#[inline]
fn tag<TM, C: TagOptions, T: TaggableValue<TM, C>>(v: &mut T, o: C::Options) {
    TaggableValue::tag_helper(v, o);
    debug_assert_eq!(v.get_tag(), o);
}

/// Changes the tag on a value. This is an unsafe operation because it changes the meaning
/// of some associated memory, meaing this is essentially a transmute
#[inline]
unsafe fn change_tag<TM, C: TagOptions, T: TaggableValue<TM, C>>(v: &mut T, o: C::Options) {
    TaggableValue::change_tag_helper(v, o);
    debug_assert_eq!(v.get_tag(), o);
}


/// A struct represnting the method of tagging using only the `MSB` of a number
pub struct TagMSB;
macro_rules! msb_set { ($t:ty) =>  {1 << (8*size_of::<$t>() - 1)} }
macro_rules! tag_msb { ($($t:ty)+) =>  {$(
    unsafe impl TaggableValue<TagMSB, Two> for $t {
        #[inline]
        fn untag(self) -> Self { self & !msb_set!($t) }
        #[inline]
        fn untag_in_place(&mut self) { *self &= !msb_set!($t) }
        #[inline]
        fn get_tag(&self) -> TwoOptions {
            if *self < msb_set!($t) { TwoOptions::Zero } else { TwoOptions::One }
        }
        #[inline]
        fn change_tag_helper(v: &mut Self, o: TwoOptions) {
            match o {
                TwoOptions::Zero => *v &= !msb_set!($t),
                TwoOptions::One => *v |= msb_set!($t),
            }
        }

        #[inline]
        fn fmt_untagged(a: &Self, f: &mut fmt::Formatter) -> fmt::Result {
            write!(f, "{:?}", a.untag())
        }

        #[inline]
        fn eq(a: &Self, b: &Self) -> bool { a.eq(b) }

        /// A helper testing inequality untagged
        #[inline]
        fn ne(a: &Self, b: &Self) -> bool { a.ne(b) }

    }
)+}}

tag_msb!{u8 u16 u32 u64 usize}

/// An option type similar to `Option<A>`, but where no extra data is used. Instead, some of
/// the space in `A` is used to "tag the union".
///
/// The one true downside is that it is impossible to get `&A` from `&EfficientOption`. The reason
/// for this is that doing so would expose the private tag info.
pub struct EfficientOption<A, TaggingMethod=TagMSB>(A,PhantomData<TaggingMethod>)
where A: TaggableValue<TaggingMethod, Two>;

impl<TaggingMethod, A: Clone> Clone for EfficientOption<A, TaggingMethod>
where A: TaggableValue<TaggingMethod, Two> {
    fn clone(&self) -> Self {
        EfficientOption(self.0.clone(), PhantomData)
    }
}
impl<TaggingMethod, A: Copy> Copy for EfficientOption<A, TaggingMethod>
where A: TaggableValue<TaggingMethod, Two> {}

impl<TaggingMethod, A> Default for EfficientOption<A, TaggingMethod>
where A: TaggableValue<TaggingMethod, Two> {
    fn default() -> Self {
        EfficientOption::none()
    }
}

impl<TaggingMethod, A: fmt::Debug> fmt::Debug for EfficientOption<A, TaggingMethod>
where A: TaggableValue<TaggingMethod, Two> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if self.0.get_tag() == TwoOptions::Zero {
            write!(f, "EfficientOption(None)")
        } else {
            write!(f, "EfficientOption(Some(")?;
            TaggableValue::fmt_untagged(&self.0, f)?;
            write!(f, "))")
        }
    }
}

impl<TaggingMethod, A: PartialEq> PartialEq for EfficientOption<A, TaggingMethod>
where A: TaggableValue<TaggingMethod, Two> {
    fn eq(&self, other: &Self) -> bool {
        (self.is_none() && other.is_none()) ||
        TaggableValue::eq(&self.0, &other.0)
    }

    fn ne(&self, other: &Self) -> bool {
        (self.is_some() || other.is_some()) &&
        TaggableValue::ne(&self.0, &other.0)
    }
}
impl<TaggingMethod, A: Eq> Eq for EfficientOption<A, TaggingMethod>
where A: TaggableValue<TaggingMethod, Two> {}

impl<TaggingMethod, A: Hash> Hash for EfficientOption<A, TaggingMethod>
where A: TaggableValue<TaggingMethod, Two> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.hash(state);
    }
}

impl<TaggingMethod, A> From<Option<A>> for EfficientOption<A, TaggingMethod>
where A: TaggableValue<TaggingMethod, Two> {
    fn from(a: Option<A>) -> Self {
        Self::new(a)
    }
}

impl<TaggingMethod, A> Into<Option<A>> for EfficientOption<A, TaggingMethod>
where A: TaggableValue<TaggingMethod, Two> {
    fn into(self) -> Option<A> { self.destructure() }
}

impl<TaggingMethod, A> EfficientOption<A, TaggingMethod>
where A: TaggableValue<TaggingMethod, Two> {
    /// Constructs a new `EfficientOption`
    pub fn new(a: Option<A>) -> Self {
        if let Some(a) = a { Self::some(a) } else { Self::none() }
    }

    /// Constructs an empty `EfficientOption`
    pub fn none() -> Self {
        let mut a = unsafe { uninitialized() };
        tag(&mut a, TwoOptions::Zero);
        EfficientOption(a, PhantomData)
    }

    /// Constructs an `EfficientOption` from an `A` value
    pub fn some(mut a: A) -> Self {
        tag(&mut a, TwoOptions::One);
        EfficientOption(a, PhantomData)
    }

    /// Destructures an `EfficientOption`
    pub fn destructure(self) -> Option<A> {
        if self.is_none() { None }
        else { Some(self.0.untag()) }
    }

    /// Returns `true` if the option is a `Some` value.
    #[inline]
    pub fn is_some(&self) -> bool { self.0.get_tag() == TwoOptions::One }

    /// Returns `true` if the option is a `None` value.
    #[inline]
    pub fn is_none(&self) -> bool { !self.is_some() }

    /// Maps the value to a result
    pub fn map<R, F: FnOnce(Option<&mut A>)-> R>(&mut self, f: F) -> R {
        let a = self.0.get_tag();
        match a {
            TwoOptions::Zero => f(None),
            TwoOptions::One => {
                self.0.untag_in_place();
                let r = f(Some(&mut self.0));
                tag(&mut self.0, a);
                r
            },
        }
    }
}

/// An option type similar to `(A, Option<B>)`, but where no extra data is used. Instead, some of
/// the space in `A` is used to "tag the union".
///
/// The one true downside is that it is impossible to get `&A` from `&EfficientOptionTuple`. The reason
/// for this is that doing so would expose the private tag info.
pub struct EfficientOptionTuple<A, B, TaggingMethod=TagMSB>(A, B, PhantomData<TaggingMethod>)
where A: TaggableValue<TaggingMethod, Two>;

impl<TaggingMethod, A: Clone, B: Clone> Clone for EfficientOptionTuple<A, B, TaggingMethod>
where A: TaggableValue<TaggingMethod, Two> {
    fn clone(&self) -> Self {
        let b = unsafe { self.ref_b().map_or(uninitialized(), Clone::clone) };
        EfficientOptionTuple(self.0.clone(), b, PhantomData)
    }

    fn clone_from(&mut self, source: &Self) {
        self.0 = source.0.clone();
        if let Some(b) = source.ref_b() { self.1 = b.clone(); }
    }
}
impl<TaggingMethod, A: Copy, B: Copy> Copy for EfficientOptionTuple<A, B, TaggingMethod>
where A: TaggableValue<TaggingMethod, Two> {}

impl<TaggingMethod, A: Default, B> Default for EfficientOptionTuple<A, B, TaggingMethod>
where A: TaggableValue<TaggingMethod, Two> {
    fn default() -> Self {
        EfficientOptionTuple::none(Default::default())
    }
}

impl<TaggingMethod, A: fmt::Debug, B: fmt::Debug> fmt::Debug for EfficientOptionTuple<A, B, TaggingMethod>
where A: TaggableValue<TaggingMethod, Two> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if let Some(b) = self.ref_b() {
            write!(f, "EfficientOptionTuple(")?;
            TaggableValue::fmt_untagged(&self.0, f)?;
            write!(f, ", Some({:?}))", b)
        } else {
            write!(f, "EfficientOptionTuple(")?;
            TaggableValue::fmt_untagged(&self.0, f)?;
            write!(f, ", None)")
        }
    }
}

impl<TaggingMethod, A: PartialEq, B: PartialEq> PartialEq for EfficientOptionTuple<A, B, TaggingMethod>
where A: TaggableValue<TaggingMethod, Two> {
    fn eq(&self, other: &Self) -> bool {
        TaggableValue::eq(&self.0, &other.0) && match (self.ref_b(), other.ref_b()) {
            (Some(s), Some(o)) => *s == *o,
            (None, None) => true,
            _ => false,
        }
    }

    fn ne(&self, other: &Self) -> bool {
        TaggableValue::ne(&self.0, &other.0) || match (self.ref_b(), other.ref_b()) {
            (Some(s), Some(o)) => *s != *o,
            (None, None) => false,
            _ => true,
        }
    }
}
impl<TaggingMethod, A: Eq, B: Eq> Eq for EfficientOptionTuple<A, B, TaggingMethod>
where A: TaggableValue<TaggingMethod, Two> {}

impl<TaggingMethod, A: Hash, B: Hash> Hash for EfficientOptionTuple<A, B, TaggingMethod>
where A: TaggableValue<TaggingMethod, Two> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.hash(state);
        if let Some(b) = self.ref_b() { b.hash(state) }
    }
}

impl<TaggingMethod, A, B> From<(A, Option<B>)> for EfficientOptionTuple<A, B, TaggingMethod>
where A: TaggableValue<TaggingMethod, Two> {
    fn from((a, b): (A, Option<B>)) -> Self {
        Self::new(a, b)
    }
}

impl<TaggingMethod, A, B> Into<(A, Option<B>)> for EfficientOptionTuple<A, B, TaggingMethod>
where A: TaggableValue<TaggingMethod, Two> {
    fn into(self) -> (A, Option<B>) { self.destructure() }
}

impl<TaggingMethod, A, B> EfficientOptionTuple<A, B, TaggingMethod>
where A: TaggableValue<TaggingMethod, Two> {
    /// Constructs a new `EfficientOptionTuple`
    pub fn new(a: A, b: Option<B>) -> Self {
        if let Some(b) = b { Self::some(a, b) } else { Self::none(a) }
    }

    /// Constructs an `EfficientOptionTuple` with no `B` value
    pub fn none(mut a: A) -> Self {
        tag(&mut a, TwoOptions::Zero);
        let b = unsafe { uninitialized() };
        EfficientOptionTuple(a, b, PhantomData)
    }

    /// Constructs an `EfficientOptionTuple` with a `B` value
    pub fn some(mut a: A, b: B) -> Self {
        tag(&mut a, TwoOptions::One);
        EfficientOptionTuple(a, b, PhantomData)
    }

    /// Destructures an `EfficientOptionTuple`
    pub fn destructure(self) -> (A, Option<B>) {
        if self.is_none() { (self.0.untag(), None) }
        else { (self.0.untag(), Some(self.1)) }
    }

    /// Returns `true` if the option is a `Some` value.
    #[inline]
    pub fn is_some(&self) -> bool { self.0.get_tag() == TwoOptions::One }

    /// Returns `true` if the option is a `None` value.
    #[inline]
    pub fn is_none(&self) -> bool { !self.is_some() }

    /// Clones the `A` value
    pub fn clone_a(self) -> A
    where A: Clone { self.0.clone().untag() }

    /// Clones the `B` value if one exists
    pub fn clone_b(self) -> Option<B>
    where B: Clone {
        self.ref_b().map(Clone::clone)
    }

    /// Gets a reference to the `B` value if one exists
    pub fn ref_b(&self) -> Option<&B> {
        if self.is_none() { None }
        else { Some(&self.1) }
    }

    /// Gets mutable a reference to the `B` value if one exists
    pub fn mut_b(&mut self) -> Option<&mut B> {
        match self.0.get_tag() {
            TwoOptions::Zero => None,
            TwoOptions::One => Some(&mut self.1),
        }
    }

    /// Replaces the `A` value
    pub fn replace_a(&mut self, mut a: A) -> A {
        tag(&mut a, self.0.get_tag());
        replace(&mut self.0, a).untag()
    }

    /// Replaces the `B` value
    pub fn replace_b(&mut self, b: Option<B>) -> Option<B> {
        match (self.0.get_tag(), b) {
            (TwoOptions::Zero, None) => None,
            (TwoOptions::Zero, Some(b)) => { unsafe {
                write(&mut self.1 as *mut B, b);
                change_tag(&mut self.0, TwoOptions::One);
                None
            }},
            (TwoOptions::One, None) => { unsafe {
                change_tag(&mut self.0, TwoOptions::Zero);
                Some(read(&self.1 as *const B))
            }},
            (TwoOptions::One, Some(b)) => Some(replace(&mut self.1, b)),
        }
    }

    /// Maps the `A` and `B` values to a result
    pub fn map<R, F: FnOnce(&mut A, Option<&mut B>)-> R>(&mut self, f: F) -> R {
        let a = self.0.get_tag();
        self.0.untag_in_place();
        let r = match a {
            TwoOptions::Zero => f(&mut self.0, None),
            TwoOptions::One => f(&mut self.0, Some(&mut self.1)),
        };
        tag(&mut self.0, a);
        r
    }
}


#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_option_new() {
        let a = EfficientOption::<usize>::some(10);
        let b = EfficientOption::<usize>::new(Some(10));
        assert_eq!(a.destructure(), Some(10));
        assert_eq!(b.destructure(), Some(10));
        assert_eq!(a, b);

        let a = EfficientOption::<usize>::none();
        let b = EfficientOption::<usize>::new(None);
        assert_eq!(a.destructure(), None);
        assert_eq!(b.destructure(), None);
        assert_eq!(a, b);
    }

    #[test]
    fn test_option_simple() {
        let v = EfficientOption::<usize>::some(10);
        assert!(!v.is_none());
        assert!(v.is_some());

        let v = EfficientOption::<usize>::none();
        assert!(v.is_none());
        assert!(!v.is_some());
    }

    #[test]
    fn test_option_mut() {
        let mut v = EfficientOption::<usize>::some(10);
        assert_eq!(v.destructure(), Some(10));

        v.map(|a| *a.unwrap() = 11 );
        assert_eq!(v.destructure(), Some(11));

        v = EfficientOption::<usize>::none();
        assert_eq!(v.destructure(), None);

        v.map(|a| assert_eq!(a, None));
        assert_eq!(v.destructure(), None);
    }

    #[test]
    fn test_option_tuple_new() {
        let a = EfficientOptionTuple::<usize, usize>::some(10, 15);
        let b = EfficientOptionTuple::<usize, usize>::new(10, Some(15));
        assert_eq!(a.destructure(), (10, Some(15)));
        assert_eq!(b.destructure(), (10, Some(15)));
        assert_eq!(a, b);

        let a = EfficientOptionTuple::<usize, usize>::none(10);
        let b = EfficientOptionTuple::<usize, usize>::new(10, None);
        assert_eq!(a.destructure(), (10, None));
        assert_eq!(b.destructure(), (10, None));
        assert_eq!(a, b);
    }

    #[test]
    fn test_option_tuple_simple() {
        let v = EfficientOptionTuple::<usize, usize>::some(10, 15);
        assert!(!v.is_none());
        assert!(v.is_some());
        assert_eq!(v.clone_a(), 10);
        assert_eq!(v.clone_b(), Some(15));
        assert_eq!(*v.ref_b().unwrap(), 15);
        assert_eq!(v.destructure(), (10, Some(15)));

        let v = EfficientOptionTuple::<usize, usize>::none(10);
        assert!(v.is_none());
        assert!(!v.is_some());
        assert_eq!(v.clone_a(), 10);
        assert_eq!(v.clone_b(), None);
        assert_eq!(v.ref_b(), None);
        assert_eq!(v.destructure(), (10, None));
    }

    #[test]
    fn test_option_tuple_mut() {
        let mut v = EfficientOptionTuple::<usize, usize>::some(10, 15);
        assert_eq!(v.destructure(), (10, Some(15)));

        *v.mut_b().unwrap() = 16;
        assert_eq!(v.destructure(), (10, Some(16)));

        v.replace_a(11);
        assert_eq!(v.destructure(), (11, Some(16)));

        v.replace_b(Some(17));
        assert_eq!(v.destructure(), (11, Some(17)));

        v.replace_b(None);
        assert_eq!(v.destructure(), (11, None));
        assert_eq!(v.mut_b(), None);

        v.map(|a, b| {
            *a = 12;
            assert_eq!(b, None);
        });
        assert_eq!(v.destructure(), (12, None));

        v.replace_a(13);
        assert_eq!(v.destructure(), (13, None));

        v.replace_b(Some(18));
        assert_eq!(v.destructure(), (13, Some(18)));

        v.map(|a, b| {
            *a = 14;
            *b.unwrap() = 19;
        });
        assert_eq!(v.destructure(), (14, Some(19)));
    }
}
