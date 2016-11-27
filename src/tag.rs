use std::fmt;
use std::hash::{Hash, Hasher};
use std::marker::PhantomData;
use std::mem::{size_of, uninitialized};

/// A struct for wrapping tagged values to prevent accidentally calling
pub struct TagWrapper<V: ?Sized, TM>(PhantomData<TM>, pub V);

impl<TM, V: Clone> Clone for TagWrapper<V, TM> {
    fn clone(&self) -> Self {
        TagWrapper(PhantomData, self.1.clone())
    }

    fn clone_from(&mut self, source: &Self) {
        self.1.clone_from(&source.1)
    }
}
impl<TM, V: Copy> Copy for TagWrapper<V, TM> {}

impl<TM, V: fmt::Debug> fmt::Debug for TagWrapper<V, TM> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self.1)
    }
}

impl<TM, V: Hash> Hash for TagWrapper<V, TM> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.1.hash(state);
    }
}

/// A trait for getting the number of options associated with a `TaggableValue` of a specific size
pub trait TagOptions: Copy+Eq+fmt::Debug {}

/// An enum for representing 1 option
#[derive(Clone,Copy,Debug,PartialEq,Eq,PartialOrd,Ord,Hash)]
pub enum One {
    Untagged,
    Tagged,
}

impl TagOptions for One {}

/// An enum for representing 2 options
#[derive(Clone,Copy,Debug,PartialEq,Eq,PartialOrd,Ord,Hash)]
pub enum Two {
    Option0,
    Option1,
}

impl TagOptions for Two {}

/// A trait representing a value which can have some space dedicated to use for tagging a union
/// If you implement this trait incorrectly, you will break memory safety.
pub unsafe trait TaggableValue<TM, Count: TagOptions> {
    /// Untags a value and returns it
    #[inline]
    fn untag(v: TagWrapper<Self, TM>) -> Self;
    /// Untags a value in place
    #[inline]
    fn untag_in_place(v: &mut TagWrapper<Self, TM>);
    /// Gets the tag associated with a value
    #[inline]
    fn get_tag(v: &TagWrapper<Self, TM>) -> Count;
    /// Tag a value and return it
    #[inline]
    fn tag(v: Self, o: Count) -> TagWrapper<Self, TM>;
    /// Tag a value in place
    #[inline]
    fn tag_in_place(v: &mut TagWrapper<Self, TM>, o: Count);
    /// Change the tag on an already tagged value
    #[inline]
    fn change_tag(v: &mut TagWrapper<Self, TM>, o: Count);

    /// Return a tagged (but otherwise uninitialized) value
    #[inline]
    unsafe fn uninitialized_from_tag(o: Count) -> TagWrapper<Self, TM>;

    /// A helper debug printing a value as though it weren't tagged
    #[inline]
    fn fmt_untagged(v: &TagWrapper<Self, TM>, f: &mut fmt::Formatter) -> fmt::Result
    where Self: fmt::Debug;

    /// A helper testing equality between tagged items
    #[inline]
    fn eq(a: &TagWrapper<Self, TM>, b: &TagWrapper<Self, TM>) -> bool
    where Self: PartialEq;

    /// A helper testing inequality between tagged items
    #[inline]
    fn ne(a: &TagWrapper<Self, TM>, b: &TagWrapper<Self, TM>) -> bool
    where Self: PartialEq;
}

/// A marker trait guarantees that `untag_in_place` is a no-op for items tagged with `Option0`
/// Items tagged with Option0 should be able to be directly accessed as if they were not tagged
/// in any way.
pub unsafe trait UntaggedZero<TM, Count: TagOptions>: TaggableValue<TM, Count> {}

unsafe impl<T, TM> TaggableValue<TM, One> for T
where T: UntaggedZero<TM, Two> {
    #[inline]
    fn untag(v: TagWrapper<T, TM>) -> T {
        TaggableValue::<TM, Two>::untag(v)
    }
    #[inline]
    fn untag_in_place(v: &mut TagWrapper<T, TM>) {
        TaggableValue::<TM, Two>::untag_in_place(v)
    }
    #[inline]
    fn get_tag(v: &TagWrapper<T, TM>) -> One {
        match TaggableValue::<TM, Two>::get_tag(v) {
            Two::Option0 => One::Untagged,
            Two::Option1 => One::Tagged,
        }
    }
    #[inline]
    fn tag(v: Self, o: One) -> TagWrapper<T, TM> {
        let o = match o {
            One::Untagged => Two::Option0,
            One::Tagged => Two::Option1,
        };
        TaggableValue::<TM, Two>::tag(v, o)
    }
    #[inline]
    fn tag_in_place(v: &mut TagWrapper<T, TM>, o: One) {
        let o = match o {
            One::Untagged => Two::Option0,
            One::Tagged => Two::Option1,
        };
        TaggableValue::<TM, Two>::tag_in_place(v, o)
    }
    #[inline]
    fn change_tag(v: &mut TagWrapper<T, TM>, o: One) {
        let o = match o {
            One::Untagged => Two::Option0,
            One::Tagged => Two::Option1,
        };
        TaggableValue::<TM, Two>::change_tag(v, o)
    }
    #[inline]
    unsafe fn uninitialized_from_tag(o: One) -> TagWrapper<T, TM> {
        let o = match o {
            One::Untagged => Two::Option0,
            One::Tagged => Two::Option1,
        };
        TaggableValue::<TM, Two>::uninitialized_from_tag(o)
    }


    #[inline]
    fn fmt_untagged(v: &TagWrapper<T, TM>, f: &mut fmt::Formatter) -> fmt::Result
    where Self: fmt::Debug {
        TaggableValue::<TM, Two>::fmt_untagged(v, f)
    }

    #[inline]
    fn eq(a: &TagWrapper<T, TM>, b: &TagWrapper<T, TM>) -> bool
    where Self: PartialEq {
        TaggableValue::<TM, Two>::eq(a, b)
    }

    #[inline]
    fn ne(a: &TagWrapper<T, TM>, b: &TagWrapper<T, TM>) -> bool
    where Self: PartialEq {
        TaggableValue::<TM, Two>::ne(a, b)
    }
}

/// A struct represnting the method of tagging using only the `MSB` of a number
#[derive(Clone,Copy,Debug,PartialEq,Eq,PartialOrd,Ord,Hash)]
pub struct TagMSB;
macro_rules! msb_set { ($t:ty) =>  {1 << (8*size_of::<$t>() - 1)} }
macro_rules! tag_msb { ($($t:ty)+) =>  {$(
    unsafe impl UntaggedZero<TagMSB, Two> for $t{}
    unsafe impl TaggableValue<TagMSB, Two> for $t {
        #[inline]
        fn untag(v: TagWrapper<$t, TagMSB>) -> $t { v.1 & !msb_set!($t) }
        #[inline]
        fn untag_in_place(v: &mut TagWrapper<$t, TagMSB>) { v.1 &= !msb_set!($t) }
        #[inline]
        fn get_tag(v: &TagWrapper<$t, TagMSB>) -> Two {
            if v.1 < msb_set!($t) { Two::Option0 } else { Two::Option1 }
        }
        #[inline]
        fn tag(v: Self, o: Two) -> TagWrapper<$t, TagMSB> {
            match o {
                Two::Option0 => TagWrapper(PhantomData, v & !msb_set!($t)),
                Two::Option1 => TagWrapper(PhantomData, v | msb_set!($t)),
            }
        }
        #[inline]
        fn tag_in_place(v: &mut TagWrapper<$t, TagMSB>, o: Two) {
            match o {
                Two::Option0 => v.1 &= !msb_set!($t),
                Two::Option1 => v.1 |= msb_set!($t),
            }
        }
        #[inline]
        fn change_tag(v: &mut TagWrapper<$t, TagMSB>, o: Two) {
            Self::tag_in_place(v, o)
        }
        #[inline]
        unsafe fn uninitialized_from_tag(o: Two) -> TagWrapper<$t, TagMSB> {
            Self::tag(uninitialized(), o)
        }


        #[inline]
        fn fmt_untagged(v: &TagWrapper<$t, TagMSB>, f: &mut fmt::Formatter) -> fmt::Result {
            write!(f, "{:?}", TaggableValue::<TagMSB, Two>::untag(*v))
        }

        #[inline]
        fn eq(a: &TagWrapper<$t, TagMSB>, b: &TagWrapper<$t, TagMSB>) -> bool { a.1.eq(&b.1) }

        #[inline]
        fn ne(a: &TagWrapper<$t, TagMSB>, b: &TagWrapper<$t, TagMSB>) -> bool { a.1.ne(&b.1) }
    }
)+}}

tag_msb!{u8 u16 u32 u64 usize}
