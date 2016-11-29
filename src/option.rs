use std::fmt;
use std::hash::{Hash, Hasher};
use std::mem::{replace,uninitialized};
use std::ptr::{read,write};

use tag::{One,Two};
use tag::{TaggableValue,TagMSB,TagWrapper};
use utils;


/// An option type similar to `Option<(A, B)>`, but where no extra data is used. Instead, some of
/// the space in `A` is used to "tag the union".
///
/// The one true downside is that it is impossible to get `&A` from `&EfficientOption`. The reason
/// for this is that doing so would expose the private tag info.
pub struct EfficientOption<A, B=(), TM=TagMSB>(TagWrapper<A, TM>, B)
where A: TaggableValue<TM, One>;

impl<TM, A: Clone, B: Clone> Clone for EfficientOption<A, B, TM>
where A: TaggableValue<TM, One> {
    fn clone(&self) -> Self {
        EfficientOption(self.0.clone(), self.1.clone())
    }

    fn clone_from(&mut self, source: &Self) {
        if source.is_some() {
            if self.is_some() {
                self.1.clone_from(&source.1);
            } else {
                let b = source.1.clone();
                unsafe { write(&mut self.1 as *mut B, b); }
            }
            self.0.clone_from(&source.0);
        } else {
            unsafe { utils::change_tag(&mut self.0, One::Tagged); }
        }
    }
}
impl<TM, A: Copy, B: Copy> Copy for EfficientOption<A, B, TM>
where A: TaggableValue<TM, One> {}

impl<TM, A, B> Default for EfficientOption<A, B, TM>
where A: TaggableValue<TM, One> {
    fn default() -> Self {
        EfficientOption::none()
    }
}

impl<TM, A: fmt::Debug, B: fmt::Debug> fmt::Debug for EfficientOption<A, B, TM>
where A: TaggableValue<TM, One> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if self.is_none() {
            write!(f, "EfficientNone")
        } else {
            write!(f, "EfficientSome(")?;
            utils::fmt_untagged(&self.0, f)?;
            write!(f, ", {:?})", self.1)
        }
    }
}

impl<TM, A: PartialEq, B: PartialEq> PartialEq for EfficientOption<A, B, TM>
where A: TaggableValue<TM, One> {
    fn eq(&self, other: &Self) -> bool {
        match (self.is_some(), other.is_some()) {
            (true, true) => utils::eq(&self.0, &other.0) && self.1 == other.1,
            (false, false) => true,
            _ => false,
        }
    }

    fn ne(&self, other: &Self) -> bool {
        match (self.is_some(), other.is_some()) {
            (true, true) => utils::ne(&self.0, &other.0) || self.1 != other.1,
            (false, false) => false,
            _ => true,
        }
    }
}
impl<TM, A: Eq, B: Eq> Eq for EfficientOption<A, B, TM>
where A: TaggableValue<TM, One> {}

impl<TM, A: Hash, B: Hash> Hash for EfficientOption<A, B, TM>
where A: TaggableValue<TM, One> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        if self.is_some() {
            self.0.hash(state);
            self.1.hash(state);
        }
    }
}

impl<TM, A> From<Option<A>> for EfficientOption<A, (), TM>
where A: TaggableValue<TM, One> {
    fn from(a: Option<A>) -> Self {
        Self::new_0(a)
    }
}

impl<TM, A, B> From<Option<(A, B)>> for EfficientOption<A, B, TM>
where A: TaggableValue<TM, One> {
    fn from(a: Option<(A, B)>) -> Self {
        Self::new(a)
    }
}

impl<TM, A, B> Into<Option<(A, B)>> for EfficientOption<A, B, TM>
where A: TaggableValue<TM, One> {
    fn into(self) -> Option<(A, B)> { self.destructure() }
}

impl<TM, A> Into<Option<A>> for EfficientOption<A, (), TM>
where A: TaggableValue<TM, One> {
    fn into(self) -> Option<A> { self.destructure().map(|(a, _)| a) }
}

impl<TM, A, B> EfficientOption<A, B, TM>
where A: TaggableValue<TM, One> {
    /// Constructs a new `EfficientOption`
    #[inline]
    pub fn new(a: Option<(A, B)>) -> Self {
        a.map_or_else(Self::none, Self::some)
    }

    /// Constructs a new `EfficientOption`
    #[inline]
    pub fn new_0(a: Option<A>) -> Self
    where B: Default {
        a.map_or_else(Self::none, Self::some_0)
    }

    /// Constructs a new `EfficientOption`
    #[inline]
    pub fn new_1(b: Option<B>) -> Self
    where A: Default {
        b.map_or_else(Self::none, Self::some_1)
    }

    /// Constructs an empty `EfficientOption`
    #[inline]
    pub fn none() -> Self {
        let a = unsafe { utils::uninitialized_from_tag(One::Tagged) };
        let b = unsafe { uninitialized() };
        EfficientOption(a, b)
    }

    /// Constructs an `EfficientOption` from an `A` value
    #[inline]
    pub fn some((a, b): (A, B)) -> Self {
        let a = utils::tag(a, One::Untagged);
        EfficientOption(a, b)
    }

    /// Constructs an `EfficientOption` from an `A` value
    #[inline]
    pub fn some_0(a: A) -> Self
    where B: Default {
        Self::some((a, Default::default()))
    }

    /// Constructs an `EfficientOption` from an `B` value
    #[inline]
    pub fn some_1(b: B) -> Self
    where A: Default {
        Self::some((Default::default(), b))
    }

    /// Clones the `A` value if one exists
    pub fn clone_0(&self) -> Option<A>
    where A: Clone {
        self.ref_0().map(Clone::clone)
    }

    /// Clones the `B` value if one exists
    pub fn clone_1(&self) -> Option<B>
    where B: Clone {
        self.ref_1().map(Clone::clone)
    }

    /// Gets a reference to both the `A` and `B` values if one exists
    pub fn as_ref(&self) -> Option<(&A, &B)> {
        if self.is_none() { None }
        else { Some((&(self.0).1, &self.1)) }
    }

    /// Gets a reference to the `A` value if one exists
    pub fn ref_0(&self) -> Option<&A> {
        if self.is_none() { None }
        else { Some(&(self.0).1) }
    }

    /// Gets a reference to the `B` value if one exists
    pub fn ref_1(&self) -> Option<&B> {
        if self.is_none() { None }
        else { Some(&self.1) }
    }

    /// Gets mutable a reference to the `B` value if one exists
    pub fn mut_1(&mut self) -> Option<&mut B> {
        if self.is_none() { None }
        else { Some(&mut self.1) }
    }

    /// Returns an `EfficientOptionMut` if the option is a `Some` value.
    #[inline]
    pub fn as_mut(&mut self) -> EfficientOptionMut<A, B, TM> {
        use self::EfficientOptionMut::{IsNone, IsSome};
        if self.is_none() {
            IsNone(EfficientOptionNoneMut(self))
        } else {
            IsSome(EfficientOptionSomeMut(self))
        }
    }

    /// Destructures an `EfficientOption`
    #[inline]
    pub fn destructure(self) -> Option<(A, B)> {
        if self.is_none() { None }
        else { Some((utils::untag(self.0), self.1)) }
    }

    /// Destructures an `EfficientOption`
    #[inline]
    pub fn destructure_0(self) -> Option<A> {
        if self.is_none() { None } else { Some(utils::untag(self.0)) }
    }

    /// Destructures an `EfficientOption`
    #[inline]
    pub fn destructure_1(self) -> Option<B> {
        if self.is_none() { None } else { Some(self.1) }
    }

    /// Takes the value out of the option, leaving a None in its place.
    pub fn take(&mut self) -> Option<(A, B)> {
        if self.is_none() { None } else {
            let (a, b) = unsafe {
                let a = read(&self.0 as *const TagWrapper<A, TM>);
                utils::change_tag(&mut self.0, One::Tagged);
                let b = read(&self.1 as *const B);
                (a, b)
            };

            Some((utils::untag(a), b))
        }
    }

    /// Takes both values out of the option, leaving a None in its place.
    /// The version only returns the `A` value
    pub fn take_0(&mut self) -> Option<A> {
        if self.is_none() { None } else {
            let a = unsafe {
                let a = read(&self.0 as *const TagWrapper<A, TM>);
                utils::change_tag(&mut self.0, One::Tagged);
                a
            };

            Some(utils::untag(a))
        }
    }

    /// Takes both values out of the option, leaving a None in its place.
    /// The version only returns the `B` value
    pub fn take_1(&mut self) -> Option<B> {
        if self.is_none() { None } else {
            let b = unsafe {
                utils::change_tag(&mut self.0, One::Tagged);
                read(&self.1 as *const B)
            };

            Some(b)
        }
    }

    /// Returns `true` if the option is a `Some` value.
    #[inline]
    pub fn is_some(&self) -> bool { utils::get_tag(&self.0) == One::Untagged }

    /// Returns `true` if the option is a `None` value.
    #[inline]
    pub fn is_none(&self) -> bool { !self.is_some() }

    /// Maps the value to a result
    #[inline]
    pub fn map<R, F>(&mut self, f: F) -> R
    where F: FnOnce(Option<(&mut A, &mut B)>) -> R {
        let b = &mut self.1;
        utils::borrow_untagged(&mut self.0, |tag, a|
            match tag {
                One::Tagged => f(None),
                One::Untagged => f(Some((a, b))),
            }
        )
    }
}

/// A helper type for `EfficientOption`, useful for adding data to `is_none` options.
pub struct EfficientOptionNoneMut<'a, A: 'a, B: 'a, TM: 'a = TagMSB>(&'a mut EfficientOption<A, B, TM>)
where A: TaggableValue<TM, One>;

/// A helper type for `EfficientOption`, useful for accessing 'is_some' data and removing it.
pub struct EfficientOptionSomeMut<'a, A: 'a, B: 'a, TM: 'a = TagMSB>(&'a mut EfficientOption<A, B, TM>)
where A: TaggableValue<TM, One>;

/// A helper type for `EfficientOption`, gives access to `EfficientOptionNoneMut` and
/// `EfficientOptionSomeMut` variants.
pub enum EfficientOptionMut<'a, A: 'a, B: 'a, TM: 'a = TagMSB>
where A: TaggableValue<TM, One> {
    IsNone(EfficientOptionNoneMut<'a, A, B, TM>),
    IsSome(EfficientOptionSomeMut<'a, A, B, TM>),
}

impl<'a, TM, A, B> EfficientOptionNoneMut<'a, A, B, TM>
where A: TaggableValue<TM, One> {
    /// Adds a value
    pub fn give(self, (a, b): (A, B)) -> EfficientOptionSomeMut<'a, A, B, TM> {
        debug_assert!(self.0.is_none());
        let a = utils::tag(a, One::Untagged);
        unsafe {
            write(&mut (self.0).0 as *mut TagWrapper<A, TM>, a);
            write(&mut (self.0).1 as *mut B, b);
        }
        EfficientOptionSomeMut(self.0)
    }
}

impl<'a, TM, A, B> EfficientOptionSomeMut<'a, A, B, TM>
where A: TaggableValue<TM, One> {
    /// Clones the `A` value
    pub fn clone_0(&self) -> A
    where A: Clone {
        debug_assert!(self.0.is_some());
        utils::untag((self.0).0.clone())
    }

    /// Clones the `B` value
    pub fn clone_1(&self) -> B
    where B: Clone {
        debug_assert!(self.0.is_some());
        self.ref_1().clone()
    }

    /// Gets a reference to the `A` value
    pub fn ref_0(&self) -> &A {
        debug_assert!(self.0.is_some());
        &((self.0).0).1
    }

    /// Gets a reference to the `B` value
    pub fn ref_1(&self) -> &B {
        debug_assert!(self.0.is_some());
        &(self.0).1
    }

    /// Gets mutable a reference to the `B` value
    pub fn mut_1(&mut self) -> &mut B {
        debug_assert!(self.0.is_some());
        &mut (self.0).1
    }

    /// Replaces the `A` value
    pub fn replace_0(&mut self, a: A) -> A {
        let a = utils::tag(a, One::Untagged);
        utils::untag(replace(&mut (self.0).0, a))
    }

    /// Replaces the `B` value
    pub fn replace_1(&mut self, b: B) -> B {
        replace(self.mut_1(), b)
    }

    /// Clones the value
    pub fn clone(&self) -> A
    where A: Clone { utils::untag((self.0).0.clone()) }

    /// Takes both values out of the option, leaving a None in its place.
    pub fn take(self) -> (EfficientOptionNoneMut<'a, A, B, TM>, (A, B)) {
        debug_assert!(self.0.is_some());
        let (a, b) = unsafe {
           let a = read(&(self.0).0 as *const TagWrapper<A, TM>);
           utils::change_tag(&mut (self.0).0, One::Tagged);
           let b = read(&(self.0).1 as *const B);
           (a, b)
        };
        (EfficientOptionNoneMut(self.0), (utils::untag(a), b))
    }

    /// Takes both values out of the option, leaving a None in its place.
    /// The version only returns the `A` value
    pub fn take_0(self) -> (EfficientOptionNoneMut<'a, A, B, TM>, A) {
        debug_assert!(self.0.is_some());
        let a = unsafe {
           let a = read(&(self.0).0 as *const TagWrapper<A, TM>);
           utils::change_tag(&mut (self.0).0, One::Tagged);
           a
        };
        (EfficientOptionNoneMut(self.0), utils::untag(a))
    }

    /// Takes both values out of the option, leaving a None in its place.
    /// The version only returns the `B` value
    pub fn take_1(self) -> (EfficientOptionNoneMut<'a, A, B, TM>, B) {
        debug_assert!(self.0.is_some());
        let b = unsafe {
           utils::change_tag(&mut (self.0).0, One::Tagged);
           read(&(self.0).1 as *const B)
        };
        (EfficientOptionNoneMut(self.0), b)
    }

    /// Maps the value to a result
    pub fn map<R, F: FnOnce(&mut A)-> R>(&mut self, f: F) -> R {
        debug_assert!(self.0.is_some());
        utils::borrow_untagged(&mut (self.0).0, |_, a|
            f(a)
        )
    }
}

impl<'a, TM, A, B> EfficientOptionMut<'a, A, B, TM>
where A: TaggableValue<TM, One> {
    /// Unwraps an option, yielding the content of a `IsSome`.
    ///
    /// # Panics
    ///
    /// Panics if the value is a `IsNone` with a custom panic message provided by
    /// `msg`.
    #[inline]
    pub fn expect_some(self, msg: &str) -> EfficientOptionSomeMut<'a, A, B, TM> {
        use self::EfficientOptionMut::{IsNone,IsSome};
        match self {
            IsNone(_) => utils::expect_failed(msg),
            IsSome(x) => x,
        }
    }

    /// Unwraps an option, yielding the content of a `IsNone`.
    ///
    /// # Panics
    ///
    /// Panics if the value is a `IsSome` with a custom panic message provided by
    /// `msg`.
    #[inline]
    pub fn expect_none(self, msg: &str) -> EfficientOptionNoneMut<'a, A, B, TM> {
        use self::EfficientOptionMut::{IsNone,IsSome};
        match self {
            IsNone(x) => x,
            IsSome(_) => utils::expect_failed(msg),
        }
    }

    /// Moves the value `v` out if it is `IsSome(v)`.
    ///
    /// In general, because this function may panic, its use is discouraged.
    /// Instead, prefer to use pattern matching and handle the `IsNone`
    /// case explicitly.
    ///
    /// # Panics
    ///
    /// Panics if the self value equals `IsNone`.
    #[inline]
    pub fn unwrap_some(self) -> EfficientOptionSomeMut<'a, A, B, TM> {
        use self::EfficientOptionMut::{IsNone,IsSome};
        match self {
            IsNone(_) => panic!("called `EfficientOptionMut::unwrap_some()` on a `IsNone` value"),
            IsSome(x) => x,
        }
    }

    /// Moves the value `v` out if it is `IsNone(v)`.
    ///
    /// In general, because this function may panic, its use is discouraged.
    /// Instead, prefer to use pattern matching and handle the `IsSome`
    /// case explicitly.
    ///
    /// # Panics
    ///
    /// Panics if the self value equals `IsSome`.
    #[inline]
    pub fn unwrap_none(self) -> EfficientOptionNoneMut<'a, A, B, TM> {
        use self::EfficientOptionMut::{IsNone,IsSome};
        match self {
            IsNone(x) => x,
            IsSome(_) => panic!("called `EfficientOptionMut::unwrap_none()` on a `IsSome` value"),
        }
    }

    /// Returns the contained `IsSome` value or a default.
    #[inline]
    pub fn unwrap_some_or(self, default: EfficientOptionSomeMut<'a, A, B, TM>) -> EfficientOptionSomeMut<'a, A, B, TM> {
        self.map(|_| default, |x| x)
    }

    /// Returns the contained `IsNone` value or a default.
    #[inline]
    pub fn unwrap_none_or(self, default: EfficientOptionNoneMut<'a, A, B, TM>) -> EfficientOptionNoneMut<'a, A, B, TM> {
        self.map(|x| x, |_| default)
    }

    /// Returns the contained `IsSome` value or computes it from a closure.
    #[inline]
    pub fn unwrap_some_or_else<F>(self, f: F) -> EfficientOptionSomeMut<'a, A, B, TM>
    where F: FnOnce(EfficientOptionNoneMut<'a, A, B, TM>) -> EfficientOptionSomeMut<'a, A, B, TM> {
        self.map(f, |x| x)
    }

    /// Returns the contained `IsNone` value or computes it from a closure.
    #[inline]
    pub fn unwrap_none_or_else<F>(self, f: F) -> EfficientOptionNoneMut<'a, A, B, TM>
    where F: FnOnce(EfficientOptionSomeMut<'a, A, B, TM>) -> EfficientOptionNoneMut<'a, A, B, TM> {
        self.map(|x| x, f)
    }

    /// Applies a function to the contained `IsSome` value or returns a `default`.
    #[inline]
    pub fn map_some_or<U, F>(self, default: U, f: F) -> U
    where F: FnOnce(EfficientOptionSomeMut<'a, A, B, TM>) -> U {
        self.map(|_| default, f)
    }

    /// Applies a function to the contained `IsNone` value or returns a `default`.
    #[inline]
    pub fn map_none_or<U, F>(self, default: U, f: F) -> U
    where F: FnOnce(EfficientOptionNoneMut<'a, A, B, TM>) -> U {
        self.map(f, |_| default)
    }


    /// Applies a function to the contained `IsSome` value or computes a `default` from the `IsNone`.
    #[inline]
    pub fn map<U, D, F>(self, default: D, f: F) -> U
    where D: FnOnce(EfficientOptionNoneMut<'a, A, B, TM>) -> U,
    F: FnOnce(EfficientOptionSomeMut<'a, A, B, TM>) -> U {
        use self::EfficientOptionMut::{IsNone,IsSome};
        match self {
            IsNone(x) => default(x),
            IsSome(x) => f(x),
        }
    }
}

/// An option type similar to `(A, Option<B>)`, but where no extra data is used. Instead, some of
/// the space in `A` is used to "tag the union".
///
/// The one true downside is that it is impossible to get `&A` from `&EfficientOptionTuple`. The reason
/// for this is that doing so would expose the private tag info.
pub struct EfficientOptionTuple<A, B, TM=TagMSB>(TagWrapper<A, TM>, B)
where A: TaggableValue<TM, Two>;

impl<TM, A: Clone, B: Clone> Clone for EfficientOptionTuple<A, B, TM>
where A: TaggableValue<TM, Two> {
    fn clone(&self) -> Self {
        let b = self.ref_1().map_or(unsafe { uninitialized() }, Clone::clone);
        EfficientOptionTuple(self.0.clone(), b)
    }

    fn clone_from(&mut self, source: &Self) {
        if let Some(b) = source.ref_1() {
            if self.is_some() {
                self.1.clone_from(b);
            } else {
                let b = b.clone();
                unsafe { write(&mut self.1 as *mut B, b) }
            }
        }
        self.0.clone_from(&source.0);
    }
}
impl<TM, A: Copy, B: Copy> Copy for EfficientOptionTuple<A, B, TM>
where A: TaggableValue<TM, Two> {}

impl<TM, A: Default, B> Default for EfficientOptionTuple<A, B, TM>
where A: TaggableValue<TM, Two> {
    fn default() -> Self {
        EfficientOptionTuple::none(Default::default())
    }
}

impl<TM, A: fmt::Debug, B: fmt::Debug> fmt::Debug for EfficientOptionTuple<A, B, TM>
where A: TaggableValue<TM, Two> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "EfficientOptionTuple(")?;
        TaggableValue::fmt_untagged(&self.0, f)?;
        if let Some(b) = self.ref_1() {
            write!(f, ", Some({:?}))", b)
        } else {
            write!(f, ", None)")
        }
    }
}

impl<TM, A: PartialEq, B: PartialEq> PartialEq for EfficientOptionTuple<A, B, TM>
where A: TaggableValue<TM, Two> {
    fn eq(&self, other: &Self) -> bool {
        TaggableValue::eq(&self.0, &other.0) && match (self.ref_1(), other.ref_1()) {
            (Some(s), Some(o)) => *s == *o,
            (None, None) => true,
            _ => false,
        }
    }

    fn ne(&self, other: &Self) -> bool {
        TaggableValue::ne(&self.0, &other.0) || match (self.ref_1(), other.ref_1()) {
            (Some(s), Some(o)) => *s != *o,
            (None, None) => false,
            _ => true,
        }
    }
}
impl<TM, A: Eq, B: Eq> Eq for EfficientOptionTuple<A, B, TM>
where A: TaggableValue<TM, Two> {}

impl<TM, A: Hash, B: Hash> Hash for EfficientOptionTuple<A, B, TM>
where A: TaggableValue<TM, Two> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.hash(state);
        if let Some(b) = self.ref_1() { b.hash(state) }
    }
}

impl<TM, A, B> From<(A, Option<B>)> for EfficientOptionTuple<A, B, TM>
where A: TaggableValue<TM, Two> {
    fn from((a, b): (A, Option<B>)) -> Self {
        Self::new(a, b)
    }
}

impl<TM, A, B> Into<(A, Option<B>)> for EfficientOptionTuple<A, B, TM>
where A: TaggableValue<TM, Two> {
    fn into(self) -> (A, Option<B>) { self.destructure() }
}

impl<TM, A, B> EfficientOptionTuple<A, B, TM>
where A: TaggableValue<TM, Two> {
    /// Constructs a new `EfficientOptionTuple`
    #[inline]
    pub fn new(a: A, b: Option<B>) -> Self {
        if let Some(b) = b { Self::some(a, b) } else { Self::none(a) }
    }

    /// Constructs an `EfficientOptionTuple` with no `B` value
    #[inline]
    pub fn none(a: A) -> Self {
        let a = utils::tag(a, Two::Option0);
        let b = unsafe { uninitialized() };
        EfficientOptionTuple(a, b)
    }

    /// Constructs an `EfficientOptionTuple` with a `B` value
    #[inline]
    pub fn some(a: A, b: B) -> Self {
        let a = utils::tag(a, Two::Option1);
        EfficientOptionTuple(a, b)
    }

    /// Destructures an `EfficientOptionTuple`
    #[inline]
    pub fn destructure(self) -> (A, Option<B>) {
        let b = if self.is_none() { None } else { Some(self.1) };
        (utils::untag(self.0), b)
    }

    /// Takes the `B` value out of the option, leaving a None in its place.
    pub fn take_1(&mut self) -> Option<B> {
        if self.is_none() { None }
        else {
            let b = unsafe {
                utils::change_tag(&mut self.0, Two::Option0);
                read(&self.1 as *const B)
            };

            Some(b)
        }
    }

    /// Returns `true` if the option is a `Some` value.
    #[inline]
    pub fn is_some(&self) -> bool { utils::get_tag(&self.0) == Two::Option1 }

    /// Returns `true` if the option is a `None` value.
    #[inline]
    pub fn is_none(&self) -> bool { !self.is_some() }

    /// Returns an `EfficientOptionTupleSomeMut` if the option is a `Some` value, returns an
    /// `EfficientOptionTupleNoneMut` otherwise.
    #[inline]
    pub fn as_mut(&mut self) -> EfficientOptionTupleMut<A, B, TM> {
        use self::EfficientOptionTupleMut::{IsNone,IsSome};
        if self.is_none() {
            IsNone(EfficientOptionTupleNoneMut(self))
        } else {
            IsSome(EfficientOptionTupleSomeMut(self))
        }
    }

    /// Clones the `A` value
    pub fn clone_0(&self) -> A
    where A: Clone { utils::untag(self.0.clone()) }

    /// Clones the `B` value if one exists
    pub fn clone_1(&self) -> Option<B>
    where B: Clone {
        self.ref_1().map(Clone::clone)
    }

    /// Gets a reference to the `B` value if one exists
    pub fn ref_1(&self) -> Option<&B> {
        if self.is_none() { None }
        else { Some(&self.1) }
    }

    /// Gets mutable a reference to the `B` value if one exists
    pub fn mut_1(&mut self) -> Option<&mut B> {
        if self.is_none() { None }
        else { Some(&mut self.1) }
    }

    /// Replaces the `A` value
    pub fn replace_0(&mut self, a: A) -> A {
        let a = utils::tag(a, utils::get_tag(&self.0));
        utils::untag(replace(&mut self.0, a))
    }

    /// Replaces the `B` value
    pub fn replace_1(&mut self, b: Option<B>) -> Option<B> {
        match (utils::get_tag(&self.0), b) {
            (Two::Option0, None) => None,
            (Two::Option0, Some(b)) => { unsafe {
                write(&mut self.1 as *mut B, b);
                utils::change_tag(&mut self.0, Two::Option1);
                None
            }},
            (Two::Option1, None) => { unsafe {
                utils::change_tag(&mut self.0, Two::Option0);
                Some(read(&self.1 as *const B))
            }},
            (Two::Option1, Some(b)) => Some(replace(&mut self.1, b)),
        }
    }

    /// Maps the `A` and `B` values to a result
    pub fn map<R, F: FnOnce(&mut A, Option<&mut B>)-> R>(&mut self, f: F) -> R {
        let b = &mut self.1;
        utils::borrow_untagged(&mut self.0, |tag, a|
            match tag {
                Two::Option0 => f(a, None),
                Two::Option1 => f(a, Some(b)),
            }
        )
    }
}

/// A helper type useful for accessing the lack of data or replacing it with nothing without having to
/// use unwraps.
pub struct EfficientOptionTupleNoneMut<'a, A: 'a, B: 'a, TM: 'a = TagMSB>(&'a mut EfficientOptionTuple<A, B, TM>)
where A: TaggableValue<TM, Two>;

/// A helper type useful for accessing the optional data or removing it without having to
/// use unwraps.
pub struct EfficientOptionTupleSomeMut<'a, A: 'a, B: 'a, TM: 'a = TagMSB>(&'a mut EfficientOptionTuple<A, B, TM>)
where A: TaggableValue<TM, Two>;

/// A helper type useful for accessing the lack of data or replacing it with nothing without having to
/// use unwraps.
pub enum EfficientOptionTupleMut<'a, A: 'a, B: 'a, TM: 'a = TagMSB>
where A: TaggableValue<TM, Two> {
    IsNone(EfficientOptionTupleNoneMut<'a, A, B, TM>),
    IsSome(EfficientOptionTupleSomeMut<'a, A, B, TM>),
}

impl<'a, TM, A, B> EfficientOptionTupleNoneMut<'a, A, B, TM>
where A: TaggableValue<TM, Two> {
    /// Clones the `A` value
    pub fn clone_0(&self) -> A
    where A: Clone { self.0.clone_0() }

    /// Adds a `B` value
    pub fn add_1(self, b: B) -> EfficientOptionTupleSomeMut<'a, A, B, TM> {
        debug_assert!(self.0.is_none());
        unsafe {
            write(&mut (self.0).1 as *mut B, b);
            utils::change_tag(&mut (self.0).0, Two::Option1);
        }
        EfficientOptionTupleSomeMut(self.0)
    }
    /// Maps the `A` value to a result
    pub fn map<R, F: FnOnce(&mut A)-> R>(&mut self, f: F) -> R {
        debug_assert!(self.0.is_none());
        utils::borrow_untagged(&mut (self.0).0, |_, a|
            f(a)
        )
    }
}

impl<'a, TM, A, B> EfficientOptionTupleSomeMut<'a, A, B, TM>
where A: TaggableValue<TM, Two> {
    /// Clones the `A` value
    pub fn clone_0(&self) -> A
    where A: Clone { self.0.clone_0() }

    /// Clones the `B` value
    pub fn clone_1(&self) -> B
    where B: Clone {
        debug_assert!(self.0.is_some());
        self.ref_1().clone()
    }

    /// Gets a reference to the `B` value
    pub fn ref_1(&self) -> &B {
        debug_assert!(self.0.is_some());
        &(self.0).1
    }

    /// Gets mutable a reference to the `B` value
    pub fn mut_1(&mut self) -> &mut B {
        debug_assert!(self.0.is_some());
        &mut (self.0).1
    }

    /// Replaces the `A` value
    pub fn replace_0(&mut self, a: A) -> A {
        debug_assert!(self.0.is_some());
        self.0.replace_0(a)
    }

    /// Removes the `B` value
    pub fn remove_1(self) -> (EfficientOptionTupleNoneMut<'a, A, B, TM>, B) {
        debug_assert!(self.0.is_some());
        let b = unsafe {
           utils::change_tag(&mut (self.0).0, Two::Option0);
           read(&(self.0).1 as *const B)
        };
        (EfficientOptionTupleNoneMut(self.0), b)
    }

    /// Maps the `A` and `B` values to a result
    pub fn map<R, F: FnOnce(&mut A, &mut B)-> R>(&mut self, f: F) -> R {
        debug_assert!(self.0.is_some());
        let b = &mut (self.0).1;
        utils::borrow_untagged(&mut (self.0).0, |_, a|
            f(a, b)
        )
    }
}

impl<'a, TM, A, B> EfficientOptionTupleMut<'a, A, B, TM>
where A: TaggableValue<TM, Two> {
    /// Unwraps an option, yielding the content of a `IsSome`.
    ///
    /// # Panics
    ///
    /// Panics if the value is a `IsNone` with a custom panic message provided by
    /// `msg`.
    #[inline]
    pub fn expect_some(self, msg: &str) -> EfficientOptionTupleSomeMut<'a, A, B, TM> {
        use self::EfficientOptionTupleMut::{IsNone,IsSome};
        match self {
            IsNone(_) => utils::expect_failed(msg),
            IsSome(x) => x,
        }
    }

    /// Unwraps an option, yielding the content of a `IsNone`.
    ///
    /// # Panics
    ///
    /// Panics if the value is a `IsSome` with a custom panic message provided by
    /// `msg`.
    #[inline]
    pub fn expect_none(self, msg: &str) -> EfficientOptionTupleNoneMut<'a, A, B, TM> {
        use self::EfficientOptionTupleMut::{IsNone,IsSome};
        match self {
            IsNone(x) => x,
            IsSome(_) => utils::expect_failed(msg),
        }
    }

    /// Moves the value `v` out if it is `IsSome(v)`.
    ///
    /// In general, because this function may panic, its use is discouraged.
    /// Instead, prefer to use pattern matching and handle the `IsNone`
    /// case explicitly.
    ///
    /// # Panics
    ///
    /// Panics if the self value equals `IsNone`.
    #[inline]
    pub fn unwrap_some(self) -> EfficientOptionTupleSomeMut<'a, A, B, TM> {
        use self::EfficientOptionTupleMut::{IsNone,IsSome};
        match self {
            IsNone(_) => panic!("called `EfficientOptionTupleMut::unwrap_some()` on a `IsNone` value"),
            IsSome(x) => x,
        }
    }

    /// Moves the value `v` out if it is `IsNone(v)`.
    ///
    /// In general, because this function may panic, its use is discouraged.
    /// Instead, prefer to use pattern matching and handle the `IsSome`
    /// case explicitly.
    ///
    /// # Panics
    ///
    /// Panics if the self value equals `IsSome`.
    #[inline]
    pub fn unwrap_none(self) -> EfficientOptionTupleNoneMut<'a, A, B, TM> {
        use self::EfficientOptionTupleMut::{IsNone,IsSome};
        match self {
            IsNone(x) => x,
            IsSome(_) => panic!("called `EfficientOptionTupleMut::unwrap_none()` on a `IsSome` value"),
        }
    }

    /// Returns the contained `IsSome` value or a default.
    #[inline]
    pub fn unwrap_some_or(self, default: EfficientOptionTupleSomeMut<'a, A, B, TM>) -> EfficientOptionTupleSomeMut<'a, A, B, TM> {
        self.map(|_| default, |x| x)
    }

    /// Returns the contained `IsNone` value or a default.
    #[inline]
    pub fn unwrap_none_or(self, default: EfficientOptionTupleNoneMut<'a, A, B, TM>) -> EfficientOptionTupleNoneMut<'a, A, B, TM> {
        self.map(|x| x, |_| default)
    }

    /// Returns the contained `IsSome` value or computes it from a closure.
    #[inline]
    pub fn unwrap_some_or_else<F>(self, f: F) -> EfficientOptionTupleSomeMut<'a, A, B, TM>
    where F: FnOnce(EfficientOptionTupleNoneMut<'a, A, B, TM>) -> EfficientOptionTupleSomeMut<'a, A, B, TM> {
        self.map(f, |x| x)
    }

    /// Returns the contained `IsNone` value or computes it from a closure.
    #[inline]
    pub fn unwrap_none_or_else<F>(self, f: F) -> EfficientOptionTupleNoneMut<'a, A, B, TM>
    where F: FnOnce(EfficientOptionTupleSomeMut<'a, A, B, TM>) -> EfficientOptionTupleNoneMut<'a, A, B, TM> {
        self.map(|x| x, f)
    }

    /// Applies a function to the contained `IsSome` value or returns a `default`.
    #[inline]
    pub fn map_some_or<U, F>(self, default: U, f: F) -> U
    where F: FnOnce(EfficientOptionTupleSomeMut<'a, A, B, TM>) -> U {
        self.map(|_| default, f)
    }

    /// Applies a function to the contained `IsNone` value or returns a `default`.
    #[inline]
    pub fn map_none_or<U, F>(self, default: U, f: F) -> U
    where F: FnOnce(EfficientOptionTupleNoneMut<'a, A, B, TM>) -> U {
        self.map(f, |_| default)
    }


    /// Applies a function to the contained `IsSome` value or computes a `default` from the `IsNone`.
    #[inline]
    pub fn map<U, D, F>(self, default: D, f: F) -> U
    where D: FnOnce(EfficientOptionTupleNoneMut<'a, A, B, TM>) -> U,
    F: FnOnce(EfficientOptionTupleSomeMut<'a, A, B, TM>) -> U {
        use self::EfficientOptionTupleMut::{IsNone,IsSome};
        match self {
            IsNone(x) => default(x),
            IsSome(x) => f(x),
        }
    }
}

/// A helper type for `Option`, useful for adding data to `is_none` options.
pub struct OptionNoneMut<'a, A: 'a>(&'a mut Option<A>);

/// A helper type for `Option`, useful for accessing 'is_some' data and removing it.
pub struct OptionSomeMut<'a, A: 'a>(&'a mut Option<A>);

/// A helper type for `Option`, gives access to `OptionNoneMut` and
/// `OptionSomeMut` variants.
pub enum OptionMut<'a, A: 'a> {
    IsNone(OptionNoneMut<'a, A>),
    IsSome(OptionSomeMut<'a, A>),
}

impl<'a, A> OptionMut<'a, A> {
    pub fn new(a: &'a mut Option<A>) -> Self {
        use self::OptionMut::{IsNone,IsSome};
        if a.is_none() { IsNone(OptionNoneMut(a))}
        else { IsSome(OptionSomeMut(a))}
    }
}

impl<'a, A> OptionNoneMut<'a, A> {
    /// Adds a value
    pub fn add(self, a: A) -> OptionSomeMut<'a, A> {
        debug_assert!(self.0.is_none());
        *self.0 = Some(a);
        OptionSomeMut(self.0)
    }
}

impl<'a, A> OptionSomeMut<'a, A> {
    /// Gets a reference to the value
    pub fn as_ref(&self) -> &A {
        debug_assert!(self.0.is_some());
        self.0.as_ref().unwrap()
    }

    /// Gets mutable a reference to the value
    pub fn as_mut(&mut self) -> &mut A {
        debug_assert!(self.0.is_some());
        self.0.as_mut().unwrap()
    }

    /// Removes the value
    pub fn remove(self) -> (OptionNoneMut<'a, A>, A) {
        debug_assert!(self.0.is_some());
        let a = replace(self.0, None).unwrap();
        (OptionNoneMut(self.0), a)
    }
}

impl<'a, A> OptionMut<'a, A> {
    /// Unwraps an option, yielding the content of a `IsSome`.
    ///
    /// # Panics
    ///
    /// Panics if the value is a `IsNone` with a custom panic message provided by
    /// `msg`.
    #[inline]
    pub fn expect_some(self, msg: &str) -> OptionSomeMut<'a, A> {
        use self::OptionMut::{IsNone,IsSome};
        match self {
            IsNone(_) => utils::expect_failed(msg),
            IsSome(x) => x,
        }
    }

    /// Unwraps an option, yielding the content of a `IsNone`.
    ///
    /// # Panics
    ///
    /// Panics if the value is a `IsSome` with a custom panic message provided by
    /// `msg`.
    #[inline]
    pub fn expect_none(self, msg: &str) -> OptionNoneMut<'a, A> {
        use self::OptionMut::{IsNone,IsSome};
        match self {
            IsNone(x) => x,
            IsSome(_) => utils::expect_failed(msg),
        }
    }

    /// Moves the value `v` out if it is `IsSome(v)`.
    ///
    /// In general, because this function may panic, its use is discouraged.
    /// Instead, prefer to use pattern matching and handle the `IsNone`
    /// case explicitly.
    ///
    /// # Panics
    ///
    /// Panics if the self value equals `IsNone`.
    #[inline]
    pub fn unwrap_some(self) -> OptionSomeMut<'a, A> {
        use self::OptionMut::{IsNone,IsSome};
        match self {
            IsNone(_) => panic!("called `OptionMut::unwrap_some()` on a `IsNone` value"),
            IsSome(x) => x,
        }
    }

    /// Moves the value `v` out if it is `IsNone(v)`.
    ///
    /// In general, because this function may panic, its use is discouraged.
    /// Instead, prefer to use pattern matching and handle the `IsSome`
    /// case explicitly.
    ///
    /// # Panics
    ///
    /// Panics if the self value equals `IsSome`.
    #[inline]
    pub fn unwrap_none(self) -> OptionNoneMut<'a, A> {
        use self::OptionMut::{IsNone,IsSome};
        match self {
            IsNone(x) => x,
            IsSome(_) => panic!("called `OptionMut::unwrap_none()` on a `IsSome` value"),
        }
    }

    /// Returns the contained `IsSome` value or a default.
    #[inline]
    pub fn unwrap_some_or(self, default: OptionSomeMut<'a, A>) -> OptionSomeMut<'a, A> {
        self.map(|_| default, |x| x)
    }

    /// Returns the contained `IsNone` value or a default.
    #[inline]
    pub fn unwrap_none_or(self, default: OptionNoneMut<'a, A>) -> OptionNoneMut<'a, A> {
        self.map(|x| x, |_| default)
    }

    /// Returns the contained `IsSome` value or computes it from a closure.
    #[inline]
    pub fn unwrap_some_or_else<F>(self, f: F) -> OptionSomeMut<'a, A>
    where F: FnOnce(OptionNoneMut<'a, A>) -> OptionSomeMut<'a, A> {
        self.map(f, |x| x)
    }

    /// Returns the contained `IsNone` value or computes it from a closure.
    #[inline]
    pub fn unwrap_none_or_else<F>(self, f: F) -> OptionNoneMut<'a, A>
    where F: FnOnce(OptionSomeMut<'a, A>) -> OptionNoneMut<'a, A> {
        self.map(|x| x, f)
    }

    /// Applies a function to the contained `IsSome` value or returns a `default`.
    #[inline]
    pub fn map_some_or<U, F>(self, default: U, f: F) -> U
    where F: FnOnce(OptionSomeMut<'a, A>) -> U {
        self.map(|_| default, f)
    }

    /// Applies a function to the contained `IsNone` value or returns a `default`.
    #[inline]
    pub fn map_none_or<U, F>(self, default: U, f: F) -> U
    where F: FnOnce(OptionNoneMut<'a, A>) -> U {
        self.map(f, |_| default)
    }


    /// Applies a function to the contained `IsSome` value or computes a `default` from the `IsNone`.
    #[inline]
    pub fn map<U, D, F>(self, default: D, f: F) -> U
    where D: FnOnce(OptionNoneMut<'a, A>) -> U,
    F: FnOnce(OptionSomeMut<'a, A>) -> U {
        use self::OptionMut::{IsNone,IsSome};
        match self {
            IsNone(x) => default(x),
            IsSome(x) => f(x),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_option_new() {
        let a = EfficientOption::<usize>::some_0(10);
        let b = EfficientOption::<usize>::new_0(Some(10));
        assert_eq!(a.destructure_0(), Some(10));
        assert_eq!(b.destructure_0(), Some(10));
        assert_eq!(a, b);

        let a = EfficientOption::<usize>::none();
        let b = EfficientOption::<usize>::new(None);
        assert_eq!(a.destructure(), None);
        assert_eq!(b.destructure(), None);
        assert_eq!(a, b);
    }

    #[test]
    fn test_option_simple() {
        let v = EfficientOption::<usize>::some_0(10);
        assert!(!v.is_none());
        assert!(v.is_some());

        let v = EfficientOption::<usize>::none();
        assert!(v.is_none());
        assert!(!v.is_some());
    }

    #[test]
    fn test_option_mut() {
        let mut v = EfficientOption::<usize>::some_0(10);
        assert_eq!(v.destructure_0(), Some(10));

        v.map(|a| *a.unwrap().0 = 11 );
        assert_eq!(v.destructure_0(), Some(11));

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
        assert_eq!(v.clone_0(), 10);
        assert_eq!(v.clone_1(), Some(15));
        assert_eq!(*v.ref_1().unwrap(), 15);
        assert_eq!(v.destructure(), (10, Some(15)));

        let v = EfficientOptionTuple::<usize, usize>::none(10);
        assert!(v.is_none());
        assert!(!v.is_some());
        assert_eq!(v.clone_0(), 10);
        assert_eq!(v.clone_1(), None);
        assert_eq!(v.ref_1(), None);
        assert_eq!(v.destructure(), (10, None));
    }

    #[test]
    fn test_option_tuple_mut() {
        let mut v = EfficientOptionTuple::<usize, usize>::some(10, 15);
        assert_eq!(v.destructure(), (10, Some(15)));

        *v.mut_1().unwrap() = 16;
        assert_eq!(v.destructure(), (10, Some(16)));

        v.replace_0(11);
        assert_eq!(v.destructure(), (11, Some(16)));

        v.replace_1(Some(17));
        assert_eq!(v.destructure(), (11, Some(17)));

        v.replace_1(None);
        assert_eq!(v.destructure(), (11, None));
        assert_eq!(v.mut_1(), None);

        v.map(|a, b| {
            *a = 12;
            assert_eq!(b, None);
        });
        assert_eq!(v.destructure(), (12, None));

        v.replace_0(13);
        assert_eq!(v.destructure(), (13, None));

        v.replace_1(Some(18));
        assert_eq!(v.destructure(), (13, Some(18)));

        v.map(|a, b| {
            *a = 14;
            *b.unwrap() = 19;
        });
        assert_eq!(v.destructure(), (14, Some(19)));
    }

    #[test]
    fn test_option_tuple_as_mut() {
        let mut v = EfficientOptionTuple::<usize, usize>::some(10, 15);
        {
            let r = v.as_mut();
            assert_eq!(r.unwrap_some().clone_0(), 10);
        }
        {
            let r = v.as_mut();
            assert_eq!(r.unwrap_some().clone_1(), 15);
        }
        {
            let r = v.as_mut();
            assert_eq!(*r.unwrap_some().ref_1(), 15);
        }


        let mut v = EfficientOptionTuple::<usize, usize>::none(10);
        {
            let r = v.as_mut();
            assert_eq!(r.unwrap_none().clone_0(), 10);
        }
    }
}
