//! Space-efficient enum values.
//!
//! For the moment only option types are implemented, as true enums would require something
//! like a `const fn` version of `size_of`.

mod utils;

pub mod tag;
pub mod option;
