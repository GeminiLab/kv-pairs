//! Key-value pair builder for API params and form data.
//!
//! This crate provides [`KVPairs`], an ordered collection of key-value pairs,
//! whose values can be either borrowed or owned, that can be used as HTTP query
//! strings or form bodies. The [`kv_pairs!`] macro can be used to build
//! `KVPairs` instances with a literal-like syntax.
//!
//! [`KVPairs`] accepts values that implement [`IntoValue`], this includes most
//! primitive and standard library types like `&str`, `String`, `bool`, and
//! common integer types. The `impl_into_value_by_*` macros can be used to
//! implement [`IntoValue`] for more types.
//!
//! [`KVPairs`] also accepts values that implement [`IntoValues`], to insert 0,
//! 1, or more values for a single key. This is useful for optional or
//! multi-value parameters. The keys are **NEVER** automatically suffixed with
//! `[]` when inserting values via [`IntoValues`].
//!
//! # Example
//!
//! ```rust
//! use kv_pairs::{kv_pairs, KVPairs};
//!
//! let params = kv_pairs![
//!     "mode" => "day",
//!     "page" => 1_u32,
//! ];
//! assert_eq!(params.content.len(), 2);
//! ```

#![cfg_attr(not(feature = "std"), no_std)]

extern crate alloc;

use alloc::borrow::{Borrow, Cow};
use alloc::string::{String, ToString};
use alloc::vec::Vec;
use core::iter::{once, Map, Once};
use core::ops::{Deref, DerefMut, Index, IndexMut};
use core::option::IntoIter as OptionIntoIter;
use core::slice::{Iter as SliceIter, IterMut as SliceIterMut};
use serde::{Deserialize, Serialize};

/// A list of key-value pairs for API query or form parameters.
///
/// Internally a `Vec<(&str, Cow<str>)>`, supporting borrowed keys/values (zero allocation) and
/// owned values when needed. Implements [`Serialize`]/[`Deserialize`] for use with serde (e.g.
/// with `reqwest`’s `.query(&p.content)` or `.form(&p.content)`).
#[derive(Clone, Debug, Eq, Hash, PartialEq, Serialize, Deserialize)]
#[serde(bound(deserialize = "'de: 'a"))]
#[serde(transparent)]
pub struct KVPairs<'a> {
    /// The key-value entries; can be passed directly to `reqwest`’s `.query()` or `.form()`.
    pub content: Vec<KVPair<'a>>,
}

/// Type alias for the inner pair type, for use in trait bounds.
pub type KVPair<'a> = (&'a str, Cow<'a, str>);

#[doc(hidden)]
pub mod __private {
    pub use alloc::borrow::Cow;
}

impl Default for KVPairs<'_> {
    fn default() -> Self {
        Self::new()
    }
}

impl<'a> KVPairs<'a> {
    /// Creates an empty key-value list.
    #[must_use]
    pub fn new() -> Self {
        Self {
            content: Vec::new(),
        }
    }

    /// Appends a single key-value pair; `value` is converted via [`IntoValue`] to `Cow<str>` (borrowed or owned).
    pub fn push_one<'b: 'a, V: IntoValue<'b>>(&mut self, key: &'a str, value: V) {
        self.content.push((key, value.into_value()));
    }

    /// Appends key-value pair(s) for each value yielded by `value` via [`IntoValues`]; for optional or multi-value parameters.
    pub fn push<'b: 'a, V: IntoValues<'b>>(&mut self, key: &'a str, value: V) {
        for v in value.into_values() {
            self.content.push((key, v));
        }
    }

    /// Appends a key-value pair with a value that implements `AsRef<str>`, using a borrow to avoid allocation.
    pub fn push_str<'b: 'a, V: AsRef<str> + ?Sized>(&mut self, key: &'a str, value: &'b V) {
        self.content.push((key, Cow::Borrowed(value.as_ref())));
    }

    /// Appends a key-value pair with an owned value (allocates and stores the string).
    pub fn push_owned<V: Into<String>>(&mut self, key: &'a str, value: V) {
        self.content.push((key, Cow::Owned(value.into())));
    }
}

impl<'a> AsRef<[KVPair<'a>]> for KVPairs<'a> {
    fn as_ref(&self) -> &[KVPair<'a>] {
        self.content.as_ref()
    }
}

impl<'a> AsRef<Vec<KVPair<'a>>> for KVPairs<'a> {
    fn as_ref(&self) -> &Vec<KVPair<'a>> {
        &self.content
    }
}

impl<'a> AsMut<[KVPair<'a>]> for KVPairs<'a> {
    fn as_mut(&mut self) -> &mut [KVPair<'a>] {
        self.content.as_mut()
    }
}

impl<'a> AsMut<Vec<KVPair<'a>>> for KVPairs<'a> {
    fn as_mut(&mut self) -> &mut Vec<KVPair<'a>> {
        &mut self.content
    }
}

impl<'a> Borrow<[KVPair<'a>]> for KVPairs<'a> {
    fn borrow(&self) -> &[KVPair<'a>] {
        self.content.as_ref()
    }
}

impl<'a> Borrow<Vec<KVPair<'a>>> for KVPairs<'a> {
    fn borrow(&self) -> &Vec<KVPair<'a>> {
        &self.content
    }
}

impl<'a> Deref for KVPairs<'a> {
    type Target = Vec<KVPair<'a>>;

    fn deref(&self) -> &Self::Target {
        &self.content
    }
}

impl DerefMut for KVPairs<'_> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.content
    }
}

impl<'a, I> Index<I> for KVPairs<'a>
where
    Vec<KVPair<'a>>: Index<I>,
{
    type Output = <Vec<KVPair<'a>> as Index<I>>::Output;

    fn index(&self, index: I) -> &Self::Output {
        &self.content[index]
    }
}

impl<'a, I> IndexMut<I> for KVPairs<'a>
where
    Vec<KVPair<'a>>: IndexMut<I>,
{
    fn index_mut(&mut self, index: I) -> &mut Self::Output {
        &mut self.content[index]
    }
}

impl<'a> FromIterator<KVPair<'a>> for KVPairs<'a> {
    fn from_iter<T: IntoIterator<Item = KVPair<'a>>>(iter: T) -> Self {
        Self {
            content: iter.into_iter().collect(),
        }
    }
}

impl<'a> IntoIterator for KVPairs<'a> {
    type Item = KVPair<'a>;
    type IntoIter = <Vec<KVPair<'a>> as IntoIterator>::IntoIter;

    fn into_iter(self) -> Self::IntoIter {
        self.content.into_iter()
    }
}

impl<'a, 'b> IntoIterator for &'b KVPairs<'a> {
    type Item = &'b KVPair<'a>;
    type IntoIter = SliceIter<'b, KVPair<'a>>;

    fn into_iter(self) -> Self::IntoIter {
        self.content.iter()
    }
}

impl<'a, 'b> IntoIterator for &'b mut KVPairs<'a> {
    type Item = &'b mut KVPair<'a>;
    type IntoIter = SliceIterMut<'b, KVPair<'a>>;

    fn into_iter(self) -> Self::IntoIter {
        self.content.iter_mut()
    }
}

/// Converts a value into `Cow<'a, str>` for use with [`KVPairs::push_one`].
///
/// Implemented for `&str`, `String`, `bool`, and common integer types; use the macros to implement for more types.
pub trait IntoValue<'a> {
    /// Converts into a borrowed or owned string.
    fn into_value(self) -> Cow<'a, str>;
}

/// Yields an iterator of `Cow<'a, str>` for use with [`KVPairs::push`].
///
/// For `Option<T>`, yields zero or one item (pair added only when `Some`); for `T: IntoValue`, yields one item.
pub trait IntoValues<'a> {
    /// Iterator over the string value(s).
    type Iter: Iterator<Item = Cow<'a, str>>;

    /// Returns an iterator of borrowed or owned strings.
    fn into_values(self) -> Self::Iter;
}

impl<'a> IntoValue<'a> for &'a str {
    fn into_value(self) -> Cow<'a, str> {
        Cow::Borrowed(self)
    }
}

impl<'a> IntoValue<'a> for String {
    fn into_value(self) -> Cow<'a, str> {
        Cow::Owned(self)
    }
}

impl<'a> IntoValue<'a> for &'a String {
    fn into_value(self) -> Cow<'a, str> {
        Cow::Borrowed(self.as_str())
    }
}

impl<'a> IntoValue<'a> for bool {
    fn into_value(self) -> Cow<'a, str> {
        Cow::Borrowed(if self { "true" } else { "false" })
    }
}

impl<'a, T: IntoValue<'a>> IntoValues<'a> for T {
    type Iter = Once<Cow<'a, str>>;

    fn into_values(self) -> Self::Iter {
        once(self.into_value())
    }
}

impl<'a, T: IntoValue<'a>> IntoValues<'a> for Option<T> {
    type Iter = Map<OptionIntoIter<T>, fn(T) -> Cow<'a, str>>;

    fn into_values(self) -> Self::Iter {
        self.into_iter().map(IntoValue::into_value)
    }
}

impl<'a, T> IntoValues<'a> for &'a [T]
where
    &'a T: IntoValue<'a>,
{
    type Iter = Map<SliceIter<'a, T>, fn(&'a T) -> Cow<'a, str>>;

    fn into_values(self) -> Self::Iter {
        self.iter().map(IntoValue::into_value)
    }
}

/// Implements [`IntoValue`] for types that yield `&str` via `AsRef<str>` (borrowed, no allocation).
///
/// Usage: `impl_into_value_by_as_ref_str! { MyType, OtherType }`
#[macro_export]
macro_rules! impl_into_value_by_as_ref_str {
    ($($type:ty),* $(,)?) => {
        $(
            impl<'a> $crate::IntoValue<'a> for &'a $type where $type: AsRef<str> {
                fn into_value(self) -> $crate::__private::Cow<'a, str> {
                    $crate::__private::Cow::Borrowed(self.as_ref())
                }
            }
        )*
    };
}

/// Implements [`IntoValue`] for types that implement `Into<&'a str>` (borrowed; useful for enums).
///
/// Usage: `impl_into_value_by_into_str_ref! { MyEnum, OtherEnum }`
#[macro_export]
macro_rules! impl_into_value_by_into_str_ref {
    ($($type:ty),* $(,)?) => {
        $(
            impl<'a> $crate::IntoValue<'a> for $type where $type: Into<&'a str> {
                fn into_value(self) -> $crate::__private::Cow<'a, str> {
                    $crate::__private::Cow::Borrowed(self.into())
                }
            }
        )*
    };
}

/// Implements [`IntoValue`] for types that implement `ToString` (owned, allocates).
///
/// Usage: `impl_into_value_by_to_string! { u64, i32, MyType }`
#[macro_export]
macro_rules! impl_into_value_by_to_string {
    ($($type:ty),* $(,)?) => {
        $(
            impl<'a> $crate::IntoValue<'a> for $type where $type: ToString {
                fn into_value(self) -> $crate::__private::Cow<'a, str> {
                    $crate::__private::Cow::Owned(self.to_string())
                }
            }
        )*
    };
}

/// Builds [`KVPairs`] with literal-like syntax.
///
/// Syntax: `kv_pairs! [ "key" => value, ... ]` where each `value` must implement [`IntoValues`] (e.g. [`IntoValue`] or `Option<T>`).
///
/// # Examples
///
/// ```rust
/// use kv_pairs::{kv_pairs, KVPairs};
///
/// let empty: KVPairs = kv_pairs![];
/// let one = kv_pairs![ "a" => "b" ];
/// let two = kv_pairs![ "x" => 1_u32, "y" => "z" ];
/// ```
#[macro_export]
macro_rules! kv_pairs {
    () => {
        $crate::KVPairs::new()
    };
    (@inner, $result: expr $(,)?) => {};
    (@inner, $result: expr, $key:expr => $value:expr $(, $($($rest:tt)+)?)?) => {
        $result.push($key, $value);
        $($(kv_pairs!(@inner, $result, $($rest)+);)?)?
    };
    ($($input:tt)*) => {
        {
            let mut result = $crate::KVPairs::new();
            kv_pairs!(@inner, result, $($input)*);
            result
        }
    };
}

impl_into_value_by_to_string! {
    u64,
    u32,
    u16,
    u8,
    i64,
    i32,
    i16,
    i8,
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::ops::DerefMut;

    #[test]
    fn new_and_default_are_empty() {
        let p: KVPairs = KVPairs::new();
        assert!(p.content.is_empty());
        let q: KVPairs = KVPairs::default();
        assert!(q.content.is_empty());
    }

    #[test]
    fn push_str_borrows() {
        let mut p = KVPairs::new();
        let s = String::from("v");
        p.push_str("k", &s);
        assert_eq!(p.content.len(), 1);
        assert_eq!(p.content[0].0, "k");
        assert_eq!(p.content[0].1.as_ref(), "v");
    }

    #[test]
    fn push_owned_allocates() {
        let mut p = KVPairs::new();
        p.push_owned("key", "value");
        assert_eq!(p.content[0].0, "key");
        assert_eq!(p.content[0].1.as_ref(), "value");
    }

    #[test]
    fn push_one_with_into_value() {
        let mut p = KVPairs::new();
        p.push_one("a", "b");
        p.push_one("n", 42_u32);
        p.push_one("flag", true);
        assert_eq!(p.content.len(), 3);
        assert_eq!(p.content[0], ("a", Cow::Borrowed("b")));
        assert_eq!(p.content[1].1.as_ref(), "42");
        assert_eq!(p.content[2].1.as_ref(), "true");
    }

    #[test]
    fn push_some_adds() {
        let mut p = KVPairs::new();
        p.push("opt", Some("v"));
        assert_eq!(p.content.len(), 1);
        assert_eq!(p.content[0].1.as_ref(), "v");
    }

    #[test]
    fn push_none_skips() {
        let mut p = KVPairs::new();
        p.push("opt", None::<&str>);
        assert!(p.content.is_empty());
    }

    #[test]
    fn macro_empty() {
        let p = kv_pairs![];
        assert!(p.content.is_empty());
    }

    #[test]
    fn macro_single() {
        let p = kv_pairs![ "k" => "v" ];
        assert_eq!(p.content.len(), 1);
        assert_eq!(p.content[0].0, "k");
        assert_eq!(p.content[0].1.as_ref(), "v");
    }

    #[test]
    fn macro_multiple() {
        let p = kv_pairs![
            "a" => "1",
            "b" => 2_u64,
            "c" => false,
        ];
        assert_eq!(p.content.len(), 3);
        assert_eq!(p.content[0], ("a", Cow::Borrowed("1")));
        assert_eq!(p.content[1].1.as_ref(), "2");
        assert_eq!(p.content[2].1.as_ref(), "false");
    }

    #[test]
    fn into_values_for_option() {
        let some_val: Option<&str> = Some("x");
        let out: Vec<Cow<str>> = some_val.into_values().collect();
        assert_eq!(out.len(), 1);
        assert_eq!(out[0].as_ref(), "x");

        let none_val: Option<&str> = None;
        let out2: Vec<Cow<str>> = none_val.into_values().collect();
        assert!(out2.is_empty());
    }

    #[test]
    fn serialize_roundtrip() {
        let p = kv_pairs![ "a" => "b", "c" => 1_i32 ];
        let json = serde_json::to_string(&p.content).unwrap();
        let back: Vec<(String, String)> = serde_json::from_str(&json).unwrap();
        assert_eq!(back.len(), 2);
        assert_eq!((back[0].0.as_str(), back[0].1.as_str()), ("a", "b"));
        assert_eq!((back[1].0.as_str(), back[1].1.as_str()), ("c", "1"));
    }

    #[test]
    fn eq_and_hash() {
        let a = kv_pairs!["x" => "1", "y" => "2"];
        let b = kv_pairs!["x" => "1", "y" => "2"];
        let c = kv_pairs!["x" => "1"];
        assert_eq!(a, b);
        assert_ne!(a, c);
        use std::hash::{Hash, Hasher};
        let mut hasher = std::hash::DefaultHasher::new();
        a.hash(&mut hasher);
        let _ = hasher.finish();
    }

    #[test]
    fn as_ref_as_mut_borrow() {
        let p = kv_pairs!["a" => "b"];
        let slice: &[KVPair] = p.as_ref();
        assert_eq!(slice.len(), 1);
        let vec_ref: &Vec<KVPair> = p.as_ref();
        assert_eq!(vec_ref.len(), 1);
        let slice_borrow: &[KVPair] = p.borrow();
        assert_eq!(slice_borrow, slice);
        let vec_borrow: &Vec<KVPair> = p.borrow();
        assert_eq!(vec_borrow.len(), 1);
        let mut q = kv_pairs!["k" => "v"];
        let slice_mut: &mut [KVPair] = q.as_mut();
        slice_mut[0].1 = Cow::Borrowed("v2");
        assert_eq!(q[0].1.as_ref(), "v2");
    }

    #[test]
    fn deref_deref_mut() {
        let p = kv_pairs!["a" => "1", "b" => "2"];
        assert_eq!(p.len(), 2);
        assert!(!p.is_empty());
        let mut q = kv_pairs!["x" => "y"];
        q.deref_mut().push(("z", Cow::Borrowed("w")));
        assert_eq!(q.len(), 2);
    }

    #[test]
    fn index_index_mut() {
        let mut p = kv_pairs!["a" => "b", "c" => "d"];
        assert_eq!(p[0].0, "a");
        assert_eq!(p[1].1.as_ref(), "d");
        p[0].1 = Cow::Borrowed("b2");
        assert_eq!(p[0].1.as_ref(), "b2");
    }

    #[test]
    fn from_iterator_into_iterator() {
        let pairs: Vec<KVPair> = vec![("k1", Cow::Borrowed("v1")), ("k2", Cow::Borrowed("v2"))];
        let p: KVPairs = pairs.into_iter().collect();
        assert_eq!(p.len(), 2);
        let back: Vec<KVPair> = p.into_iter().collect();
        assert_eq!(back.len(), 2);
        assert_eq!(back[0].0, "k1");
        let p2 = kv_pairs!["a" => "b"];
        let ref_iter: Vec<_> = (&p2).into_iter().collect();
        assert_eq!(ref_iter.len(), 1);
        assert_eq!(ref_iter[0].0, "a");
    }
}
