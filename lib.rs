//! This crate exposes a `.peeking()` method, for looking at the next element in
//! an iterator without consuming it.
//!
//! Unlike the [`peekable`][1] method in the standard library, `peeking` can be
//! *stacked*. This means that chaining multiple calls of `peeking` will
//! increase the number of elements returned by `peek`.
//!
//! # Example
//!
//! ```rust
//! # use duck::PeekingExt;
//! let anatids = vec!["duck", "goose", "swan"];
//!
//! // Since .peeking() is called twice, this iterator will peek two elements ahead
//! let mut iter = anatids.into_iter().peeking().peeking();
//! assert_eq!(iter.peek(), Some((&"duck", Some(&"goose"))));
//!
//! // Step the iterator twice
//! iter.next(); iter.next();
//!
//! // Now we're at "swan", which has no elements after it
//! assert_eq!(iter.peek(), Some((&"swan", None)));
//! ```
//!
//! [1]: https://doc.rust-lang.org/std/iter/trait.Iterator.html#method.peekable

#![doc(html_root_url = "https://docs.rs/duck/0.1.0")]

/// An extension trait that adds a `.peeking()` method to iterators.
///
/// See the top-level documentation for how to use this trait.
pub trait PeekingExt: Iterator + Sized {
    fn peeking(self) -> Goose<Self> {
        Goose::new(self)
    }
}

impl<I: Iterator> PeekingExt for I {}

/// An internal trait that represents either a `Duck` or a `Goose`.
pub trait Anatid<'a>: Iterator {
    type PeekItem: 'a;
    fn peek(&'a mut self) -> Option<Self::PeekItem>;
}

// `Duck` and `Goose` have identical implementations for `Iterator`
// https://github.com/rust-lang/rust/blob/2e6334062e2be142125e99d63867711da505cc9e/src/libcore/iter/mod.rs#L1408-L1473
macro_rules! impl_iterator {
    ($T:ident) => {
        impl<I: Iterator> Iterator for $T<I> {
            type Item = I::Item;

            #[inline]
            fn next(&mut self) -> Option<I::Item> {
                match self.peeked.take() {
                    Some(v) => v,
                    None => self.iter.next(),
                }
            }

            #[inline]
            fn count(mut self) -> usize {
                match self.peeked.take() {
                    Some(None) => 0,
                    Some(Some(_)) => 1 + self.iter.count(),
                    None => self.iter.count(),
                }
            }

            #[inline]
            fn nth(&mut self, n: usize) -> Option<I::Item> {
                match self.peeked.take() {
                    // the .take() below is just to avoid "move into pattern guard"
                    Some(ref mut v) if n == 0 => v.take(),
                    Some(None) => None,
                    Some(Some(_)) => self.iter.nth(n - 1),
                    None => self.iter.nth(n),
                }
            }

            #[inline]
            fn last(mut self) -> Option<I::Item> {
                let peek_opt = match self.peeked.take() {
                    Some(None) => return None,
                    Some(v) => v,
                    None => None,
                };
                self.iter.last().or(peek_opt)
            }

            #[inline]
            fn size_hint(&self) -> (usize, Option<usize>) {
                let peek_len = match self.peeked {
                    Some(None) => return (0, Some(0)),
                    Some(Some(_)) => 1,
                    None => 0,
                };
                let (lo, hi) = self.iter.size_hint();
                let lo = lo.saturating_add(peek_len);
                let hi = hi.and_then(|x| x.checked_add(peek_len));
                (lo, hi)
            }
        }

        impl<I: ExactSizeIterator> ExactSizeIterator for $T<I> {}

        // Requires nightly
        // impl<I: FusedIterator> FusedIterator for $T<I> {}
    };
}

/// Extends a plain `Iterator` with the ability to peek a single element.
#[derive(Clone, Debug)]
pub struct Goose<I: Iterator> {
    iter: I,
    peeked: Option<Option<I::Item>>,
}

impl<I: Iterator> Goose<I> {
    fn new(iter: I) -> Self {
        Goose { iter, peeked: None }
    }

    /// Inspect the next element of the iterator without consuming it.
    pub fn peek(&mut self) -> Option<&I::Item> {
        Anatid::peek(self)
    }

    /// Extends the iterator to peek two elements instead of one.
    pub fn peeking(self) -> Duck<Self> {
        Duck::new(self)
    }
}

impl_iterator!(Goose);

// https://github.com/rust-lang/rust/blob/2e6334062e2be142125e99d63867711da505cc9e/src/libcore/iter/mod.rs#L1475-L1525
impl<'a, I: Iterator> Anatid<'a> for Goose<I> where I::Item: 'a {
    type PeekItem = &'a I::Item;

    fn peek(&'a mut self) -> Option<&'a I::Item> {
        if self.peeked.is_none() {
            self.peeked = Some(self.iter.next());
        }
        match self.peeked {
            Some(Some(ref value)) => Some(value),
            Some(None) => None,
            _ => unreachable!(),
        }
    }
}

/// Extends an existing `Duck` or `Goose` to peek one more element.
#[derive(Clone, Debug)]
pub struct Duck<I: Iterator> {
    iter: I,
    peeked: Option<Option<I::Item>>,
}

impl<'a, I: Anatid<'a>> Duck<I> {
    fn new(iter: I) -> Self {
        Duck { iter, peeked: None }
    }

    /// Inspect the next *n* elements in the iterator without consuming them,
    /// where *n* is the number of `Duck` or `Goose` types in the stack.
    pub fn peek(&'a mut self) -> Option<(&'a I::Item, Option<<I as Anatid<'a>>::PeekItem>)> {
        Anatid::peek(self)
    }
}

impl<'a, I: Anatid<'a>> Duck<I> where I::Item: 'a {
    /// Extends the iterator to peek one more element.
    pub fn peeking(self) -> Duck<Self> {
        Duck::new(self)
    }
}

impl_iterator!(Duck);

// https://github.com/rust-lang/rust/blob/2e6334062e2be142125e99d63867711da505cc9e/src/libcore/iter/mod.rs#L1475-L1525
impl<'a, I: Anatid<'a>> Anatid<'a> for Duck<I> where I::Item: 'a {
    type PeekItem = (&'a I::Item, Option<I::PeekItem>);

    fn peek(&'a mut self) -> Option<Self::PeekItem> {
        if self.peeked.is_none() {
            self.peeked = Some(self.iter.next());
        }
        match self.peeked {
            Some(Some(ref value)) => Some((value, self.iter.peek())),
            Some(None) => None,
            _ => unreachable!(),
        }
    }
}

#[test]
fn simple() {
    let iter = vec![0, 1, 2].into_iter();
    let mut iter = iter.peeking().peeking().peeking();
    assert_eq!(iter.peek(), Some((&0, Some((&1, Some(&2))))));
    assert_eq!(iter.next(), Some(0));
    assert_eq!(iter.peek(), Some((&1, Some((&2, None)))));
    assert_eq!(iter.next(), Some(1));
    assert_eq!(iter.peek(), Some((&2, None)));
    assert_eq!(iter.next(), Some(2));
    assert_eq!(iter.peek(), None);
    assert_eq!(iter.next(), None);
}