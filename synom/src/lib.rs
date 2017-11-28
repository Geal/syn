//! Adapted from [`nom`](https://github.com/Geal/nom) by removing the
//! `IPResult::Incomplete` variant which:
//!
//! - we don't need,
//! - is an unintuitive footgun when working with non-streaming use cases, and
//! - more than doubles compilation time.
//!
//! ## Whitespace handling strategy
//!
//! As (sy)nom is a parser combinator library, the parsers provided here and
//! that you implement yourself are all made up of successively more primitive
//! parsers, eventually culminating in a small number of fundamental parsers
//! that are implemented in Rust. Among these are `punct!` and `keyword!`.
//!
//! All synom fundamental parsers (those not combined out of other parsers)
//! should be written to skip over leading whitespace in their input. This way,
//! as long as every parser eventually boils down to some combination of
//! fundamental parsers, we get correct whitespace handling at all levels for
//! free.
//!
//! For our use case, this strategy is a huge improvement in usability,
//! correctness, and compile time over nom's `ws!` strategy.

extern crate proc_macro;
extern crate proc_macro2;

#[macro_use] extern crate nom;

#[cfg(feature = "printing")]
extern crate quote;

#[doc(hidden)]
pub use proc_macro2::{TokenTree, TokenStream};

use std::convert::From;
use std::error::Error;
use std::fmt;
use nom::{Convert,IResult,ErrorKind};

#[cfg(feature = "parsing")]
#[doc(hidden)]
pub mod helper;

pub mod delimited;
pub mod tokens;
pub mod span;
pub mod cursor;

pub use cursor::{SynomBuffer, Cursor};

/// The result of a parser
pub type PResult<'a, O> = IResult<Cursor<'a>, O, ParseError>;
//Result<(Cursor<'a>, O), ParseError>;

/// An error with a default error message.
///
/// NOTE: We should provide better error messages in the future.
pub fn parse_error<'a,O>(input: Cursor<'a>) -> PResult<'a, O> {
    Err(nom::Err::Error(error_position!(ErrorKind::Custom(ParseError(None)), input)))
}

pub trait Synom: Sized {
    fn parse(input: Cursor) -> PResult<Self>;

    fn description() -> Option<&'static str> {
        None
    }
}

#[derive(Debug,Clone)]
pub struct ParseError(Option<String>);

impl Error for ParseError {
    fn description(&self) -> &str {
        match self.0 {
            Some(ref desc) => desc,
            None => "failed to parse",
        }
    }
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        <str as fmt::Display>::fmt(self.description(), f)
    }
}

impl From<proc_macro2::LexError> for ParseError {
    fn from(_: proc_macro2::LexError) -> ParseError {
        ParseError(Some("error while lexing input string".to_owned()))
    }
}

impl From<proc_macro::LexError> for ParseError {
    fn from(_: proc_macro::LexError) -> ParseError {
        ParseError(Some("error while lexing input string".to_owned()))
    }
}

impl ParseError {
    // For syn use only. Not public API.
    #[doc(hidden)]
    pub fn new<T: Into<String>>(msg: T) -> Self {
        ParseError(Some(msg.into()))
    }

    #[doc(hidden)]
    pub fn new_empty() -> Self {
        ParseError(None)
    }
}

impl Synom for TokenStream {
    fn parse(input: Cursor) -> PResult<Self> {
        Ok((Cursor::empty(), input.token_stream()))
    }
}

impl<'a> From<nom::Err<Cursor<'a>>> for ParseError {
    fn from(_: nom::Err<Cursor<'a>>) -> Self {
        ParseError(None)
    }
}

impl From<u32> for ParseError {
    fn from(_: u32) -> Self {
        ParseError(None)
    }
}

impl Convert<ParseError> for ParseError {
    fn convert(e: ParseError) -> Self {
        e
    }
}

/// Define a function from a parser combination.
///
/// - **Syntax:** `named!(NAME -> TYPE, PARSER)` or `named!(pub NAME -> TYPE, PARSER)`
///
/// ```rust
/// # extern crate syn;
/// # #[macro_use] extern crate synom;
/// # use syn::Type;
/// # use synom::delimited::Delimited;
/// // One or more Rust types separated by commas.
/// named!(pub comma_separated_types -> Delimited<Type, Token![,]>,
///     call!(Delimited::parse_separated_nonempty)
/// );
/// # fn main() {}
/// ```
#[macro_export]
macro_rules! named {
    ($name:ident -> $o:ty, $submac:ident!( $($args:tt)* )) => {
        fn $name(i: $crate::Cursor) -> $crate::PResult<$o> {
            let res: $crate::PResult<$o> = $submac!(i, $($args)*);
            res
        }
    };

    (pub $name:ident -> $o:ty, $submac:ident!( $($args:tt)* )) => {
        pub fn $name(i: $crate::Cursor) -> $crate::PResult<$o> {
            $submac!(i, $($args)*)
        }
    };

    // These two variants are for defining named parsers which have custom
    // arguments, and are called with `call!()`
    ($name:ident($($params:tt)*) -> $o:ty, $submac:ident!( $($args:tt)* )) => {
        fn $name(i: $crate::Cursor, $($params)*) -> $crate::PResult<$o> {
            $submac!(i, $($args)*)
        }
    };

    (pub $name:ident($($params:tt)*) -> $o:ty, $submac:ident!( $($args:tt)* )) => {
        pub fn $name(i: $crate::Cursor, $($params)*) -> $crate::PResult<$o> {
            $submac!(i, $($args)*)
        }
    };
}


// Somehow this helps with type inference in `map!`.
//
// Not public API.
#[doc(hidden)]
pub fn invoke<T, R, F: FnOnce(T) -> R>(f: F, t: T) -> R {
    f(t)
}


/// Parse zero or more values using the given parser.
///
/// - **Syntax:** `many0!(THING)`
/// - **Output:** `Vec<THING>`
///
/// You may also be looking for:
///
/// - `call!(Delimited::parse_separated)` - zero or more values with separator
/// - `call!(Delimited::parse_separated_nonempty)` - one or more values
/// - `call!(Delimited::parse_terminated)` - zero or more, allows trailing separator
///
/// ```rust
/// extern crate syn;
/// #[macro_use] extern crate synom;
///
/// use syn::Item;
///
/// named!(items -> Vec<Item>, many0!(syn!(Item)));
///
/// # fn main() {}
#[macro_export]
macro_rules! many0 {
    ($i:expr, $submac:ident!( $($args:tt)* )) => {{
        let ret;
        let mut res   = ::std::vec::Vec::new();
        let mut input = $i;

        loop {
            if input.eof() {
                ret = ::std::result::Result::Ok((input, res));
                break;
            }

            match $submac!(input, $($args)*) {
                ::std::result::Result::Err(_) => {
                    ret = ::std::result::Result::Ok((input, res));
                    break;
                }
                ::std::result::Result::Ok((i, o)) => {
                    // loop trip must always consume (otherwise infinite loops)
                    if i == input {
                        ret = $crate::parse_error(input);
                        break;
                    }

                    res.push(o);
                    input = i;
                }
            }
        }

        ret
    }};

    ($i:expr, $f:expr) => {
        $crate::many0($i, $f)
    };
}

// Improve compile time by compiling this loop only once per type it is used
// with.
//
// Not public API.
#[doc(hidden)]
pub fn many0<'a, T>(mut input: Cursor, f: fn(Cursor) -> PResult<T>) -> PResult<Vec<T>> {
    let mut res = Vec::new();

    loop {
        if input.eof() {
            return Ok((input, res));
        }

        match f(input) {
            Err(_) => {
                return Ok((input, res));
            }
            Ok((i, o)) => {
                // loop trip must always consume (otherwise infinite loops)
                if i == input {
                    return Err(nom::Err::Error(error_position!(ErrorKind::Many0, input)));
                }

                res.push(o);
                input = i;
            }
        }
    }
}

/// Unconditionally fail to parse anything. This may be useful in ignoring some
/// arms of a `switch!` parser.
///
/// - **Syntax:** `reject!()`
/// - **Output:** never succeeds
///
/// ```rust
/// extern crate syn;
/// #[macro_use] extern crate synom;
///
/// use syn::Item;
///
/// // Parse any item, except for a module.
/// named!(almost_any_item -> Item,
///     switch!(syn!(Item),
///         Item::Mod(_) => reject!()
///         |
///         ok => value!(ok)
///     )
/// );
///
/// # fn main() {}
/// ```
#[macro_export]
macro_rules! reject {
    ($i:expr,) => {
        $crate::parse_error($i)
    }
}


/// Run a series of parsers, one after another, optionally assigning the results
/// a name. Fail if any of the parsers fails.
///
/// Produces the result of evaluating the final expression in parentheses with
/// all of the previously named results bound.
///
/// - **Syntax:** `do_parse!(name: THING1 >> THING2 >> (RESULT))`
/// - **Output:** `RESULT`
///
/// ```rust
/// extern crate syn;
/// #[macro_use] extern crate synom;
/// extern crate proc_macro2;
///
/// use syn::{Ident, TokenTree};
/// use synom::tokens::Paren;
/// use proc_macro2::TokenStream;
///
/// // Parse a macro invocation like `stringify!($args)`.
/// named!(simple_mac -> (Ident, (TokenStream, Paren)), do_parse!(
///     name: syn!(Ident) >>
///     punct!(!) >>
///     body: parens!(syn!(TokenStream)) >>
///     (name, body)
/// ));
///
/// # fn main() {}
/// ```
#[macro_export]
macro_rules! do_parse {
    ($i:expr, ( $($rest:expr),* )) => {
        ::std::result::Result::Ok(($i, ( $($rest),* )))
    };

    ($i:expr, $e:ident >> $($rest:tt)*) => {
        do_parse!($i, call!($e) >> $($rest)*)
    };

    ($i:expr, $submac:ident!( $($args:tt)* ) >> $($rest:tt)*) => {
        match $submac!($i, $($args)*) {
            ::std::result::Result::Err(err) =>
                ::std::result::Result::Err(err),
            ::std::result::Result::Ok((i, _)) =>
                do_parse!(i, $($rest)*),
        }
    };

    ($i:expr, $field:ident : $e:ident >> $($rest:tt)*) => {
        do_parse!($i, $field: call!($e) >> $($rest)*)
    };

    ($i:expr, $field:ident : $submac:ident!( $($args:tt)* ) >> $($rest:tt)*) => {
        match $submac!($i, $($args)*) {
            ::std::result::Result::Err(err) =>
                ::std::result::Result::Err(err),
            ::std::result::Result::Ok((i, o)) => {
                let $field = o;
                do_parse!(i, $($rest)*)
            },
        }
    };

    ($i:expr, mut $field:ident : $e:ident >> $($rest:tt)*) => {
        do_parse!($i, mut $field: call!($e) >> $($rest)*)
    };

    ($i:expr, mut $field:ident : $submac:ident!( $($args:tt)* ) >> $($rest:tt)*) => {
        match $submac!($i, $($args)*) {
            ::std::result::Result::Err(err) =>
                ::std::result::Result::Err(err),
            ::std::result::Result::Ok((i, o)) => {
                let mut $field = o;
                do_parse!(i, $($rest)*)
            },
        }
    };
}

#[macro_export]
macro_rules! input_end {
    ($i:expr,) => {
        $crate::input_end($i)
    };
}

// Not a public API
#[doc(hidden)]
pub fn input_end<'a>(input: Cursor<'a>) -> PResult<'a, ()> {
    if input.eof() {
        Ok((Cursor::empty(), ()))
    } else {
        Err(nom::Err::Error(error_position!(ErrorKind::Eof, input)))
    }
}
