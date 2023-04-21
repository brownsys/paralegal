//! [`nom`]-based parser-combinators for parsing the token stream in Rust
//! [`Attribute`](crate::rust::ast::Attribute)s.
//!
//! Usually used in a closure handed to
//! [`MetaItemMatch::match_extract`](crate::utils::MetaItemMatch::match_extract).
//!
//! The benefit of using a combinator library such as [`nom`] is not just that
//! it gives us boundaries for parsers that lets us (re)combine them, but also
//! that we get features that are annoying to implement (such as backtracking)
//! for free.
use crate::{
    consts,
    desc::{
        ExceptionAnnotation, Identifier, MarkerAnnotation, MarkerRefinement, MarkerRefinementKind,
        TypeDescriptor,
    },
    rust::*,
    Symbol,
};
use ast::{token, tokenstream};
use token::*;
use tokenstream::*;

pub extern crate nom;

use nom::{
    error::{Error, ErrorKind},
    Parser,
};

/// Just a newtype-wrapper for `CursorRef` so we can implement traits on it
/// (specifically [`nom::InputLength`]).
///
/// Construct if from a [`TokenStream`] with [`Self::from_stream`].
#[derive(Clone)]
pub struct I<'a>(CursorRef<'a>);
type R<'a, T> = nom::IResult<I<'a>, T>;

impl<'a> Iterator for I<'a> {
    type Item = &'a TokenTree;
    fn next(&mut self) -> Option<Self::Item> {
        self.0.next()
    }
}

impl<'a> I<'a> {
    /// Canonical constructor for [`I`]
    pub fn from_stream(s: &'a TokenStream) -> Self {
        I(s.trees())
    }
}

impl<'a> std::fmt::Debug for I<'a> {
    /// This only exists so we can use the standard `nom::Err`. A better
    /// solution would be to make our own error type that does not rely on this
    /// being printable.
    fn fmt(&self, fmt: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        for t in self.clone() {
            write!(fmt, "{:?}", t)?;
            write!(fmt, ",")?;
        }
        Ok(())
    }
}

impl<'a> nom::InputLength for I<'a> {
    fn input_len(&self) -> usize {
        // Extremely yikes, but the only way to get to this information. :(
        // It's a trick to break visibility as per https://www.reddit.com/r/rust/comments/cfxg60/comment/eud8n3y/
        type __EvilTarget<'a> = (&'a TokenStream, usize);
        use std::mem::{size_of, transmute};
        assert_eq!(size_of::<__EvilTarget>(), size_of::<Self>());
        let slf = unsafe { transmute::<&Self, &__EvilTarget<'_>>(self) };
        slf.0.len() - slf.1
    }
}

/// Parse any one token, returning the token.
///
/// This is the basic primitive that all other parsers are built from.
fn one(mut tree: I) -> R<&TokenTree> {
    match tree.next() {
        None => Result::Err(nom::Err::Error(Error::new(
            tree,
            nom::error::ErrorKind::IsNot,
        ))),
        Some(t) => Ok((tree, t)),
    }
}

/// Parse a single token that is not a subtree and return the token.
///
/// The difference between this and [`one`] is that this function expects the
/// token to be a [`TokenTree::Token`] and does not permit
/// [`TokenTree::Delimited`] subtrees.
pub fn one_token(i: I) -> R<&Token> {
    nom::combinator::map_res(one, |t| match t {
        TokenTree::Token(t) => Ok(t),
        _ => Result::Err(()),
    })(i)
}

/// Parse a [`TokenKind::Literal`] if it has a specific [`LitKind`] and return
/// the payload of the literal.
///
/// This can parse all types of literals since the literal payloads in these
/// token treed are uniformly represented as strings and need to be parsed to
/// extract the actual type of the literal. So you will likely want to call
/// [`str::parse`] on the result.
pub fn lit<'a, A, F: Fn(&str) -> Result<A, String> + 'a>(
    k: LitKind,
    f: F,
) -> impl FnMut(I<'a>) -> R<'a, A> {
    nom::combinator::map_res(one_token, move |t| match t {
        Token {
            kind: TokenKind::Literal(Lit {
                kind: knd, symbol, ..
            }),
            ..
        } if *knd == k => f(symbol.as_str()),
        _ => Result::Err("Wrong kind of token".to_string()),
    })
}

/// Parse an integer literal and return the integer.
pub fn integer(i: I) -> R<u16> {
    lit(LitKind::Integer, |symbol: &str| {
        symbol
            .parse()
            .map_err(|e: <u16 as std::str::FromStr>::Err| e.to_string())
    })(i)
}

/// Parse an identifier. Identifiers in annotations are similar to identifiers
/// in rust in general, e.g. strings or word character, numbers and underscores.
pub fn identifier(i: I) -> R<Symbol> {
    nom::combinator::map_res(one_token, |t| match t.ident() {
        Some((rustc_span::symbol::Ident { name, .. }, _)) => Ok(name),
        _ => Result::Err(()),
    })(i)
}

/// Expect the next token to be an identifier with the value `s`
pub fn assert_identifier<'a>(s: Symbol) -> impl FnMut(I<'a>) -> R<'a, ()> {
    nom::combinator::map_res(
        identifier,
        move |i| if i == s { Ok(()) } else { Result::Err(()) },
    )
}

/// Parse a [`TokenTree::Delimited`] with the delimiter character `delim`,
/// applying the subparser `p` to the tokens in between the delimiters and
/// return the result of the subparser.
pub fn delimited<'a, A, P: Parser<I<'a>, A, Error<I<'a>>>>(
    mut p: P,
    delim: Delimiter,
) -> impl FnMut(I<'a>) -> R<'a, A> {
    move |i| {
        one(i).and_then(|(i, t)| match t {
            TokenTree::Delimited(_, d, s) if *d == delim => {
                p.parse(I::from_stream(s)).map(|(mut rest, r)| {
                    assert!(rest.next().is_none());
                    (i, r)
                })
            }
            _ => Result::Err(nom::Err::Error(Error::new(i, ErrorKind::Fail))),
        })
    }
}

/// Expect the next token to have the token kind `k`.
pub fn assert_token<'a>(k: TokenKind) -> impl FnMut(I<'a>) -> R<'a, ()> {
    nom::combinator::map_res(
        one_token,
        move |t| if *t == k { Ok(()) } else { Result::Err(()) },
    )
}

/// Parse something dictionnary-like.
///
/// Expects the next token to be a braces delimited subtree containing pairs of
/// `keys` and `values` that are comme separated and where each key and value is
/// separated with an `=`. E.g. something of the form `{ k1 = v1, k2 = v2, ...}`
pub fn dict<'a, K, V, P: Parser<I<'a>, K, Error<I<'a>>>, G: Parser<I<'a>, V, Error<I<'a>>>>(
    keys: P,
    values: G,
) -> impl FnMut(I<'a>) -> R<'a, Vec<(K, V)>> {
    delimited(
        nom::multi::separated_list0(
            assert_token(TokenKind::Comma),
            nom::sequence::separated_pair(keys, assert_token(TokenKind::Eq), values),
        ),
        Delimiter::Brace,
    )
}

/// Parse bracket-delimited, comma-separated integers, e.g. `[1,2,3]`.
pub fn integer_list(i: I) -> R<Vec<u16>> {
    delimited(
        nom::multi::separated_list0(assert_token(TokenKind::Comma), integer),
        Delimiter::Bracket,
    )(i)
}

/// Parser for the payload of the `#[dfpp::output_type(...)]` annotation.
pub(crate) fn otype_ann_match(ann: &ast::MacArgs) -> Vec<TypeDescriptor> {
    match ann {
        ast::MacArgs::Delimited(_, _, stream) => {
            let mut p = nom::multi::separated_list0(
                assert_token(TokenKind::Comma),
                nom::combinator::map(identifier, Identifier::new),
            );
            p(I::from_stream(stream))
                .unwrap_or_else(|err: nom::Err<_>| {
                    panic!("parser failed on {ann:?} with error {err:?}")
                })
                .1
        }
        _ => panic!(),
    }
}

/// Parser for an [`ExceptionAnnotation`]
pub(crate) fn match_exception(ann: &rustc_ast::MacArgs) -> ExceptionAnnotation {
    use rustc_ast::*;
    match ann {
        ast::MacArgs::Delimited(_, _, stream) => {
            let p = |i| {
                let (i, verification_hash) = nom::combinator::opt(nom::sequence::preceded(
                    nom::sequence::tuple((
                        assert_identifier(*consts::VERIFICATION_HASH_SYM),
                        assert_token(TokenKind::Eq),
                    )),
                    lit(token::LitKind::Str, |s| {
                        crate::desc::VerificationHash::from_str_radix(s, 16)
                            .map_err(|e: std::num::ParseIntError| e.to_string())
                    }),
                ))(i)?;
                let _ = nom::combinator::eof(i)?;
                Ok(ExceptionAnnotation { verification_hash })
            };
            p(I::from_stream(stream))
                .unwrap_or_else(|err: nom::Err<_>| panic!("parser failed with error {err:?}"))
        }
        _ => panic!(),
    }
}

/// A parser for annotation refinements.
///
/// Is not guaranteed to consume the entire input if does not match. You may
/// want to call [`nom::combinator::eof`] afterwards to guarantee all input has
/// been consumed.
fn refinements_parser(i: I) -> R<MarkerRefinement> {
    nom::combinator::map_res(
        // nom::multi::separated_list0(
        //     assert_token(TokenKind::Comma),
        nom::branch::alt((
            nom::sequence::preceded(
                nom::sequence::tuple((
                    assert_identifier(*consts::ARG_SYM),
                    assert_token(TokenKind::Eq),
                )),
                nom::combinator::map(integer_list, MarkerRefinementKind::Argument),
            ),
            nom::combinator::value(
                MarkerRefinementKind::Return,
                assert_identifier(*consts::RETURN_SYM),
            ),
        )),
        //),
        |refinements| {
            vec![refinements]
                .into_iter()
                .try_fold(MarkerRefinement::empty(), MarkerRefinement::merge_kind)
        },
    )(i)
}

/// Parser for a [`LabelAnnotation`]
pub(crate) fn ann_match_fn(ann: &rustc_ast::MacArgs) -> MarkerAnnotation {
    use rustc_ast::*;
    use token::*;
    match ann {
        ast::MacArgs::Delimited(_, _, stream) => {
            let p = |i| {
                let (i, label) = identifier(i)?;
                let (i, cont) = nom::combinator::opt(assert_token(TokenKind::Comma))(i)?;
                let (i, refinement) = nom::combinator::cond(cont.is_some(), refinements_parser)(i)?;
                let (_, _) = nom::combinator::eof(i)?;
                Ok(MarkerAnnotation {
                    marker: label,
                    refinement: refinement.unwrap_or_else(MarkerRefinement::empty),
                })
            };
            p(I::from_stream(stream))
                .unwrap_or_else(|err: nom::Err<_>| panic!("parser failed with error {err:?}"))
        }
        _ => panic!(),
    }
}
