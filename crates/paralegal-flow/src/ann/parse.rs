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
use super::{
    ExceptionAnnotation, MarkerAnnotation, MarkerRefinement, MarkerRefinementKind, VerificationHash,
};
use crate::{
    utils::{self, resolve::def_path_res, write_sep, Print, TinyBitSet},
    Symbol,
};
use paralegal_spdg::Identifier;

use rustc_ast::{self as ast, token, tokenstream, ExprKind};
use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;
use rustc_parse::parser as rustc_parser;
use token::*;
use tokenstream::*;

pub extern crate nom;

use nom::{error::Error, Parser};

pub struct Symbols {
    /// The symbol `arguments` which we use for refinement in a `#[paralegal_flow::marker(...)]`
    /// annotation.
    arg_sym: Symbol,
    /// The symbol `return` which we use for refinement in a `#[paralegal_flow::marker(...)]`
    /// annotation.
    return_sym: Symbol,
    /// The symbol `verification_hash` which we use for refinement in a
    /// `#[paralegal_flow::exception(...)]` annotation.
    verification_hash_sym: Symbol,
}

impl Default for Symbols {
    fn default() -> Self {
        Self {
            arg_sym: Symbol::intern("arguments"),
            return_sym: Symbol::intern("return"),
            verification_hash_sym: Symbol::intern("verification_hash"),
        }
    }
}

/// Just a newtype-wrapper for `CursorRef` so we can implement traits on it
/// (specifically [`nom::InputLength`]).
///
/// Construct if from a [`TokenStream`] with [`Self::from_stream`].
#[derive(Clone)]
pub struct I<'a>(RefTokenTreeCursor<'a>);
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
        // Cloning is cheap, because this is just a pointer + a count
        self.clone().0.count()
    }
}

type Integer = u32;

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
        TokenTree::Token(t, _) => Ok(t),
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
pub fn integer(i: I) -> R<Integer> {
    lit(LitKind::Integer, |symbol: &str| {
        symbol
            .parse()
            .map_err(|e: <Integer as std::str::FromStr>::Err| e.to_string())
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
pub fn delimited<'a, A, P: Parser<I<'a>, A, Error<I<'a>>> + 'a>(
    mut p: P,
    delim: Delimiter,
) -> impl FnMut(I<'a>) -> R<'a, A> {
    nom::combinator::map_res(
        nom::combinator::map_res(
            nom::combinator::map_res(one, move |t| match t {
                TokenTree::Delimited(_, d, s) if *d == delim => Ok(s),
                _ => Result::Err(""),
            }),
            move |s| p.parse(I::from_stream(s)),
        ),
        |(mut rest, r)| {
            if rest.next().is_some() {
                Result::Err("")
            } else {
                Ok(r)
            }
        },
    )
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
pub fn dict<
    'a,
    K: 'a,
    V: 'a,
    P: Parser<I<'a>, K, Error<I<'a>>> + 'a,
    G: Parser<I<'a>, V, Error<I<'a>>> + 'a,
>(
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
pub fn integer_list(i: I) -> R<Vec<Integer>> {
    delimited(
        nom::multi::separated_list0(assert_token(TokenKind::Comma), integer),
        Delimiter::Bracket,
    )(i)
}

pub fn tiny_bitset(i: I) -> R<TinyBitSet> {
    nom::combinator::map(integer_list, TinyBitSet::from_iter)(i)
}

/// Parser for the payload of the `#[paralegal_flow::output_type(...)]` annotation.
pub(crate) fn otype_ann_match(ann: &ast::AttrArgs, tcx: TyCtxt) -> Result<Vec<DefId>, String> {
    match ann {
        ast::AttrArgs::Delimited(dargs) => {
            let mut parser =
                rustc_parser::Parser::new(&tcx.sess.parse_sess, dargs.tokens.clone(), None);
            std::iter::from_fn(|| {
                if parser.token.kind == TokenKind::Eof {
                    return None;
                }
                let ExprKind::Path(qself, path) = &parser.parse_expr().ok()?.kind else {
                    return Some(Result::Err(format!("Expected path expression")));
                };
                if parser.token.kind != TokenKind::Eof {
                    parser.expect(&TokenKind::Comma).ok()?;
                }
                Some(
                    def_path_res(tcx, qself.as_deref(), &path.segments)
                        .map_err(|err| format!("Failed resolution: {err:?}",))
                        .map(|d| d.def_id()),
                )
            })
            .collect()
        }
        _ => Result::Err("Expected delimoted annotation".to_owned()),
    }
}

/// Parser for an [`ExceptionAnnotation`]
pub(crate) fn match_exception(
    symbols: &Symbols,
    ann: &rustc_ast::AttrArgs,
) -> Result<ExceptionAnnotation, String> {
    use rustc_ast::*;
    match ann {
        ast::AttrArgs::Delimited(dargs) => {
            let p = |i| {
                let (i, verification_hash) = nom::combinator::opt(nom::sequence::preceded(
                    nom::sequence::tuple((
                        assert_identifier(symbols.verification_hash_sym),
                        assert_token(TokenKind::Eq),
                    )),
                    lit(token::LitKind::Str, |s| {
                        VerificationHash::from_str_radix(s, 16)
                            .map_err(|e: std::num::ParseIntError| e.to_string())
                    }),
                ))(i)?;
                let _ = nom::combinator::eof(i)?;
                Ok(ExceptionAnnotation { verification_hash })
            };
            p(I::from_stream(&dargs.tokens))
                .map_err(|err: nom::Err<_>| format!("parser failed with error {err:?}"))
        }
        _ => Result::Err("Expected delimited annotation".to_owned()),
    }
}

/// A parser for annotation refinements.
///
/// Is not guaranteed to consume the entire input if does not match. You may
/// want to call [`nom::combinator::eof`] afterwards to guarantee all input has
/// been consumed.
fn refinements_parser<'a>(symbols: &Symbols, i: I<'a>) -> R<'a, MarkerRefinement> {
    nom::combinator::map_res(
        // nom::multi::separated_list0(
        //     assert_token(TokenKind::Comma),
        nom::branch::alt((
            nom::sequence::preceded(
                nom::sequence::tuple((
                    assert_identifier(symbols.arg_sym),
                    assert_token(TokenKind::Eq),
                )),
                nom::combinator::map(tiny_bitset, MarkerRefinementKind::Argument),
            ),
            nom::combinator::value(
                MarkerRefinementKind::Return,
                assert_identifier(symbols.return_sym),
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
pub(crate) fn ann_match_fn(
    symbols: &Symbols,
    ann: &rustc_ast::AttrArgs,
) -> Result<MarkerAnnotation, String> {
    use rustc_ast::*;
    use token::*;
    match ann {
        ast::AttrArgs::Delimited(dargs) => {
            let p = |i| {
                let (i, label) = identifier(i)?;
                let (i, cont) = nom::combinator::opt(assert_token(TokenKind::Comma))(i)?;
                let (i, refinement) =
                    nom::combinator::cond(cont.is_some(), |c| refinements_parser(symbols, c))(i)?;
                let (_, _) = nom::combinator::eof(i)?;
                Ok(MarkerAnnotation {
                    marker: Identifier::new(label),
                    refinement: refinement.unwrap_or_else(MarkerRefinement::empty),
                })
            };
            p(I::from_stream(&dargs.tokens))
                .map_err(|err: nom::Err<_>| format!("parser failed with error {err:?}"))
        }
        _ => Result::Err("Expected delimited annotation".to_owned()),
    }
}
