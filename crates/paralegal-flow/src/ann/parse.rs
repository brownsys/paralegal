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
use std::borrow::Cow;

use super::{
    ExceptionAnnotation, MarkerAnnotation, MarkerRefinement, MarkerRefinementKind, VerificationHash,
};
use crate::{
    utils::{resolve::def_path_res, TinyBitSet},
    Symbol,
};
use either::Either;
use nom_supreme::{
    error::ErrorTree,
    final_parser::{final_parser, RecreateContext},
    ParserExt,
};
use paralegal_spdg::Identifier;

use rustc_ast::{
    self as ast,
    token::{self, Delimiter, Lit, LitKind, Token, TokenKind},
    tokenstream, ExprKind,
};
use rustc_hir as hir;
use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;
use rustc_parse::parser as rustc_parser;
use rustc_span::Span;
use tokenstream::*;

pub extern crate nom;

use nom::{
    error::{ErrorKind, FromExternalError, ParseError},
    Parser,
};

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
type R<'a, T> = nom::IResult<I<'a>, T, ErrorTree<I<'a>>>;

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

impl std::fmt::Debug for I<'_> {
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

impl nom::InputLength for I<'_> {
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
        None => Result::Err(nom::Err::Error(ErrorTree::from_error_kind(
            tree,
            nom::error::ErrorKind::Eof,
        ))),
        Some(t) => Ok((tree, t)),
    }
}

#[derive(Debug, Clone, Copy)]
struct StructuralError {
    expected: Structure,
    found: Structure,
}

#[derive(Debug, Clone, Copy)]
enum Structure {
    Token,
    Delimited(Delimiter),
}

impl std::fmt::Display for Structure {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Structure::Token => write!(f, "token"),
            Structure::Delimited(delim) => write!(
                f,
                "section delimited by {}",
                match delim {
                    Delimiter::Parenthesis => Cow::Borrowed("(...)"),
                    Delimiter::Brace => "{...}".into(),
                    Delimiter::Bracket => "[...]".into(),
                    _ => format!("{delim:?}").into(),
                }
            ),
        }
    }
}

impl std::fmt::Display for StructuralError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Expected a {}, but got a {}", self.expected, self.found)
    }
}

impl std::error::Error for StructuralError {}

/// Parse a single token that is not a subtree and return the token.
///
/// The difference between this and [`one`] is that this function expects the
/// token to be a [`TokenTree::Token`] and does not permit
/// [`TokenTree::Delimited`] subtrees.
pub fn one_token(i: I) -> R<&Token> {
    nom::combinator::map_res(one, |t| match t {
        TokenTree::Token(t, _) => Ok(t),
        TokenTree::Delimited(_, _, delim, _) => Err(StructuralError {
            expected: Structure::Token,
            found: Structure::Delimited(*delim),
        }),
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
        _ => Result::Err("expected literal token".to_string()),
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

#[derive(Debug)]
struct NotAnIdentifierErr;
impl std::error::Error for NotAnIdentifierErr {}
impl std::fmt::Display for NotAnIdentifierErr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Expected identifier")
    }
}

/// Parse an identifier. Identifiers in annotations are similar to identifiers
/// in rust in general, e.g. strings or word character, numbers and underscores.
pub fn identifier(i: I) -> R<Symbol> {
    nom::combinator::map_res(one_token, |t| match t.ident() {
        Some((rustc_span::symbol::Ident { name, .. }, _)) => Ok(name),
        _ => Result::Err(NotAnIdentifierErr),
    })(i)
}

#[derive(Debug, Clone)]
struct NotIdentifierErr {
    expected: Symbol,
    found: Symbol,
}

impl std::error::Error for NotIdentifierErr {}

impl std::fmt::Display for NotIdentifierErr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Expected identifier `{}`, got `{}` instead",
            self.expected, self.found
        )
    }
}

/// Expect the next token to be an identifier with the value `s`
pub fn assert_identifier<'a>(s: Symbol) -> impl FnMut(I<'a>) -> R<'a, ()> {
    nom::combinator::map_res(identifier, move |i| {
        if i == s {
            Ok(())
        } else {
            Result::Err(NotIdentifierErr {
                expected: s,
                found: i,
            })
        }
    })
}

#[derive(Debug, Clone)]
struct UnusedInputErr;

impl std::error::Error for UnusedInputErr {}

impl std::fmt::Display for UnusedInputErr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Unused input left")
    }
}

/// Parse a [`TokenTree::Delimited`] with the delimiter character `delim`,
/// applying the subparser `p` to the tokens in between the delimiters and
/// return the result of the subparser.
pub fn delimited<'a, A, P: Parser<I<'a>, A, ErrorTree<I<'a>>> + 'a>(
    mut p: P,
    delim: Delimiter,
) -> impl FnMut(I<'a>) -> R<'a, A> {
    move |s| {
        let (s, tok) = one(s)?;
        let stream = match tok {
            TokenTree::Delimited(_, _, d, s) if *d == delim => s,
            t => {
                return Result::Err(nom::Err::Error(ErrorTree::from_external_error(
                    s,
                    ErrorKind::Fail,
                    StructuralError {
                        expected: Structure::Delimited(delim),
                        found: match t {
                            TokenTree::Token(_, _) => Structure::Token,
                            TokenTree::Delimited(_, _, d, _) => Structure::Delimited(*d),
                        },
                    },
                )));
            }
        };
        let (mut rest, r) = p.parse(I::from_stream(stream))?;

        if rest.next().is_some() {
            Result::Err(nom::Err::Error(ErrorTree::from_external_error(
                rest,
                ErrorKind::Fail,
                UnusedInputErr,
            )))
        } else {
            Ok((s, r))
        }
    }
}

#[derive(Debug, Clone)]
struct WrongTokenKindErr {
    expected: TokenKind,
    found: TokenKind,
}

/// Unsafe impl, because the [`TokenKind`] can contain an AST node
/// (in `Interpolated`). We need this impl though so we can return the expected
/// and found toke kind in the error.
///
/// We mostly hope this doesn't lead to data races. We protect against it a bit
/// by adding an `assert` to the `Display` impl.
unsafe impl Send for WrongTokenKindErr {}
/// Unsafe imlp, because the [`TokenKind`] can contain an AST node
/// (in `Interpolated`). We need this impl though so we can return the expected
/// and found toke kind in the error.
///
/// We mostly hope this doesn't lead to data races. We protect against it a bit
/// by adding an `assert` to the `Display` impl.
unsafe impl Sync for WrongTokenKindErr {}

impl std::error::Error for WrongTokenKindErr {}
impl std::fmt::Display for WrongTokenKindErr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // There is a theoretical possibility of race conditions with the
        // pointers stored in this token variant so this prevents us from
        // trying to read that data, just in case.
        assert!(!matches!(self.found, TokenKind::Interpolated(_)));
        write!(
            f,
            "Expected token kind {:?}, found {:?}",
            self.expected, self.found
        )
    }
}

/// Expect the next token to have the token kind `k`.
pub fn assert_token<'a>(k: TokenKind) -> impl Parser<I<'a>, (), ErrorTree<I<'a>>> + 'a {
    move |s| {
        let (s, t) = one_token(s)?;
        if *t == k {
            Ok((s, ()))
        } else {
            Result::Err(nom::Err::Error(ErrorTree::from_external_error(
                s,
                ErrorKind::Fail,
                WrongTokenKindErr {
                    expected: k.clone(),
                    found: t.kind.clone(),
                },
            )))
        }
    }
}

pub fn dict<
    'a,
    K: 'a,
    V: 'a,
    P: Parser<I<'a>, K, ErrorTree<I<'a>>> + 'a,
    G: Parser<I<'a>, V, ErrorTree<I<'a>>> + 'a,
>(
    keys: P,
    values: G,
) -> impl FnMut(I<'a>) -> R<'a, Vec<(K, V)>> {
    delimited(
        nom::multi::separated_list0(
            assert_token(TokenKind::Comma).context("expected ','"),
            nom::sequence::separated_pair(
                keys,
                assert_token(TokenKind::Eq).context("expected '='"),
                values,
            ),
        ),
        Delimiter::Brace,
    )
}

/// Parse bracket-delimited, comma-separated integers, e.g. `[1,2,3]`.
pub fn integer_list(i: I) -> R<Vec<Integer>> {
    delimited(
        nom::multi::separated_list0(
            assert_token(TokenKind::Comma).context("expected ','"),
            integer,
        ),
        Delimiter::Bracket,
    )(i)
}

/// Parse the `arguments` refinement.
///
/// Note that the `body` argument isn't actually always a trait function.
/// The `Provided` variant is (in this case) also used for normal functions.
pub fn arguments<'a, 'b>(
    tcx: TyCtxt<'_>,
    hir_id: hir::HirId,
    attr_span: Span,
) -> impl Parser<I<'b>, TinyBitSet, ErrorTree<I<'b>>> + use<'a, 'b, '_> {
    delimited(
        nom::multi::separated_list0(
            assert_token(TokenKind::Comma).context("expected ','"),
            nom::branch::alt((integer.map(Either::Left), identifier.map(Either::Right))),
        ),
        Delimiter::Bracket,
    )
    .map_res(move |options| {
        let id = hir_id.as_owner().ok_or(RefinementOnNonFunctionErr)?;
        let node = tcx.hir_owner_node(id);
        let body = node
            .body_id()
            .map(hir::TraitFn::Provided)
            .or(match node {
                hir::OwnerNode::TraitItem(
                    hir::TraitItem {
                        kind: hir::TraitItemKind::Fn(_, f),
                        ..
                    },
                    ..,
                ) => Some(*f),
                _ => None,
            })
            .ok_or(RefinementOnNonFunctionErr)?;
        let sig_info = match body {
            hir::TraitFn::Provided(id) => Either::Left(tcx.hir().body(id).params),
            hir::TraitFn::Required(idents) => Either::Right(idents),
        };

        Ok::<TinyBitSet, RefinementOnNonFunctionErr>(TinyBitSet::from_iter(
            options.into_iter().filter_map(|option| match option {
                Either::Left(i) => Some(i),
                Either::Right(s) => {
                    let found = match sig_info {
                        Either::Left(params) => params.iter().position(|arg| {
                            let pat_is_sym = |p: &hir::Pat| {
                                matches!(p.kind, hir::PatKind::Binding(_, _, ident, _)
                            if ident.name == s)
                            };

                            if pat_is_sym(arg.pat) {
                                true
                            } else if arg.pat.walk_short(pat_is_sym) {
                                tcx.dcx()
                                    .struct_span_err(
                                        arg.span,
                                        format!(
                                        "Refinement via name '{s}' cannot refer to pattern argument"
                                    ),
                                    )
                                    .with_span_note(tcx.def_span(id.def_id), "annotated item")
                                    .emit();
                                true
                            } else {
                                false
                            }
                        }),
                        Either::Right(idents) => idents.iter().position(|ident| ident.name == s),
                    };
                    if found.is_none() {
                        tcx.dcx()
                            .struct_span_err(
                                attr_span,
                                format!("Argument refinement '{s}' does not refer to any argument"),
                            )
                            .with_span_note(tcx.def_span(id.def_id), "annotated function")
                            .emit();
                    }
                    found.map(|idx| idx as Integer)
                }
            }),
        ))
    })
}

/// Parser for the payload of the `#[paralegal_flow::output_type(...)]` annotation.
pub(crate) fn otype_ann_match(ann: &ast::AttrArgs, tcx: TyCtxt) -> Result<Vec<DefId>, String> {
    match ann {
        ast::AttrArgs::Delimited(dargs) => {
            let mut parser = rustc_parser::Parser::new(&tcx.sess.psess, dargs.tokens.clone(), None);
            std::iter::from_fn(|| {
                if parser.token.kind == TokenKind::Eof {
                    return None;
                }
                let ExprKind::Path(qself, path) = &parser.parse_expr().ok()?.kind else {
                    return Some(Result::Err(format!(
                        "Expected path expression, got {:?}",
                        dargs.tokens
                    )));
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
        _ => Result::Err("Expected delimited annotation".to_owned()),
    }
}

/// Parser for an [`ExceptionAnnotation`]
pub(crate) fn match_exception(
    symbols: &Symbols,
    ann: &rustc_ast::AttrArgs,
) -> Result<ExceptionAnnotation, String> {
    use rustc_ast::*;
    apply_parser_in_delimited_annotation(
        |i| {
            let (i, verification_hash) = nom::combinator::opt(nom::sequence::preceded(
                nom::sequence::tuple((
                    assert_identifier(symbols.verification_hash_sym),
                    assert_token(TokenKind::Eq).context("expected '='"),
                )),
                lit(token::LitKind::Str, |s| {
                    VerificationHash::from_str_radix(s, 16)
                        .map_err(|e: std::num::ParseIntError| e.to_string())
                }),
            ))(i)?;
            Ok((i, ExceptionAnnotation { verification_hash }))
        },
        ann,
    )
}

/// A parser for annotation refinements.
///
/// Is not guaranteed to consume the entire input if does not match. You may
/// want to call [`nom::combinator::eof`] afterwards to guarantee all input has
/// been consumed.
fn refinements_parser<'a>(
    tcx: TyCtxt<'_>,
    symbols: &Symbols,
    hir_id: hir::HirId,
    i: I<'a>,
    attr_span: Span,
) -> R<'a, MarkerRefinement> {
    nom::combinator::map_res(
        // nom::multi::separated_list0(
        //     assert_token(TokenKind::Comma),
        nom::branch::alt((
            nom::sequence::preceded(
                nom::sequence::tuple((
                    assert_identifier(symbols.arg_sym),
                    assert_token(TokenKind::Eq).context("expected '='"),
                )),
                nom::combinator::map(
                    arguments(tcx, hir_id, attr_span),
                    MarkerRefinementKind::Argument,
                ),
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

#[derive(Debug, Clone)]
struct DisplaySpan(Span);

impl std::fmt::Display for DisplaySpan {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self.0)
    }
}

impl RecreateContext<I<'_>> for DisplaySpan {
    fn recreate_context(_: I<'_>, tail: I<'_>) -> Self {
        DisplaySpan(tail.0.clone().next().map_or(Span::default(), |f| f.span()))
    }
}

fn apply_parser_in_delimited_annotation<'a, A, P: Parser<I<'a>, A, ErrorTree<I<'a>>> + 'a>(
    p: P,
    ann: &'a rustc_ast::AttrArgs,
) -> Result<A, String> {
    use rustc_ast::*;
    match ann {
        ast::AttrArgs::Delimited(dargs) => final_parser(p)(I::from_stream(&dargs.tokens))
            .map_err(|err: ErrorTree<DisplaySpan>| err.to_string()),
        _ => Result::Err("Expected delimited annotation".to_owned()),
    }
}

#[derive(Debug)]
struct RefinementOnNonFunctionErr;

impl std::error::Error for RefinementOnNonFunctionErr {}
impl std::fmt::Display for RefinementOnNonFunctionErr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "This refinement can only be applied to functions or methods"
        )
    }
}

/// Parser for a [`LabelAnnotation`]
pub(crate) fn ann_match_fn(
    tcx: TyCtxt<'_>,
    symbols: &Symbols,
    hir_id: hir::HirId,
    ann: &rustc_ast::AttrArgs,
    attr_span: Span,
) -> Result<MarkerAnnotation, String> {
    use rustc_ast::*;
    use token::*;

    apply_parser_in_delimited_annotation(
        |i| {
            let (i, label) = identifier(i)?;
            let (i, cont) = nom::combinator::opt(assert_token(TokenKind::Comma))(i)?;
            let (i, refinement) = nom::combinator::cond(cont.is_some(), |c| {
                refinements_parser(tcx, symbols, hir_id, c, attr_span)
            })(i.clone())?;
            Ok((
                i,
                MarkerAnnotation {
                    marker: Identifier::new(label),
                    refinement: refinement.unwrap_or_else(MarkerRefinement::empty),
                },
            ))
        },
        ann,
    )
}
