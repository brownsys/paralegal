use crate::rust::*;

use crate::desc::{Annotation, AnnotationRefinement};
use crate::{HashMap, Symbol};
use ast::{token, tokenstream};
use token::*;
use tokenstream::*;

pub extern crate nom;

use nom::{
    error::{Error, ErrorKind},
    Parser,
};

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
    pub fn from_stream(s: &'a TokenStream) -> Self {
        I(s.trees())
    }
}

impl<'a> std::fmt::Debug for I<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
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
        let slf = unsafe { transmute::<&Self, &__EvilTarget<'_>>(&self) };
        slf.0.len() - slf.1
    }
}
fn one<'a>() -> impl FnMut(I<'a>) -> R<'a, &'a TokenTree> {
    |mut tree: I<'a>| match tree.next() {
        None => Result::Err(nom::Err::Error(Error::new(
            tree,
            nom::error::ErrorKind::IsNot,
        ))),
        Some(t) => Ok((tree, t)),
    }
}

pub fn one_token<'a>() -> impl FnMut(I<'a>) -> R<'a, &'a Token> {
    nom::combinator::map_res(one(), |t| match t {
        TokenTree::Token(t) => Ok(t),
        _ => Result::Err(()),
    })
}

pub fn lit<'a, A, F: Fn(&str) -> Result<A, String> + 'a>(
    k: LitKind,
    f: F,
) -> impl FnMut(I<'a>) -> R<'a, A> {
    nom::combinator::map_res(one_token(), move |t| match t {
        Token {
            kind: TokenKind::Literal(Lit {
                kind: knd, symbol, ..
            }),
            ..
        } if *knd == k => f(symbol.as_str()),
        _ => Result::Err("Wrong kind of token".to_string()),
    })
}

pub fn integer<'a>() -> impl FnMut(I<'a>) -> R<'a, u16> {
    lit(LitKind::Integer, |symbol: &str| {
        symbol
            .parse()
            .map_err(|e: <u16 as std::str::FromStr>::Err| e.to_string())
    })
}

pub fn identifier<'a>() -> impl FnMut(I<'a>) -> R<'a, Symbol> {
    nom::combinator::map_res(one_token(), |t| match t.ident() {
        Some((rustc_span::symbol::Ident { name, .. }, _)) => Ok(name),
        _ => Result::Err(()),
    })
}

pub fn assert_identifier<'a>(s: Symbol) -> impl FnMut(I<'a>) -> R<'a, ()> {
    nom::combinator::map_res(
        identifier(),
        move |i| if i == s { Ok(()) } else { Result::Err(()) },
    )
}

pub fn delimited<'a, A, P: Parser<I<'a>, A, Error<I<'a>>>>(
    mut p: P,
    delim: Delimiter,
) -> impl FnMut(I<'a>) -> R<'a, A> {
    move |i| {
        one()(i).and_then(|(i, t)| match t {
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

pub fn assert_token<'a>(k: TokenKind) -> impl FnMut(I<'a>) -> R<'a, ()> {
    nom::combinator::map_res(
        one_token(),
        move |t| if *t == k { Ok(()) } else { Result::Err(()) },
    )
}

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

pub fn integer_list<'a>() -> impl FnMut(I<'a>) -> R<'a, Vec<u16>> {
    delimited(
        nom::multi::separated_list0(assert_token(TokenKind::Comma), integer()),
        Delimiter::Bracket,
    )
}

fn translate_delimiter(d: rustc_ast::MacDelimiter) -> rustc_ast::token::Delimiter {
    use rustc_ast::*;
    match d {
        MacDelimiter::Parenthesis => Delimiter::Parenthesis,
        MacDelimiter::Brace => Delimiter::Brace,
        MacDelimiter::Bracket => Delimiter::Bracket,
    }
}

pub(crate) fn ann_match_fn(ann: &rustc_ast::MacArgs) -> Annotation {
    use rustc_ast::*;
    use token::*;
    match ann {
        ast::MacArgs::Delimited(sp, delim, stream) => {
            let p = |i| {
                let (i, label) = identifier()(i)?;
                let (i, refinement) = nom::combinator::map(
                    nom::combinator::opt(nom::sequence::preceded(
                        nom::sequence::tuple((
                            assert_token(TokenKind::Comma),
                            assert_identifier(*crate::ARG_SYM),
                            assert_token(TokenKind::Eq),
                        )),
                        nom::combinator::map(integer_list(), |il| {
                            AnnotationRefinement::Argument(il)
                        }),
                    )),
                    |o| o.unwrap_or(AnnotationRefinement::None),
                )(i)?;
                let _ = nom::combinator::eof(i)?;
                Ok(Annotation { label, refinement })
            };
            p(I::from_stream(&stream)).unwrap_or_else(|err: nom::Err<_>| {
                panic!("parser failed on {ann:?} with error {err:?}")
            })
        }
        _ => panic!(),
    }
}
