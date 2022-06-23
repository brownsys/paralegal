use crate::rust::*;

use crate::HashMap;
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

#[derive(PartialEq, Eq, PartialOrd, Ord, Debug)]
pub struct SinkAnnotationPayload {
    pub leaks: Vec<u16>,
    pub scopes: Vec<u16>,
}

pub(crate) fn sink_ann_match_fn(ann: &rustc_ast::MacArgs) -> SinkAnnotationPayload {
    use rustc_ast::*;
    use token::*;

    let mut m = match ann {
        ast::MacArgs::Delimited(sp, delim, stream) => {
            let s = tokenstream::TokenStream::new(vec![tokenstream::TreeAndSpacing::from(
                tokenstream::TokenTree::Delimited(
                    sp.clone(),
                    match delim {
                        MacDelimiter::Parenthesis => Delimiter::Parenthesis,
                        MacDelimiter::Brace => Delimiter::Brace,
                        MacDelimiter::Bracket => Delimiter::Bracket,
                    },
                    stream.clone(),
                ),
            )]);
            let mut p = dict(
                nom::combinator::map_res(one_token(), |t| match t.ident() {
                    Some((rustc_span::symbol::Ident { name, .. }, _))
                        if crate::SINK_ANN_SYMS.contains(&name) =>
                    {
                        Ok(name)
                    }
                    _ => Result::Err(()),
                }),
                delimited(
                    nom::multi::separated_list0(assert_token(TokenKind::Comma), integer()),
                    Delimiter::Bracket,
                ),
            );
            p(I::from_stream(&s))
                .unwrap_or_else(|_| panic!("parser failed"))
                .1
                .into_iter()
                .collect::<HashMap<_, _>>()
        }
        _ => panic!("Incorrect annotation {ann:?}"),
    };
    SinkAnnotationPayload {
        leaks: m.remove(&crate::LEAKS_SYM).expect("leaks not found"),
        scopes: m.remove(&crate::SCOPED_SYM).expect("scoped not found"),
    }
}
