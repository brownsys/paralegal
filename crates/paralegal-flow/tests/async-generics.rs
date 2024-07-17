use paralegal_flow::test_utils::InlineTestBuilder;

#[test]
fn await_on_generic() {
    InlineTestBuilder::new(stringify!(
        use std::{
            future::{Future},
            task::{Context, Poll},
            pin::Pin
        };
        struct AFuture;

        impl Future for AFuture {
            type Output = usize;
            fn poll(self: Pin<&mut Self>, ctx: &mut Context<'_>) -> Poll<Self::Output> {
                unimplemented!()
            }
        }

        trait Trait {
            fn method(&mut self) -> AFuture;
        }

        async fn main<T: Trait>(mut t: T) -> usize {
            t.method().await
        }
    ))
    .check(|_ctrl| {})
}

#[test]
fn await_with_inner_generic() {
    InlineTestBuilder::new(stringify!(
        use std::{
            future::{Future},
            task::{Context, Poll},
            pin::Pin,
        };
        struct AFuture<'a, T: ?Sized>(&'a mut T);

        impl<'a, T> Future for AFuture<'a, T> {
            type Output = usize;
            fn poll(self: Pin<&mut Self>, ctx: &mut Context<'_>) -> Poll<Self::Output> {
                unimplemented!()
            }
        }

        trait Trait {
            fn method(&mut self) -> AFuture<'_, Self> {
                AFuture(self)
            }
        }

        async fn main<T: Trait>(mut t: T) -> usize {
            t.method().await
        }
    ))
    .check(|_ctrl| {})
}

#[test]
fn await_with_inner_generic_constrained() {
    InlineTestBuilder::new(stringify!(
        use std::{
            future::{Future},
            task::{Context, Poll},
            pin::Pin,
        };
        struct AFuture<'a, T: ?Sized>(&'a mut T);

        impl<'a, T: Trait + Unpin + ?Sized> Future for AFuture<'a, T> {
            type Output = usize;
            fn poll(self: Pin<&mut Self>, ctx: &mut Context<'_>) -> Poll<Self::Output> {
                unimplemented!()
            }
        }

        trait Trait: Send + Unpin + 'static {
            fn method(&mut self) -> AFuture<'_, Self>
            where
                Self: Unpin + Sized,
            {
                AFuture(self)
            }
        }

        async fn main<T: Trait>(mut t: T) -> usize {
            t.method().await
        }
    ))
    .check(|_ctrl| {})
}
