extern crate quote;

use proc_macro::TokenStream;
use quote::quote;

macro_rules! export {
    ($name:ident) => {
        #[proc_macro_attribute]
        pub fn $name(attr: TokenStream, item: TokenStream) -> TokenStream {
            impl_::$name(attr, item)
        }
    };
}

export!(marker);
export!(output_types);
export!(analyze);

#[cfg(not(paralegal))]
mod impl_ {
    use super::{quote, TokenStream};

    macro_rules! pass {
        ($name:ident $(,)?) => {
            pass!($name, true);
        };
        ($name:ident, $takes_args:expr $(,)?) => {
            pub fn $name(attr: TokenStream, it: TokenStream) -> TokenStream {
                if $takes_args || attr.is_empty() {
                    it
                } else {
                    let mut out: TokenStream = quote!(
                        compile_error!("The `paralegal::{}` attribute does not take arguments", stringify!($name));
                    ).into();
                    // Reemit item so any compile errors on it are also reported
                    out.extend(it);
                    out
                }
            }
        };
    }

    pass!(marker);
    pass!(output_types);
    pass!(analyze, false);
}

#[cfg(paralegal)]
mod impl_ {
    use super::{quote, TokenStream};
    use proc_macro2::TokenStream as TokenStream2;
    use proc_macro2::{Ident, Span};

    macro_rules! tool_attr {
        ($name:ident $(,)?) => {
            tool_attr!($name, true);
        };
        ($name:ident, $takes_args:expr $(,)?) => {
            #[allow(dead_code)]
            pub fn $name(attr: TokenStream, item: TokenStream) -> TokenStream {
                let attr = TokenStream2::from(attr);
                let name = Ident::new(stringify!($name), Span::mixed_site());
                let mut out: TokenStream = if $takes_args {
                    quote!(
                        #[paralegal_flow::#name(#attr)]
                    )
                } else if !attr.is_empty() {
                    quote!(
                        compile_error!("The `paralegal::{}` attribute does not take any arguments", stringify!($name));
                    )
                } else {
                    quote!(
                        #[paralegal_flow::#name]
                    )
                }
                .into();

                out.extend(item);
                out
            }
        };
    }

    tool_attr!(marker);
    tool_attr!(analyze, false);
    tool_attr!(output_types);
}
