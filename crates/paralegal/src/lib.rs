//! The paralegal annotation library.
//!
//! For the comprehensive documentation see
//! <https://justus-adam.notion.site/Markers-and-Annotations-b3b078ea2f7f41739de1efe7f9d33484?pvs=4>
//!
//! Note that these proc macros expand differently depending on whether this
//! library is compiled as part of paralegal analysis. As such you may encounter
//! some compile errors at the use-site only when running `cargo
//! paralegal-flow`.
#![deny(missing_docs)]

extern crate quote;

use proc_macro::TokenStream;

/// Re-export the named item from the `impl_` mod as a proc-macro.
///
/// Allows documentation to be added to the name (from
/// <https://amanjeev.com/blog/rust-document-macro-invocations/>)
macro_rules! export {
    ($(#[$meta:meta])* $name:ident) => {
        $(#[$meta])*
        #[proc_macro_attribute]
        pub fn $name(attr: TokenStream, item: TokenStream) -> TokenStream {
            impl_::$name(attr, item)
        }
    };
}

export!(
    /// Attach an annotation to this item.
    ///
    /// For more information see
    /// <https://justus-adam.notion.site/Markers-and-Annotations-b3b078ea2f7f41739de1efe7f9d33484?pvs=4#2d84ac8a378c4b53a56be8e402c68a32>
    ///
    /// ### Example
    ///
    /// Can be applied to types
    ///
    /// ```
    /// #[paralegal::marker(sensitive)]
    /// struct User {}
    /// ```
    ///
    /// Or to functions, their arguments and return values.
    ///
    /// ```
    /// #[paralegal::marker(receiving, arguments = [0], return)]
    /// #[paralegal::marker(leaking, arguments = [1])]
    /// fn send(recipients: &[String], content: &str) { .. }
    /// ```
    marker
);
export!(
    /// Declare an analysis-level type alias
    ///
    /// See
    /// <https://justus-adam.notion.site/Markers-and-Annotations-b3b078ea2f7f41739de1efe7f9d33484?pvs=4#9d98b6c941d14633b06ac2b4a5c9cc66>
    ///
    /// ### Example
    ///
    /// ```
    /// #[paralegal::output_type(Address)]
    /// struct Email {}
    /// ```
    output_types
);
export!(
    /// Mark this function as entry point for analysis.
    ///
    /// See also
    /// <https://justus-adam.notion.site/Markers-and-Annotations-b3b078ea2f7f41739de1efe7f9d33484?pvs=4#9a99ae10f3e047d4a3bc97364c3d253e>
    analyze
);

#[cfg(not(paralegal))]
mod impl_ {
    use super::TokenStream;

    /// A no-op implementation for a proc-macro.
    macro_rules! pass {
        ($name:ident) => {
            pub fn $name(_: TokenStream, it: TokenStream) -> TokenStream {
                it
            }
        };
    }

    pass!(marker);
    pass!(output_types);
    pass!(analyze);
}

#[cfg(paralegal)]
mod impl_ {
    use super::{quote, TokenStream};
    use proc_macro2::TokenStream as TokenStream2;
    use proc_macro2::{Ident, Span};
    use quote::quote;

    /// Generate a proc-macro function `name` that emits a `paralegal_flow`
    /// version of `name`.
    macro_rules! tool_attr {
        ($name:ident $(,)?) => {
            tool_attr!($name, true);
        };
        ($name:ident, $takes_args:expr $(,)?) => {
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
