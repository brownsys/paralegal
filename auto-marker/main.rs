//! Applies markers to a crate based on heuristics. Must be run in the
//! directory that contains the `Cargo.toml`, which it uses to extract the crate
//! name.
//!
//! Outputs an `external-annotations.toml` file.
//!
//! The main component here is the [`Collector`], see its documentation for more
//! information.
#![feature(let_chains, rustc_private)]
extern crate anyhow;
extern crate clap;
extern crate dfpp;
extern crate regex;
extern crate syn;
extern crate toml;
#[macro_use]
extern crate lazy_static;

use dfpp::{
    desc::{MarkerAnnotation, MarkerRefinementKind},
    Symbol,
};
use regex::Regex;
use std::path::Path;
use syn::{visit::Visit, Ident, ItemImpl, Signature, Type};

type Identifier = String;

lazy_static! {
    static ref USER_DATA_REGEX: Regex = Regex::new(r"(?i)\buser\b").unwrap();
    static ref IO_FN_NAME_REGEX: Regex = Regex::new(r"(?i)\bwrite\b").unwrap();
    static ref DATABASE_REGEX: Regex =
        Regex::new(r"(?i)\b(DB|Database|Connection|Conn)\b").unwrap();
    static ref DB_METHOD_REGEX: Regex = Regex::new(r"(?i)\b(insert|delete)\b").unwrap();
    static ref USER_DATA_MARKER: Symbol = Symbol::intern("user_data");
    static ref IO_MARKER_NAME: Symbol = Symbol::intern("io");
}

/// Extend a $stack with $elem, then perform $inner, then pop the stack and
/// ensure the original length was restored.
///
/// This is supposed to be used to ensure correct handling of the `mod_stack`
/// context in [`Collector`]
macro_rules! pushed {
    ($stack:expr, $elem:expr, $inner:expr) => {{
        let len = $stack.len();
        $stack.push($elem);
        let result = $inner;
        assert!($stack.pop().is_some());
        assert_eq!($stack.len(), len);
        result
    }};
}

/// Heuristic context and collector of markers. Implemented as a directory tree
/// traversal and a syntax visitor.
///
/// The marker assignment is done with external markers so we don't actually
/// have to perform any changes to the source code. To create external markers
/// we must know the whole path for each item and so we accumulate a stack of
/// `mod`s as context and also a potential `impl` block we might be in. The
/// [`Self::mark_local_item`] function is responsible for using that context to
/// create a full path for the marker. The first context item is the crate name
/// which makes this theoretically suitable for multi-crate setups.
///
/// However if we do decide that source code edits are appropriate we could make
/// this `VisitMut` instead. We could use that to either add the markers inline
/// (less interesting) which allows us to also add markers to trait
/// implementation methods (which currently can't be done via external markers).
struct Collector {
    markers: dfpp::marker_db::RawExternalMarkers,
    // Context
    crate_name: Identifier,
    mod_stack: Vec<Identifier>,
    maybe_impl: Option<ItemImpl>,
}

impl Collector {
    /// Initialize a new collector with an empty context and empty marker
    /// collection.
    fn new(crate_name: Identifier) -> Self {
        Self {
            crate_name,
            markers: Default::default(),
            mod_stack: vec![],
            maybe_impl: None,
        }
    }

    /// If `maybe_impl` is set and it is a simple ident type then return that
    /// ident.
    fn simple_self_ty(&self) -> Option<&Ident> {
        match self.maybe_impl.as_ref()?.self_ty.as_ref() {
            Type::Path(pt) => pt.path.get_ident(),
            _ => None,
        }
    }

    /// Attach the marker to this item in the current context. Uses
    /// `self.mod_stack` and `self.maybe_impl` to construct a complete path to
    /// the item before assigning the marker.
    fn mark_local_item(&mut self, name: &Ident, marker: MarkerAnnotation) {
        let mut full_path = std::iter::once(&self.crate_name)
            .chain(self.mod_stack.iter())
            .cloned()
            .collect::<Vec<_>>();
        if self.maybe_impl.is_some() {
            full_path.push(
                self.simple_self_ty()
                    .expect("Can only mark items in impl blocks for simple types")
                    .to_string(),
            );
        }
        full_path.push(name.to_string());
        let name = full_path.join("::");
        self.markers.entry(name).or_default().push(marker)
    }

    /// Check that should be performed on all `fn`-like items (be they
    /// associated functions or bare functions)
    fn all_functions_check(&mut self, sig: &Signature) {
        if IO_FN_NAME_REGEX.is_match(&sig.ident.to_string()) {
            self.mark_local_item(
                &sig.ident,
                MarkerAnnotation {
                    marker: *IO_MARKER_NAME,
                    refinement: MarkerRefinementKind::Argument(
                        (0..sig.inputs.len() as u32).collect(),
                    )
                    .into(),
                },
            )
        }
    }

    /// Read the contents of the file, parse the code and visit it.
    fn handle_file(&mut self, path: impl AsRef<Path>) -> anyhow::Result<()> {
        let content = std::fs::read_to_string(&path)?;
        let ast = syn::parse_file(&content)?;
        self.visit_file(&ast);
        Ok(())
    }

    /// Check all files in this directory, recursively traversing subdirectories
    /// as `mod`s.
    fn traverse_directory(&mut self, path: impl AsRef<Path>) -> anyhow::Result<()> {
        for dir in path.as_ref().read_dir()? {
            let dir = dir?;
            let file_type = dir.file_type()?;
            if file_type.is_file() {
                if dir.file_name() == "mod.rs" {
                    self.handle_file(dir.path())?
                } else if let Some((name, ext)) = dir.file_name().to_str().unwrap().split_once('.')
                    && ext == "rs"
                {
                    pushed!(self.mod_stack, name.to_string(), {
                        self.handle_file(dir.path())?
                    });
                }
            } else if file_type.is_dir() {
                pushed!(
                    self.mod_stack,
                    dir.file_name().to_str().unwrap().to_string(),
                    { self.traverse_directory(dir.path())? }
                )
            }
        }
        Ok(())
    }
}

impl<'ast> Visit<'ast> for Collector {
    fn visit_item_struct(&mut self, i: &'ast syn::ItemStruct) {
        if USER_DATA_REGEX.is_match(&i.ident.to_string()) {
            self.mark_local_item(
                &i.ident,
                MarkerAnnotation {
                    marker: *USER_DATA_MARKER,
                    refinement: Default::default(),
                },
            )
        }
        syn::visit::visit_item_struct(self, i)
    }

    fn visit_item_enum(&mut self, i: &'ast syn::ItemEnum) {
        if USER_DATA_REGEX.is_match(&i.ident.to_string()) {
            self.mark_local_item(
                &i.ident,
                MarkerAnnotation {
                    marker: *USER_DATA_MARKER,
                    refinement: Default::default(),
                },
            )
        }
        syn::visit::visit_item_enum(self, i)
    }

    fn visit_impl_item_fn(&mut self, i: &'ast syn::ImplItemFn) {
        let impl_target_contains_database = self
            .simple_self_ty()
            .map_or(false, |id| DATABASE_REGEX.is_match(&id.to_string()));
        if impl_target_contains_database && DB_METHOD_REGEX.is_match(&i.sig.ident.to_string()) {
            // attach to argument instead
            self.mark_local_item(
                &i.sig.ident,
                MarkerAnnotation {
                    marker: *IO_MARKER_NAME,
                    refinement: MarkerRefinementKind::Argument([1].into_iter().collect()).into(),
                },
            )
        }
        self.all_functions_check(&i.sig);
        syn::visit::visit_impl_item_fn(self, i)
    }

    fn visit_item_fn(&mut self, i: &'ast syn::ItemFn) {
        self.all_functions_check(&i.sig);
        syn::visit::visit_item_fn(self, i)
    }

    fn visit_item_impl(&mut self, i: &'ast ItemImpl) {
        assert!(self.maybe_impl.replace(i.clone()).is_none());
        syn::visit::visit_item_impl(self, i);
        assert!(self.maybe_impl.take().is_some());
    }

    fn visit_item_mod(&mut self, i: &'ast syn::ItemMod) {
        pushed!(self.mod_stack, i.ident.to_string(), {
            syn::visit::visit_item_mod(self, i)
        });
    }
}

/// Main entry point for the directory traversal. Assumes the current directory
/// is a crate with a `Cargo.toml` file and a `src` directory that contains the
/// rust source code.
fn check_crate() -> anyhow::Result<()> {
    let manifest_file = std::fs::read_to_string("Cargo.toml")?;
    let manifest: toml::Table = toml::from_str(&manifest_file).unwrap();

    let crate_name = manifest
        .get("package")
        .unwrap()
        .as_table()
        .unwrap()
        .get("name")
        .unwrap()
        .as_str()
        .unwrap()
        .to_string();
    let mut coll = Collector::new(crate_name);

    coll.traverse_directory(Path::new("src")).unwrap();

    let outstr = toml::to_string_pretty(&coll.markers).unwrap();
    let mut outfile = std::fs::OpenOptions::new()
        .truncate(true)
        .write(true)
        .open("external-annotations.toml")
        .unwrap();
    use std::io::Write;
    write!(outfile, "{}", outstr)?;
    Ok(())
}

fn main() {
    // TODO:
    //  - Mark std::io::Write impls

    check_crate().unwrap()
}
