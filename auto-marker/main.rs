#![feature(let_chains, rustc_private)]
extern crate clap;
extern crate dfpp;
extern crate regex;
extern crate syn;
extern crate toml;
#[macro_use]
extern crate lazy_static;

use dfpp::desc::{MarkerAnnotation, MarkerRefinement};
use regex::Regex;
use std::io;
use std::path::Path;
use syn::{visit::Visit, Ident, ItemImpl, Signature, Type};

type Identifier = String;

lazy_static! {
    static ref USER_DATA_REGEX: Regex = Regex::new(r"(?i)\buser\b").unwrap();
    static ref IO_FN_NAME_REGEX: Regex = Regex::new(r"(?i)\bwrite\b").unwrap();
    static ref DATABASE_REGEX: Regex =
        Regex::new(r"(?i)\b(DB|Database|Connection|Conn)\b").unwrap();
    static ref DB_METHOD_REGEX: Regex = Regex::new(r"(?i)\b(insert|delete)\b").unwrap();
}

struct Collector {
    markers: dfpp::marker_db::RawExternalMarkers,
    // Context
    crate_name: Identifier,
    mod_stack: Vec<Identifier>,
    maybe_impl: Option<ItemImpl>,
}

impl Collector {
    fn new(crate_name: Identifier) -> Self {
        Self {
            crate_name,
            markers: Default::default(),
            mod_stack: vec![],
            maybe_impl: None,
        }
    }

    fn simple_self_ty(&self) -> Option<&Ident> {
        match self.maybe_impl.as_ref()?.self_ty.as_ref() {
            Type::Path(pt) => pt.path.get_ident(),
            _ => None,
        }
    }

    fn mark_local_item(&mut self, name: &Ident, marker: &str) {
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
        self.markers
            .entry(name)
            .or_default()
            .push(MarkerAnnotation {
                marker: dfpp::Symbol::intern(marker),
                refinement: MarkerRefinement::empty(),
            })
    }

    fn all_functions_check(&mut self, sig: &Signature) {
        if IO_FN_NAME_REGEX.is_match(&sig.ident.to_string()) {
            self.mark_local_item(&sig.ident, "io")
        }
    }

    fn traverse_directory(&mut self, path: &Path) -> io::Result<()> {
        for dir in path.read_dir()? {
            let mod_stack_depth = self.mod_stack.len();
            let dir = dir?;
            let file_type = dir.file_type()?;
            if file_type.is_file() {
                let do_traverse = if dir.file_name() != "mod.rs" {
                    true
                } else if let Some((name, ext)) = dir.file_name().to_str().unwrap().split_once(".") 
                    && ext == "rs"
                {
                    self.mod_stack.push(name.to_string());
                    true
                } else {
                    false
                };

                if do_traverse {
                    let content = std::fs::read_to_string(dir.path())?;
                    let ast = syn::parse_file(&content).unwrap();
                    self.visit_file(&ast);
                }
            } else if file_type.is_dir() {
                self.mod_stack
                    .push(dir.file_name().to_str().unwrap().to_string())
            }

            let new_stack_len = self.mod_stack.len();
            if new_stack_len == mod_stack_depth + 1 {
                // we must have pushed onto the stack before, restore the old one now.
                self.mod_stack.pop();
            } else if new_stack_len == mod_stack_depth {
                // we didn't push onto the stack (either the directory name wasn't parseable or we saw mod.rs) so we do nothing.
            } else {
                unreachable!("Invariant broken, mod stack depth old: {mod_stack_depth}, new: {new_stack_len}")
            }
        }
        Ok(())
    }
}

impl<'ast> Visit<'ast> for Collector {
    fn visit_item_struct(&mut self, i: &'ast syn::ItemStruct) {
        if USER_DATA_REGEX.is_match(&i.ident.to_string()) {
            self.mark_local_item(&i.ident, "user_data")
        }
        syn::visit::visit_item_struct(self, i)
    }

    fn visit_item_enum(&mut self, i: &'ast syn::ItemEnum) {
        if USER_DATA_REGEX.is_match(&i.ident.to_string()) {
            self.mark_local_item(&i.ident, "user_data")
        }
        syn::visit::visit_item_enum(self, i)
    }

    fn visit_impl_item_fn(&mut self, i: &'ast syn::ImplItemFn) {
        let impl_target_contains_database = self
            .simple_self_ty()
            .map_or(false, |id| DATABASE_REGEX.is_match(&id.to_string()));
        if impl_target_contains_database && DB_METHOD_REGEX.is_match(&i.sig.ident.to_string()) {
            // attach to argument instead
            self.mark_local_item(&i.sig.ident, "io")
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
        self.mod_stack.push(i.ident.to_string());
        syn::visit::visit_item_mod(self, i);
        assert_eq!(self.mod_stack.pop(), Some(i.ident.to_string()));
    }
}

fn check_crate() -> io::Result<()> {
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
    write!(outfile, "{}", outstr)
}

fn main() {
    // TODO:
    //  - Mark std::io::Write impls
    //  - Transform matches on trait impls by duplicating the function and
    //    decorating the inner one.

    check_crate().unwrap()
}
