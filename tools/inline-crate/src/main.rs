use anyhow::{anyhow, Result};
use clap::Parser;
use proc_macro2::{Span, TokenStream};
use std::{
    ffi::OsStr,
    fs::DirEntry,
    io,
    path::{Path, PathBuf},
};
use syn::{visit_mut::VisitMut, AttrStyle, Ident, Item, Meta, PathArguments, PathSegment};

struct AppendCrate<'a> {
    crate_name: &'a str,
}

impl<'a> AppendCrate<'a> {
    fn new(crate_name: &'a str) -> Self {
        Self { crate_name }
    }
}

impl<'a> VisitMut for AppendCrate<'a> {
    fn visit_path_mut(&mut self, i: &mut syn::Path) {
        if matches!(i.segments.first(), Some(PathSegment { ident, arguments: PathArguments::None }) if ident == self.crate_name)
        {
            i.segments.insert(
                0,
                PathSegment {
                    ident: Ident::new("crate", Span::mixed_site()),
                    arguments: syn::PathArguments::None,
                },
            )
        }
    }

    fn visit_item_mut(&mut self, i: &mut syn::Item) {
        if matches!(i, Item::ExternCrate(ec) if ec.ident == self.crate_name) {
            *i = Item::Verbatim(TokenStream::new());
        }
    }
}

struct TransformSource<'a> {
    crate_name: &'a str,
    is_lib_rs: bool,
}

impl<'a> TransformSource<'a> {
    fn new(crate_name: &'a str) -> Self {
        Self {
            crate_name,
            is_lib_rs: false,
        }
    }
}

impl<'a> VisitMut for TransformSource<'a> {
    fn visit_file_mut(&mut self, i: &mut syn::File) {
        if self.is_lib_rs {
            i.attrs.retain(|att| {
                matches!(att.style, AttrStyle::Inner(_))
                    && matches!(&att.meta, Meta::List(ml)
                    if ml.path.get_ident().map_or(false, |i| i == "feature"))
            })
        }
    }

    fn visit_path_mut(&mut self, i: &mut syn::Path) {
        if matches!(i.segments.first(), Some(PathSegment { ident, arguments: PathArguments::None }) if ident == "crate")
        {
            i.segments.insert(
                1,
                PathSegment {
                    ident: Ident::new(self.crate_name, Span::mixed_site()),
                    arguments: syn::PathArguments::None,
                },
            )
        }
    }
}

#[derive(Debug, Parser)]
struct Arguments {
    source: PathBuf,
    target: PathBuf,
    #[clap(long)]
    skip_existing: bool,
}

struct IterDirTree {
    queue: Vec<Result<DirEntry, io::Error>>,
}

impl Iterator for IterDirTree {
    type Item = Result<PathBuf, io::Error>;

    fn next(&mut self) -> Option<Self::Item> {
        let elem = self.queue.pop()?;
        elem.and_then(|e| {
            let t = e.file_type()?;
            if t.is_dir() {
                self.queue.extend(e.path().read_dir()?);
                self.next().transpose()
            } else {
                Ok(Some(e.path()))
            }
        })
        .transpose()
    }
}

fn iter_dir_tree(path: impl AsRef<Path>) -> Result<IterDirTree, io::Error> {
    Ok(IterDirTree {
        queue: path.as_ref().read_dir()?.collect(),
    })
}

fn transform_file(
    vis: &mut impl VisitMut,
    source: impl AsRef<Path>,
    target: impl AsRef<Path>,
) -> Result<()> {
    use std::io::Write;
    let s = std::fs::read_to_string(source)?;
    let mut ast = syn::parse_file(&s)?;
    vis.visit_file_mut(&mut ast);
    let new_s = prettyplease::unparse(&ast);
    let mut f = std::fs::OpenOptions::new()
        .truncate(true)
        .write(true)
        .create(true)
        .open(target)?;
    write!(f, "{new_s}")?;
    Ok(())
}

fn get_manifest(path: impl AsRef<Path>) -> Result<toml::Table> {
    Ok(toml::from_str(&std::fs::read_to_string(path)?)?)
}

fn main() -> Result<()> {
    let args = Box::leak(Box::new(Arguments::parse())) as &'static Arguments;

    let source_manifest = get_manifest(args.source.join("Cargo.toml"))?;
    let mut target_manifest = get_manifest(args.target.join("Cargo.toml"))?;

    let crate_name = source_manifest
        .get("package")
        .ok_or_else(|| anyhow!("No key 'package'"))?
        .as_table()
        .ok_or_else(|| anyhow!("'package' key is not a table"))?
        .get("name")
        .ok_or_else(|| anyhow!("No key 'name'"))?
        .as_str()
        .ok_or_else(|| anyhow!("'name' is not a string"))?;

    let mut vis = AppendCrate::new(crate_name);

    for entry in iter_dir_tree(args.target.join("src"))? {
        let path = entry?;
        transform_file(&mut vis, &path, &path)?;
    }

    let mut vis = TransformSource::new(crate_name);

    for entry in iter_dir_tree(args.source.join("src"))? {
        let source_path = entry?;
        let mut relative = source_path.strip_prefix(&args.source)?;

        let lrs: &OsStr = "lib.rs".as_ref();

        let is_lib_rs = relative == lrs;
        if is_lib_rs {
            relative = Path::new("mod.rs");
        }

        let target_path = args.target.join(relative);
        if let Some(p) = target_path.parent() {
            std::fs::create_dir_all(p)?;
        }
        if target_path.exists() {
            if args.skip_existing {
                continue;
            } else {
                panic!("{} exists", target_path.display());
            }
        }

        vis.is_lib_rs = is_lib_rs;
        transform_file(&mut vis, &source_path, &target_path)?;
    }

    let target_deps = target_manifest
            .get_mut("dependencies")
            .ok_or_else(|| anyhow!("Target manifest has no 'dependencies' key"))?
            .as_table_mut()
            .ok_or_else(|| anyhow!("Target dependencies are not a table"))?;
    let source_deps = source_manifest
            .get("dependencies")
            .ok_or_else(|| anyhow!("Source manifest has no 'dependencies' key"))?
            .as_table()
            .ok_or_else(|| anyhow!("Source dependencies are not a table"))?;
    for (k, v) in source_deps {
        if !target_deps.contains_key(k) {
            assert!(target_deps.insert(k.clone(), v.clone()).is_none());
        }
    }
    use std::io::Write;
    let mut f = std::fs::OpenOptions::new().truncate(true).write(true).open(args.target.join("Cargo.toml"))?;
    write!(f, "{}", toml::to_string(&target_manifest)?)?;
    // Combine deps

    Ok(())
}
