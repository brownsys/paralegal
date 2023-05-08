#![feature(rustc_private)]
use std::fmt::Display;

use clap::Parser;

use dfpp::{HashMap,ir::global_location::*, ana::inline::{add_weighted_edge, Edge}, utils::{Print, write_sep}};

#[derive(Parser)]
struct Args {
    file: std::path::PathBuf,
}

fn main() {
    let args = Args::parse();

    let (flow, _) = dfpp::dbg::read_non_transitive_graph_and_body(std::fs::File::open(&args.file).unwrap());

    let arena = dfpp::rust::rustc_arena::TypedArena::default();
    let interner = GlobalLocationInterner::new(&arena);
    let gli = GLI::new(&interner);
    let ref mut graph = petgraph::graphmap::GraphMap::<_, _, petgraph::Directed>::new();
    let mut gloc_translation_map = HashMap::<String, GlobalLocation>::new();
    for (to_raw, deps) in flow.location_dependencies.iter() {
        let to = gli.from_vec(to_raw.as_slice().to_vec());
        gloc_translation_map.insert(
            format!("{to}"),
            to
        );
        for (i, deps) in deps.input_deps.iter().enumerate() {
            let mut weight = Edge::empty();
            weight.add_type(dfpp::ana::inline::EdgeType::Data(i as u32));
            for from_raw in deps {
                let from = gli.from_vec(from_raw.as_slice().to_vec());
                add_weighted_edge(graph, from, to, weight);
            }
        }
    }

    let mut buf = String::new();
    let stdin = std::io::stdin();
    while let Ok(_) = stdin.read_line(&mut buf) {
        let mut words = buf.split_ascii_whitespace();

        if let None = words.next().and_then(|cmd| {
            match cmd {
                "paths" => {
                    let from = *gloc_translation_map.get(words.next()?)?;
                    let to = *gloc_translation_map.get(words.next()?)?;
                    for path in petgraph::algo::all_simple_paths::<Vec<_>, _>(&*graph, from, to, 0, None) {
                        println!("{}", Print(|fmt| {
                            write_sep(fmt, " -> ", &path, |node, fmt| {
                                node.fmt(fmt)
                            })
                        }));
                    }
                    Some(())
                }
                _ => None,
            }
        }) {
            println!("There was an error")
        }
    }
}