#![feature(rustc_private)]

extern crate dialoguer as dl;
use std::fmt::Display;

use clap::Parser;

use dfpp::{
    ana::inline::{add_weighted_edge, Edge},
    ir::global_location::*,
    utils::{write_sep, Print},
    HashMap,
};
use generic_array::sequence::Concat;

#[derive(Parser)]
struct Args {
    file: std::path::PathBuf,
}

#[derive(Clone)]
enum Command {
    Paths(String, String),
}

impl std::fmt::Display for Command {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Command::Paths(from, to) => write!(f, "paths {from} {to}"),
        }
    }
}

#[derive(Debug)]
enum ReadCommandErr {
    NoCommand,
    NoFromPath,
    NoToPath,
    TooManyArgs(usize, String),
    UnknownCommand(String),
}

impl std::fmt::Display for ReadCommandErr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use ReadCommandErr::*;
        match self {
            NoCommand => write!(f, "No command word provided"),
            NoFromPath => write!(f, "No 'from' path provided to 'paths' command"),
            NoToPath => write!(f, "No 'to' path provided to 'paths' command"),
            TooManyArgs(num, full) => write!(
                f,
                "too many arguments provided, expected {num}. Full command {full}"
            ),
            UnknownCommand(cmd) => write!(f, "Unknown command word '{cmd}'"),
        }
    }
}

impl std::str::FromStr for Command {
    type Err = ReadCommandErr;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut split = s.split_ascii_whitespace();
        match split.next().ok_or(ReadCommandErr::NoCommand)? {
            "paths" => {
                let from = split.next().ok_or(ReadCommandErr::NoFromPath)?;
                let to = split.next().ok_or(ReadCommandErr::NoToPath)?;
                if split.next().is_some() {
                    return Err(ReadCommandErr::TooManyArgs(2, s.to_string()));
                }
                Ok(Command::Paths(from.to_string(), to.to_string()))
            }
            other => Err(ReadCommandErr::UnknownCommand(other.to_string())),
        }
    }
}

struct Repl<'g> {
    gli: GLI<'g>,
    gloc_translation_map: HashMap<String, GlobalLocation<'g>>,
    graph: petgraph::graphmap::GraphMap<GlobalLocation<'g>, Edge, petgraph::Directed>,
}

impl<'g> Repl<'g> {
    fn run_command(&self, command: Command) -> Option<()> {
        match command {
            Command::Paths(from, to) => {
                let from = *self.gloc_translation_map.get(&from)?;
                let to = *self.gloc_translation_map.get(&to)?;
                for path in
                    petgraph::algo::all_simple_paths::<Vec<_>, _>(&self.graph, from, to, 0, None)
                {
                    println!(
                        "{}",
                        Print(|fmt| {
                            write_sep(fmt, " -> ", &path, |node, fmt| node.fmt(fmt))
                        })
                    );
                }
                Some(())
            }
        }
    }
}

fn main() {
    let args = Args::parse();

    dfpp::rust::rustc_span::create_default_session_if_not_set_then(|_| {
        let (flow, _) =
            dfpp::dbg::read_non_transitive_graph_and_body(std::fs::File::open(&args.file).unwrap());

        let arena = dfpp::rust::rustc_arena::TypedArena::default();
        let interner = GlobalLocationInterner::new(&arena);
        let gli = GLI::new(&interner);
        let mut g = petgraph::graphmap::GraphMap::<_, _, petgraph::Directed>::new();
        let graph = &mut g;
        let mut gloc_translation_map = HashMap::<String, GlobalLocation>::new();
        for (to_raw, deps) in flow.location_dependencies.iter() {
            let to = gli.from_vec(to_raw.as_slice().to_vec());
            gloc_translation_map.insert(format!("{to}"), to);
            for (i, deps) in deps.input_deps.iter().enumerate() {
                let mut weight = Edge::empty();
                weight.add_type(dfpp::ana::inline::EdgeType::Data(i as u32));
                for from_raw in deps {
                    let from = gli.from_vec(from_raw.as_slice().to_vec());
                    add_weighted_edge(graph, from, to, weight);
                }
            }
        }

        let repl = Repl {
            graph: g,
            gli,
            gloc_translation_map,
        };

        let mut prompt = dl::Input::new();
        prompt.with_prompt("> ");
        loop {
            match prompt.interact_text() {
                Ok(cmd) => {
                    if let Some(()) = repl.run_command(cmd) {
                    } else {
                        println!("There was an error")
                    }
                }
                Err(e) => println!("Error {}", e),
            }
        }
    });
}
