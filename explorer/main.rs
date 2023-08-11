//! CLI interface, history and setup code for the explorer
#![feature(rustc_private)]
#![feature(never_type)]

extern crate dialoguer as dl;
extern crate indicatif as ind;
extern crate ringbuffer;
extern crate serde_lexpr as sexpr;

use clap::Parser;

use dfpp::{ir::global_location::*, serializers::Bodies, Either, HashMap};
use ringbuffer::RingBufferWrite;

mod command;
mod graph;
mod run;

use command::*;
use graph::*;

/// Command line arguments for the explorer.
#[derive(Parser)]
struct Args {
    file: Option<std::path::PathBuf>,
    #[clap(long)]
    script: Option<std::path::PathBuf>,
    #[clap(last = true)]
    command: Vec<String>,
}

/// State of the read-eval-print loop
struct Repl<'g> {
    gloc_translation_map: Option<HashMap<NodeName, Node<'g>>>,
    graph: Option<Graph<'g>>,
    prompt_for_missing_nodes: bool,
    bodies: Option<Bodies>,
    gli: GLI<'g>,
}

impl<'g> Repl<'g> {
    fn empty(gli: GLI<'g>) -> Self {
        Self {
            gli,
            gloc_translation_map: None,
            graph: None,
            bodies: None,
            prompt_for_missing_nodes: true,
        }
    }
}

/// history of commands previously run in the explorer
struct MyHistory<C>(ringbuffer::ConstGenericRingBuffer<C, 256>);

impl<C> std::default::Default for MyHistory<C> {
    fn default() -> Self {
        Self(ringbuffer::ConstGenericRingBuffer::default())
    }
}

impl<C: ToString + Clone> dl::History<C> for MyHistory<C> {
    fn read(&self, pos: usize) -> Option<String> {
        use ringbuffer::RingBufferExt;
        let new_idx = -1 - (pos as isize);
        self.0.get(new_idx).map(|c| c.to_string())
    }
    fn write(&mut self, val: &C) {
        self.0.push(val.clone())
    }
}

fn main() {
    let args = Args::parse();

    dfpp::rust::rustc_span::create_default_session_if_not_set_then(|_| {
        let arena = dfpp::rust::rustc_arena::TypedArena::default();
        let interner = GlobalLocationInterner::new(&arena);
        let gli = GLI::new(&interner);
        let mut repl = Repl::empty(gli);

        if let Some(file) = args.file.as_ref() {
            repl.load_graph(file.as_path()).unwrap();
        }

        if let Some(script) = {
            (!args.command.is_empty())
                .then(|| Either::Right([args.command.join(" ")].into_iter()))
                .or_else(|| {
                    args.script.map(|script| {
                        let file = std::fs::File::open(script).unwrap();
                        use std::io::{BufRead, BufReader};
                        Either::Left(BufReader::new(file).lines().map(Result::unwrap))
                    })
                })
        } {
            repl.prompt_for_missing_nodes = false;
            for l in script {
                repl.run_command(l.parse().unwrap())
                    .unwrap_or_else(|err| panic!("{err}"))
            }
        } else {
            let mut history = MyHistory::<Command>::default();
            let mut prompt = dl::Input::new();
            prompt.history_with(&mut history);
            prompt.with_prompt("query");
            loop {
                match prompt.interact_text() {
                    Ok(cmd) => {
                        if let Err(e) = repl.run_command(cmd) {
                            println!("{e}")
                        }
                    }
                    Err(e) => println!("Error {}", e),
                }
            }
        }
    });
}
