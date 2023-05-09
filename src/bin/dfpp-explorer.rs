#![feature(rustc_private)]

extern crate dialoguer as dl;
extern crate indicatif as ind;
extern crate ringbuffer;
use std::fmt::Display;

use clap::Parser;

use dfpp::{
    ana::inline::{add_weighted_edge, Edge, EdgeType},
    ir::global_location::*,
    utils::{write_sep, Print},
    Either, HashMap,
};
use ringbuffer::RingBufferWrite;

#[derive(Parser)]
struct Args {
    file: std::path::PathBuf,
}

#[derive(Clone, Copy)]
enum Direction {
    In,
    Out,
    Both,
}

impl Direction {
    fn wants_in(self) -> bool {
        matches!(self, Direction::Both | Direction::In)
    }
    fn wants_out(self) -> bool {
        matches!(self, Direction::Both | Direction::In)
    }
}

impl std::fmt::Display for Direction {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Direction::In => write!(f, "in"),
            Direction::Out => write!(f, "out"),
            Direction::Both => write!(f, "both"),
        }
    }
}

#[derive(Clone, Copy)]
enum PathType {
    Data,
    Control,
    Both,
}

impl std::fmt::Display for PathType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use PathType::*;
        match self {
            Data => f.write_str("data"),
            Control => f.write_str("control"),
            Both => f.write_str("all")
        }
    }
}

#[derive(Clone, Copy)]
enum PathMetric {
    MinCtrl,
    None
}

impl std::fmt::Display for PathMetric {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PathMetric::MinCtrl => f.write_str("min-ctrl"),
            PathMetric::None => f.write_str("no"),
        }
    }
}

#[derive(Clone)]
enum Command {
    Paths(PathType, String, String, PathMetric),
    Reachable(PathType, String, String),
    Edges(String, Direction),
    Alias(String, String),
    Size,
}

impl std::fmt::Display for Command {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Command::Paths(t, from, to, metric) => {
                write!(
                    f,
                    "{t}-paths {from} {to}",
                )?;
                if !matches!(metric, PathMetric::None) {
                    write!(f, " {metric}")?;
                }
                Ok(())
            }   
            Command::Edges(from, dir) => write!(f, "edges {from} {dir}"),
            Command::Alias(from, to) => write!(f, "alias {from} {to}"),
            Command::Size => write!(f, "size"),
            Command::Reachable(tp, from, to) => write!(f, "{tp}-reachable {from} {to}"),
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
    NoNodeProvided,
    UnknownDirection(String),
    NoAliasName,
    UnknownPathMetric(String),
    UnknownPathType(String),
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
            NoNodeProvided => write!(f, "No node provided"),
            UnknownDirection(dir) => write!(f, "Unknown direction '{dir}'"),
            NoAliasName => write!(f, "No alias name provided"),
            UnknownPathMetric(m) => write!(f, "Unknown path metric '{m}'"),
            UnknownPathType(ty) => write!(f, "Unknown path type '{ty}'"),
        }
    }
}

fn parse_path_type(s: &str) -> Result<PathType, ReadCommandErr> {
    match s {
        "data" => Ok(PathType::Data),
        "control" => Ok(PathType::Control),
        "all" => Ok(PathType::Both),
        other => Err(ReadCommandErr::UnknownPathType(other.to_string())),
    }
}

fn make_reachable_command<'a, I: Iterator<Item=&'a str>>(tp: Option<&str>, mut split: I) -> Result<Command, ReadCommandErr> {
    let t = tp.map_or(Ok(PathType::Both), parse_path_type)?;
    let from = split.next().ok_or(ReadCommandErr::NoFromPath)?;
    let to = split.next().ok_or(ReadCommandErr::NoToPath)?;
    Ok(Command::Reachable(t, from.to_string(), to.to_string()))
}

fn make_paths_command<'a, I: Iterator<Item=&'a str>>(tp: Option<&str>, mut split: I) -> Result<Command, ReadCommandErr> {
    let t = tp.map_or(Ok(PathType::Both), parse_path_type)?;
    let from = split.next().ok_or(ReadCommandErr::NoFromPath)?;
    let to = split.next().ok_or(ReadCommandErr::NoToPath)?;
    let metric = split.next().map_or(Ok(PathMetric::None), |m| match m {
        "min-ctrl" => Ok(PathMetric::MinCtrl),
        other => Err(ReadCommandErr::UnknownPathMetric(other.to_string()))
    })?;
    Ok(Command::Paths(t, from.to_string(), to.to_string(), metric))
}

impl std::str::FromStr for Command {
    type Err = ReadCommandErr;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut split = s.split_ascii_whitespace();
        let cmdstr = split.next().ok_or(ReadCommandErr::NoCommand)?;
        let dehyphenated = cmdstr.split('-').collect::<Vec<_>>();
        let cmd = match dehyphenated.as_slice() {
            [tp, "paths"] => make_paths_command(Some(tp), &mut split),
            ["paths"] => make_paths_command(None, &mut split),
            [tp, "reachable"] => make_reachable_command(Some(tp), &mut split),
            ["reachable"] => make_reachable_command(None, &mut split),
            ["edges"] => {
                let node = split.next().ok_or(ReadCommandErr::NoNodeProvided)?;
                let dir = split.next().map_or(Ok(Direction::Out), |s| match s {
                    "in" => Ok(Direction::In),
                    "out" => Ok(Direction::Out),
                    "both" | "inout" => Ok(Direction::Both),
                    other => Err(ReadCommandErr::UnknownDirection(other.to_string())),
                })?;
                Ok(Command::Edges(node.to_string(), dir))
            }
            ["alias"] => {
                let name = split.next().ok_or(ReadCommandErr::NoAliasName)?;
                let node = split.next().ok_or(ReadCommandErr::NoNodeProvided)?;
                Ok(Command::Alias(name.to_string(), node.to_string()))
            }
            ["size"] => Ok(Command::Size),
            other => Err(ReadCommandErr::UnknownCommand(cmdstr.to_string())),
        }?;
        if split.next().is_some() {
            return Err(ReadCommandErr::TooManyArgs(2, s.to_string()));
        }
        Ok(cmd)
    }
}

enum RunCommandErr<'g> {
    NodeNotFound(String),
    Unimplemented(&'static str),
    EdgeWeightMissing(GlobalLocation<'g>, GlobalLocation<'g>),
    NonsensicalPathMetric(PathType, PathMetric),
    IOError(std::io::Error)
}

impl From<std::io::Error> for RunCommandErr<'_> {
    fn from(err: std::io::Error) -> Self {
        RunCommandErr::IOError(err)
    }
}

impl<'g> std::fmt::Display for RunCommandErr<'g> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use RunCommandErr::*;
        match self {
            NodeNotFound(n) => write!(f, "Node '{n}' is not known"),
            Unimplemented(s) => write!(f, "'{s}' functionality is not implemented"),
            EdgeWeightMissing(from, to) => write!(f, "Edge weight {from} -> {to} was unexpectedly missing"),
            NonsensicalPathMetric(path_type, metric) => write!(f, "Metric {metric} makes no sense on path query of type {path_type}"),
            IOError(err) => write!(f, "IO Error: {err}"),
        }
    }
}

type Graph<'g> = petgraph::graphmap::GraphMap<GlobalLocation<'g>, Edge, petgraph::Directed>;

struct Repl<'g> {
    gloc_translation_map: HashMap<String, GlobalLocation<'g>>,
    graph: Graph<'g>,
    prompt_for_missing_nodes: bool,
}

impl<'g> Repl<'g> {
    fn translate_node(&self, name: String) -> Result<GlobalLocation<'g>, RunCommandErr<'g>> {
        self.gloc_translation_map
            .get(&name)
            .ok_or(())
            .or_else(|()|
                if self.prompt_for_missing_nodes {
                    println!("Could not find the node '{name}', did you mean instead: (press 'ESC' to abort)");
                    let mut selection = dl::FuzzySelect::new();
                    let items = self.gloc_translation_map.keys().collect::<Vec<_>>();
                    selection.items(items.as_slice())
                        .with_initial_text(&name);
                    if let Some(idx) = selection.interact_opt()? {
                        Ok(&self.gloc_translation_map[items[idx]])
                    } else {
                        Err(RunCommandErr::NodeNotFound(name))
                    }
                } else {
                    Err(RunCommandErr::NodeNotFound(name))
                })
            .map(|r| *r)
    }

    fn data_graph(&self) -> IgnoreCtrlEdges<'_, 'g> {
        IgnoreCtrlEdges(&self.graph)
    }

    fn run_command(&mut self, command: Command) -> Result<(), RunCommandErr<'g>> {
        match command {
            Command::Reachable(path_type, from, to) => {
                use petgraph::algo::has_path_connecting;
                let from = self.translate_node(from)?;
                let to = self.translate_node(to)?;
                let is_reachable = match path_type {
                    PathType::Both => Ok(has_path_connecting(&self.graph, from, to, None)),
                    PathType::Data => Ok(has_path_connecting(self.data_graph(), from, to, None)),
                    PathType::Control => Err(RunCommandErr::Unimplemented("control-reachable")),
                }?;
                println!("{}", if is_reachable {
                    "Yes"
                } else {
                    "No"
                });
                Ok(())
            }
            Command::Paths(path_type, from, to, metric) => {
                if matches!((path_type, metric), (PathType::Data, PathMetric::MinCtrl)) {
                    return Err(RunCommandErr::NonsensicalPathMetric(path_type, metric))
                }
                let from = self.translate_node(from)?;
                let to = self.translate_node(to)?;
                let paths =
                    match path_type {
                        PathType::Both => Ok(Either::Left(petgraph::algo::all_simple_paths::<
                            Vec<_>,
                            _,
                        >(
                            &self.graph, from, to, 0, None
                        ))),
                        PathType::Data => Ok(Either::Right(petgraph::algo::all_simple_paths::<
                            Vec<_>,
                            _,
                        >(
                            self.data_graph(),
                            from,
                            to,
                            0,
                            None,
                        ))),
                        PathType::Control => Err(RunCommandErr::Unimplemented("control-paths")),
                    }?;

                match metric {
                    PathMetric::MinCtrl => {
                        let mut scanned = 0_u64;
                        let mut min = usize::MAX;
                        let mut min_paths = vec![];
                        let progress = ind::ProgressBar::new(80)
                            .with_style(ind::ProgressStyle::with_template("[{elapsed}] {msg}").unwrap());
                        'next_path: for path in paths {
                            let mut prior = None;
                            let mut len = 0;
                            scanned += 1;
                            if scanned % 10_000 == 0 {
                                progress.set_message(format!("Current state: Scanned {scanned} paths, found {} of length {min}", min_paths.len()));
                            }
                            for to in path.iter().cloned() {
                                if let Some(from) = prior {
                                    let edge = self.graph.edge_weight(from, to).ok_or(RunCommandErr::EdgeWeightMissing(from, to))?;
                                    if !edge.is_data() && edge.is_control() {
                                        len += 1;
                                    }
                                    if len > min {
                                        continue 'next_path;
                                    }
                                }
                                prior = Some(to);
                            }
                            assert!(len <= min);
                            if len < min {
                                min = len;
                                min_paths.clear()
                            }
                            min_paths.push(path);
                            progress.set_message(format!("Current state: Scanned {scanned} paths, found {} of length {min}", min_paths.len()));
                        }                    
                        progress.finish_and_clear();
                        for path in min_paths {
                            println!(
                                "{}",
                                Print(|fmt| { write_sep(fmt, " -> ", &path, |node, fmt| node.fmt(fmt)) })
                            );
                            println!("Extrema for {metric} metric found was {min}")
                        }
                    }
                    PathMetric::None => {
                        for path in paths {
                            println!(
                                "{}",
                                Print(|fmt| { write_sep(fmt, " -> ", &path, |node, fmt| node.fmt(fmt)) })
                            )
                        }
                    }
                }
                Ok(())
            }
            Command::Edges(from, dir) => {
                let node = self.translate_node(from)?;
                let mut num = 0;
                if dir.wants_in() {
                    for (from, _, edge) in self
                        .graph
                        .edges_directed(node, petgraph::Direction::Incoming)
                    {
                        num += 1;
                        println!("in {from} {edge}");
                    }
                }
                if dir.wants_out() {
                    for (_, to, edge) in self
                        .graph
                        .edges_directed(node, petgraph::Direction::Outgoing)
                    {
                        num += 1;
                        println!("out {to} {edge}");
                    }
                }
                println!("Found {num} edges");
                Ok(())
            }
            Command::Alias(name, node) => {
                let node = self.translate_node(node)?;
                if let Some(old) = self.gloc_translation_map.insert(name, node) {
                    println!("Overwrote prior value {old}");
                }
                Ok(())
            }
            Command::Size => {
                println!(
                    "{} nodes, {} edges",
                    self.graph.node_count(),
                    self.graph
                        .all_edges()
                        .map(|(_, _, weight)| weight.count())
                        .sum::<u32>()
                );
                Ok(())
            }
        }
    }
}

#[derive(Clone, Copy)]
struct IgnoreCtrlEdges<'a, 'g>(&'a Graph<'g>);

impl<'a, 'g> petgraph::visit::NodeCount for IgnoreCtrlEdges<'a, 'g> {
    fn node_count(self: &Self) -> usize {
        self.0.node_count()
    }
}

impl<'a, 'g> petgraph::visit::Visitable for IgnoreCtrlEdges<'a, 'g> {
    type Map = <&'a Graph<'g> as petgraph::visit::Visitable>::Map;

    fn visit_map(self: &Self) -> Self::Map {
        self.0.visit_map()
    }

    fn reset_map(self: &Self,map: &mut Self::Map) {
        self.0.reset_map(map)
    }
}

struct NoCtrlNeighbors<'a, 'g> {
    inner: petgraph::graphmap::Edges<
        'a,
        dfpp::ir::GlobalLocation<'g>,
        dfpp::ana::inline::Edge,
        petgraph::Directed,
    >,
    node: GlobalLocation<'g>,
}

impl<'a, 'g> std::iter::Iterator for NoCtrlNeighbors<'a, 'g> {
    type Item = GlobalLocation<'g>;
    fn next(&mut self) -> Option<Self::Item> {
        let (from, to, weight) = self.inner.next()?;
        let mut weight = *weight;
        weight.remove_type(EdgeType::Control);
        (!weight.is_empty())
            .then_some(if from == self.node { to } else { from })
            .or_else(|| self.next())
    }
}

struct NoCtrlNeighborsDirected<'a, 'g> {
    inner: petgraph::graphmap::EdgesDirected<
        'a,
        dfpp::ir::GlobalLocation<'g>,
        dfpp::ana::inline::Edge,
        petgraph::Directed,
    >,
    direction: petgraph::Direction,
}

impl<'a, 'g> std::iter::Iterator for NoCtrlNeighborsDirected<'a, 'g> {
    type Item = GlobalLocation<'g>;
    fn next(&mut self) -> Option<Self::Item> {
        let (from, to, weight) = self.inner.next()?;
        let mut weight = *weight;
        weight.remove_type(EdgeType::Control);
        (!weight.is_empty())
            .then_some(if self.direction == petgraph::Direction::Outgoing {
                to
            } else {
                from
            })
            .or_else(|| self.next())
    }
}

impl<'a, 'g> petgraph::visit::IntoNeighborsDirected for IgnoreCtrlEdges<'a, 'g> {
    type NeighborsDirected = NoCtrlNeighborsDirected<'a, 'g>;
    fn neighbors_directed(
        self,
        n: Self::NodeId,
        d: petgraph::Direction,
    ) -> Self::NeighborsDirected {
        NoCtrlNeighborsDirected {
            inner: self.0.edges_directed(n, d),
            direction: d,
        }
    }
}

impl<'a, 'g> petgraph::visit::GraphBase for IgnoreCtrlEdges<'a, 'g> {
    type EdgeId = <&'a Graph<'g> as petgraph::visit::GraphBase>::EdgeId;
    type NodeId = <&'a Graph<'g> as petgraph::visit::GraphBase>::NodeId;
}

impl<'a, 'g> petgraph::visit::GraphRef for IgnoreCtrlEdges<'a, 'g> {}

impl<'a, 'g> petgraph::visit::IntoNeighbors for IgnoreCtrlEdges<'a, 'g> {
    type Neighbors = NoCtrlNeighbors<'a, 'g>;
    fn neighbors(self, a: Self::NodeId) -> Self::Neighbors {
        NoCtrlNeighbors {
            inner: self.0.edges(a),
            node: a,
        }
    }
}

struct MyHistory<C>(ringbuffer::ConstGenericRingBuffer<C, 256>);

impl <C> std::default::Default for MyHistory<C> {
    fn default() -> Self {
        Self(ringbuffer::ConstGenericRingBuffer::default())
    }
}


impl <C: ToString + Clone> dl::History<C> for MyHistory<C> {
    fn read(&self, pos: usize) -> Option<String> {
        use ringbuffer::RingBufferExt;
        let new_idx = -1 -(pos as isize);
        self.0.get(new_idx).map(|c| c.to_string())
    }
    fn write(&mut self, val: &C) {
        self.0.push(val.clone())
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
            for (weight, deps) in deps
                .input_deps
                .iter()
                .enumerate()
                .map(|(i, deps)| {
                    let mut weight = Edge::empty();
                    weight.add_type(EdgeType::Data(i as u32));
                    (weight, deps)
                })
                .chain([{
                    let mut weight = Edge::empty();
                    weight.add_type(EdgeType::Control);
                    (weight, &deps.ctrl_deps)
                }])
            {
                for from_raw in deps {
                    let from = gli.from_vec(from_raw.as_slice().to_vec());
                    add_weighted_edge(graph, from, to, weight);
                }
            }
        }

        let mut repl = Repl {
            graph: g,
            gloc_translation_map,
            prompt_for_missing_nodes: true,
        };
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
    });
}
