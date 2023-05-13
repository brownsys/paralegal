#![feature(rustc_private)]

extern crate dialoguer as dl;
extern crate indicatif as ind;
extern crate ringbuffer;
use std::fmt::Display;

use clap::Parser;

use dfpp::{
    ana::inline::{add_weighted_edge, Edge, EdgeType},
    ir::{global_location::*, CallOnlyFlow},
    utils::{outfile_pls, write_sep, Print},
    Either, HashMap,
};
use ringbuffer::RingBufferWrite;

#[derive(Parser)]
struct Args {
    file: std::path::PathBuf,
    #[clap(long)]
    script: Option<std::path::PathBuf>,
    #[clap(last = true)]
    command: Vec<String>,
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
        matches!(self, Direction::Both | Direction::Out)
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
            Both => f.write_str("all"),
        }
    }
}

#[derive(Clone, Copy)]
enum PathMetric {
    MinCtrl,
    None,
    Shortest,
}

impl std::fmt::Display for PathMetric {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            PathMetric::MinCtrl => "min-ctrl",
            PathMetric::None => "no",
            PathMetric::Shortest => "shortest",
        })
    }
}

#[derive(Eq, Ord, PartialEq, PartialOrd, Clone, Debug, Hash)]
struct NodeName(String);

impl From<String> for NodeName {
    fn from(s: String) -> Self {
        Self(s)
    }
}

impl From<&'_ str> for NodeName {
    fn from(s: &'_ str) -> Self {
        Self(s.to_string())
    }
}

impl From<&'_ NodeName> for String {
    fn from(n: &'_ NodeName) -> Self {
        n.0.clone()
    }
}

impl std::fmt::Display for NodeName {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.0.as_str())
    }
}

#[derive(Clone, Copy)]
enum GraphOutputFormat {
    Pdf,
    Graphviz,
}

impl std::str::FromStr for GraphOutputFormat {
    type Err = ();
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "pdf" => Ok(GraphOutputFormat::Pdf),
            "gv" | "dot" | "graphviz" => Ok(GraphOutputFormat::Graphviz),
            _ => Err(()),
        }
    }
}

#[derive(Clone)]
enum Command {
    Paths(PathType, NodeName, NodeName, PathMetric),
    Reachable(PathType, NodeName, NodeName),
    Edges(NodeName, Direction),
    Alias(NodeName, NodeName),
    DotSubgraph {
        from: NodeName,
        depth: usize,
        output: std::path::PathBuf,
        format: GraphOutputFormat,
        direction: Direction,
    },
    Size,
}

impl std::fmt::Display for Command {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Command::Paths(t, from, to, metric) => {
                write!(f, "{t}-paths {from} {to}",)?;
                if !matches!(metric, PathMetric::None) {
                    write!(f, " {metric}")?;
                }
                Ok(())
            }
            Command::Edges(from, dir) => write!(f, "edges {from} {dir}"),
            Command::Alias(from, to) => write!(f, "alias {from} {to}"),
            Command::Size => write!(f, "size"),
            Command::Reachable(tp, from, to) => write!(f, "{tp}-reachable {from} {to}"),
            Command::DotSubgraph {
                from,
                depth,
                output,
                direction,
                ..
            } => write!(
                f,
                "dot-subgraph {from} {depth} {} {direction}",
                output.display()
            ),
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
    NoDepth,
    ParseIntErr(std::num::ParseIntError),
    NoOutputFile,
    UnknownGraphOutputFormat(String),
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
            NoDepth => write!(f, "No depth provided"),
            ParseIntErr(er) => write!(f, "{}", er),
            NoOutputFile => write!(f, "No output file provided"),
            UnknownGraphOutputFormat(format) => write!(f, "Unknown graph output format {format}"),
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

fn make_reachable_command<'a, I: Iterator<Item = &'a str>>(
    tp: Option<&str>,
    mut split: I,
) -> Result<Command, ReadCommandErr> {
    let t = tp.map_or(Ok(PathType::Both), parse_path_type)?;
    let from = split.next().ok_or(ReadCommandErr::NoFromPath)?;
    let to = split.next().ok_or(ReadCommandErr::NoToPath)?;
    Ok(Command::Reachable(t, from.into(), to.into()))
}

fn make_paths_command<'a, I: Iterator<Item = &'a str>>(
    tp: Option<&str>,
    mut split: I,
) -> Result<Command, ReadCommandErr> {
    let t = tp.map_or(Ok(PathType::Both), parse_path_type)?;
    let from = split.next().ok_or(ReadCommandErr::NoFromPath)?;
    let to = split.next().ok_or(ReadCommandErr::NoToPath)?;
    let metric = split.next().map_or(Ok(PathMetric::None), |m| match m {
        "min-ctrl" => Ok(PathMetric::MinCtrl),
        "shortest" => Ok(PathMetric::Shortest),
        other => Err(ReadCommandErr::UnknownPathMetric(other.to_string())),
    })?;
    Ok(Command::Paths(t, from.into(), to.into(), metric))
}

impl std::str::FromStr for Direction {
    type Err = ();
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "in" => Ok(Direction::In),
            "out" => Ok(Direction::Out),
            "both" | "inout" => Ok(Direction::Both),
            _ => Err(()),
        }
    }
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
                let dir = split.next().map_or(Ok(Direction::Out), |s| {
                    Direction::from_str(s)
                        .map_err(|()| ReadCommandErr::UnknownDirection(s.to_string()))
                })?;
                Ok(Command::Edges(node.into(), dir))
            }
            ["alias"] => {
                let name = split.next().ok_or(ReadCommandErr::NoAliasName)?;
                let node = split.next().ok_or(ReadCommandErr::NoNodeProvided)?;
                Ok(Command::Alias(name.into(), node.into()))
            }
            ["size"] => Ok(Command::Size),
            ["dot", "subgraph"] => {
                let from = split.next().ok_or(ReadCommandErr::NoFromPath)?.into();
                let depth = split
                    .next()
                    .ok_or(ReadCommandErr::NoDepth)
                    .and_then(|d| usize::from_str(d).map_err(ReadCommandErr::ParseIntErr))?;
                let output: std::path::PathBuf =
                    split.next().ok_or(ReadCommandErr::NoOutputFile)?.into();
                let format = output
                    .extension()
                    .map_or(Ok(GraphOutputFormat::Pdf), |os_str| {
                        let str = os_str.to_str().unwrap();
                        GraphOutputFormat::from_str(str)
                            .map_err(|()| ReadCommandErr::UnknownGraphOutputFormat(str.to_string()))
                    })?;
                let direction = split.next().map_or(Ok(Direction::Out), |s| {
                    Direction::from_str(s)
                        .map_err(|()| ReadCommandErr::UnknownDirection(s.to_string()))
                })?;
                Ok(Command::DotSubgraph {
                    from,
                    depth,
                    output,
                    format,
                    direction,
                })
            }
            _ => Err(ReadCommandErr::UnknownCommand(cmdstr.to_string())),
        }?;
        if split.next().is_some() {
            return Err(ReadCommandErr::TooManyArgs(2, s.to_string()));
        }
        Ok(cmd)
    }
}

enum RunCommandErr<'g> {
    NodeNotFound(NodeName),
    Unimplemented(&'static str),
    EdgeWeightMissing(Node<'g>, Node<'g>),
    NonsensicalPathMetric(PathType, PathMetric),
    IOError(std::io::Error),
    DotError(Option<i32>),
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
            EdgeWeightMissing(from, to) => {
                write!(f, "Edge weight {from} -> {to} was unexpectedly missing")
            }
            NonsensicalPathMetric(path_type, metric) => write!(
                f,
                "Metric {metric} makes no sense on path query of type {path_type}"
            ),
            IOError(err) => write!(f, "IO Error: {err}"),
            DotError(status) => {
                write!(f, "Error running 'dot'")?;
                if let Some(code) = status {
                    write!(f, " {code}")?;
                }
                Ok(())
            }
        }
    }
}

type Graph<'g> = petgraph::graphmap::GraphMap<Node<'g>, Edge, petgraph::Directed>;

struct Repl<'g> {
    gloc_translation_map: HashMap<NodeName, Node<'g>>,
    graph: Graph<'g>,
    prompt_for_missing_nodes: bool,
}

impl<'g> Repl<'g> {
    fn translate_node(&self, name: NodeName) -> Result<Node<'g>, RunCommandErr<'g>> {
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

    fn data_graph(&self) -> IgnoreCtrlEdges<&'_ Graph<'g>> {
        IgnoreCtrlEdges(&self.graph)
    }

    fn create_subgraph(&self, from: Node<'g>, depth: usize, direction: Direction) -> Graph<'g> {
        let mut subg = Graph::new();
        subg.add_node(from);
        let mut queue = vec![(from, depth)];
        while let Some((from, mut depth)) = queue.pop() {
            if depth == 0 {
                continue;
            }
            depth -= 1;
            for (to, weight, is_out) in direction
                .wants_out()
                .then(|| self.graph.edges(from).map(|(_, to, w)| (to, w, true)))
                .into_iter()
                .flatten()
                .chain(
                    direction
                        .wants_in()
                        .then(|| {
                            self.graph
                                .edges_directed(from, petgraph::Direction::Incoming)
                                .map(|(to, _, w)| (to, w, false))
                        })
                        .into_iter()
                        .flatten(),
                )
            {
                if !subg.contains_node(to) {
                    queue.push((to, depth));
                }
                let (from, to) = if is_out { (from, to) } else { (to, from) };
                add_weighted_edge(&mut subg, from, to, *weight);
            }
        }
        subg
    }

    fn run_paths_command(
        &mut self,
        from: Node<'g>,
        to: Node<'g>,
        path_type: PathType,
        metric: PathMetric,
    ) -> Result<(), RunCommandErr<'g>> {
        let paths = match path_type {
            PathType::Both if matches!(metric, PathMetric::Shortest) => Ok(Box::new(
                [{
                    let paths = petgraph::algo::bellman_ford(
                        &WithWeightedEdges {
                            graph: &self.graph,
                            weight: &|_| 1.0,
                        },
                        from,
                    )
                    .unwrap();
                    let mut v = std::iter::successors(Some(to), |to| {
                        paths.predecessors
                            [petgraph::visit::NodeIndexable::to_index(&self.graph, *to)]
                    })
                    .collect::<Vec<_>>();
                    v.reverse();
                    v
                }]
                .into_iter(),
            )
                as Box<dyn Iterator<Item = Vec<Node<'g>>>>),
            PathType::Data if matches!(metric, PathMetric::Shortest) => Ok(Box::new(
                [{
                    let paths = petgraph::algo::bellman_ford(
                        &WithWeightedEdges {
                            graph: &self.data_graph(),
                            weight: &|_| 1.0,
                        },
                        from,
                    )
                    .unwrap();
                    let mut v = std::iter::successors(Some(to), |to| {
                        paths.predecessors
                            [petgraph::visit::NodeIndexable::to_index(&self.graph, *to)]
                    })
                    .collect::<Vec<_>>();
                    v.reverse();
                    v
                }]
                .into_iter(),
            )
                as Box<dyn Iterator<Item = Vec<Node<'g>>>>),
            PathType::Both => Ok(Box::new(petgraph::algo::all_simple_paths::<Vec<_>, _>(
                &self.graph,
                from,
                to,
                0,
                None,
            )) as Box<dyn Iterator<Item = Vec<Node<'g>>>>),
            PathType::Data => Ok(Box::new(petgraph::algo::all_simple_paths::<Vec<_>, _>(
                self.data_graph(),
                from,
                to,
                0,
                None,
            )) as Box<_>),
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
                        progress.set_message(format!(
                            "Current state: Scanned {scanned} paths, found {} of length {min}",
                            min_paths.len()
                        ));
                    }
                    for to in path.iter().cloned() {
                        if let Some(from) = prior {
                            let edge = self
                                .graph
                                .edge_weight(from, to)
                                .ok_or(RunCommandErr::EdgeWeightMissing(from, to))?;
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
                    progress.set_message(format!(
                        "Current state: Scanned {scanned} paths, found {} of length {min}",
                        min_paths.len()
                    ));
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
            PathMetric::None | PathMetric::Shortest => {
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

    fn run_command(&mut self, command: Command) -> Result<(), RunCommandErr<'g>> {
        match command {
            Command::DotSubgraph {
                from,
                depth,
                output,
                format,
                direction,
            } => {
                let from = self.translate_node(from)?;
                let subg = self.create_subgraph(from, depth, direction);
                let gvfile = output.with_extension("gv");
                let mut outf = outfile_pls(&gvfile)?;
                use std::io::Write;
                write!(
                    outf,
                    "{}",
                    petgraph::dot::Dot::with_attr_getters(
                        &subg,
                        &[],
                        &|_, _| "".to_string(),
                        &|_, _| "shape=box".to_string()
                    ),
                )?;
                if matches!(format, GraphOutputFormat::Pdf) {
                    use std::process;
                    let status = process::Command::new("dot")
                        .arg("-Tpdf")
                        .arg(format!("-o{}", output.with_extension("pdf").display()))
                        .arg(format!("{}", gvfile.display()))
                        .status()?;
                    if !status.success() {
                        return Err(RunCommandErr::DotError(status.code()));
                    }
                }
                Ok(())
            }
            Command::Reachable(path_type, from, to) => {
                use petgraph::algo::has_path_connecting;
                let from = self.translate_node(from)?;
                let to = self.translate_node(to)?;
                let is_reachable = match path_type {
                    PathType::Both => Ok(has_path_connecting(&self.graph, from, to, None)),
                    PathType::Data => Ok(has_path_connecting(self.data_graph(), from, to, None)),
                    PathType::Control => Err(RunCommandErr::Unimplemented("control-reachable")),
                }?;
                println!("{}", if is_reachable { "Yes" } else { "No" });
                Ok(())
            }
            Command::Paths(path_type, from, to, metric) => {
                if matches!((path_type, metric), (PathType::Data, PathMetric::MinCtrl)) {
                    return Err(RunCommandErr::NonsensicalPathMetric(path_type, metric));
                }
                let from = self.translate_node(from)?;
                let to = self.translate_node(to)?;
                self.run_paths_command(from, to, path_type, metric)
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

    fn from_flow_graph(flow: &CallOnlyFlow<RawGlobalLocation>, gli: GLI<'g>) -> Self {
        let mut g = petgraph::graphmap::GraphMap::<_, _, petgraph::Directed>::new();
        let graph = &mut g;

        for (to_raw, deps) in flow.location_dependencies.iter() {
            let to = gli.from_vec(to_raw.as_slice().to_vec()).into();
            for (weight, deps) in deps
                .input_deps
                .iter()
                .enumerate()
                .map(|(i, deps)| (Edge::from_types([EdgeType::Data(i as u32)]), deps))
                .chain([(Edge::from_types([EdgeType::Control]), &deps.ctrl_deps)])
            {
                for from_raw in deps {
                    let from = gli.from_vec(from_raw.as_slice().to_vec()).into();
                    add_weighted_edge(graph, from, to, weight);
                }
            }
        }

        for from_raw in &flow.return_dependencies {
            let from = gli.from_vec(from_raw.as_slice().to_vec()).into();
            add_weighted_edge(
                graph,
                from,
                Node::return_(),
                Edge::from_types([EdgeType::Data(0)]),
            );
        }

        let gloc_translation_map: HashMap<NodeName, Node> =
            g.nodes().map(|n| (format!("{n}").into(), n)).collect();
        Self {
            graph: g,
            gloc_translation_map,
            prompt_for_missing_nodes: true,
        }
    }
}

use petgraph::visit::{
    Data, EdgeRef, GraphBase, GraphRef, IntoEdgeReferences, IntoEdges, IntoEdgesDirected,
    IntoNeighbors, IntoNeighborsDirected, IntoNodeIdentifiers, NodeCount, NodeIndexable, Visitable,
};

struct WithWeightedEdges<'f, G: IntoEdgeReferences> {
    graph: G,
    weight: &'f dyn Fn(G::EdgeRef) -> f32,
}

impl<'f, G: Data + IntoEdgeReferences> Data for WithWeightedEdges<'f, G> {
    type NodeWeight = G::NodeWeight;
    type EdgeWeight = f32;
}

#[derive(Clone, Copy)]
struct WeightedEdgeRef<E> {
    original_ref: E,
    weight: f32,
}

impl<E: EdgeRef> EdgeRef for WeightedEdgeRef<E> {
    type EdgeId = E::EdgeId;
    type NodeId = E::NodeId;
    type Weight = f32;
    fn source(&self) -> Self::NodeId {
        self.original_ref.source()
    }
    fn target(&self) -> Self::NodeId {
        self.original_ref.target()
    }
    fn id(&self) -> Self::EdgeId {
        self.original_ref.id()
    }
    fn weight(&self) -> &Self::Weight {
        &self.weight
    }
}

struct WeightedEdgeReferences<'f, E, I> {
    inner: I,
    get_weight: &'f dyn Fn(E) -> f32,
}

impl<'f, E: EdgeRef, I: Iterator<Item = E>> Iterator for WeightedEdgeReferences<'f, E, I> {
    type Item = WeightedEdgeRef<E>;
    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().map(|ef| WeightedEdgeRef {
            original_ref: ef,
            weight: (self.get_weight)(ef),
        })
    }
}

impl<'f, G: IntoEdgeReferences> IntoEdgeReferences for &'_ WithWeightedEdges<'f, G>
where
    G::EdgeReferences: 'f,
    G::NodeId: 'f,
{
    type EdgeRef = WeightedEdgeRef<G::EdgeRef>;
    type EdgeReferences = WeightedEdgeReferences<'f, G::EdgeRef, G::EdgeReferences>;

    fn edge_references(self) -> Self::EdgeReferences {
        WeightedEdgeReferences {
            inner: self.graph.edge_references(),
            get_weight: self.weight,
        }
    }
}

impl<'f, G: IntoEdges> IntoEdges for &'_ WithWeightedEdges<'f, G>
where
    G::EdgeReferences: 'f,
    G::NodeId: 'f,
{
    type Edges = WeightedEdgeReferences<'f, G::EdgeRef, G::Edges>;

    fn edges(self, a: Self::NodeId) -> Self::Edges {
        WeightedEdgeReferences {
            inner: self.graph.edges(a),
            get_weight: self.weight,
        }
    }
}

impl<'f, G: IntoNeighbors + IntoEdgeReferences> IntoNeighbors for &'_ WithWeightedEdges<'f, G> {
    type Neighbors = <G as IntoNeighbors>::Neighbors;

    fn neighbors(self, a: Self::NodeId) -> Self::Neighbors {
        self.graph.neighbors(a)
    }
}

impl<'f, G: GraphBase + IntoEdgeReferences> GraphBase for WithWeightedEdges<'f, G> {
    type EdgeId = <G as GraphBase>::EdgeId;
    type NodeId = <G as GraphBase>::NodeId;
}

impl<'f, G: NodeIndexable + IntoEdgeReferences> NodeIndexable for &'_ WithWeightedEdges<'f, G> {
    fn from_index(self: &Self, i: usize) -> Self::NodeId {
        self.graph.from_index(i)
    }
    fn node_bound(self: &Self) -> usize {
        self.graph.node_bound()
    }
    fn to_index(self: &Self, a: Self::NodeId) -> usize {
        self.graph.to_index(a)
    }
}

impl<'f, G: NodeCount + IntoEdgeReferences> NodeCount for &'_ WithWeightedEdges<'f, G> {
    fn node_count(self: &Self) -> usize {
        self.graph.node_count()
    }
}

impl<'f, G: IntoNodeIdentifiers + IntoEdgeReferences> IntoNodeIdentifiers
    for &'_ WithWeightedEdges<'f, G>
{
    type NodeIdentifiers = <G as IntoNodeIdentifiers>::NodeIdentifiers;
    fn node_identifiers(self) -> Self::NodeIdentifiers {
        self.graph.node_identifiers()
    }
}

#[derive(Clone, Copy)]
struct IgnoreCtrlEdges<G>(G);

impl<G: NodeCount> NodeCount for IgnoreCtrlEdges<G> {
    fn node_count(self: &Self) -> usize {
        self.0.node_count()
    }
}

impl<G: Visitable> Visitable for IgnoreCtrlEdges<G> {
    type Map = G::Map;

    fn visit_map(self: &Self) -> Self::Map {
        self.0.visit_map()
    }

    fn reset_map(self: &Self, map: &mut Self::Map) {
        self.0.reset_map(map)
    }
}

#[derive(Copy, Clone, Eq, PartialEq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
struct Node<'g>(Option<GlobalLocation<'g>>);

impl<'g> Node<'g> {
    fn return_() -> Self {
        Self(None)
    }
    fn location(loc: GlobalLocation<'g>) -> Self {
        Self(Some(loc))
    }
}

impl<'g> From<GlobalLocation<'g>> for Node<'g> {
    fn from(loc: GlobalLocation<'g>) -> Self {
        Self::location(loc)
    }
}

impl<'g> std::fmt::Display for Node<'g> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let Some(n) = self.0 {
            n.fmt(f)
        } else {
            f.write_str("return")
        }
    }
}

struct NoCtrlNeighbors<E, I: Iterator<Item = E>> {
    inner: I,
    direction: petgraph::Direction,
}

impl<E: EdgeRef<Weight = Edge>, I: Iterator<Item = E>> std::iter::Iterator
    for NoCtrlNeighbors<E, I>
{
    type Item = E::NodeId;
    fn next(&mut self) -> Option<Self::Item> {
        let eref = self.inner.next()?;
        let mut weight = *eref.weight();
        weight.remove_type(EdgeType::Control);
        (!weight.is_empty())
            .then_some(if self.direction == petgraph::Direction::Outgoing {
                eref.target()
            } else {
                eref.source()
            })
            .or_else(|| self.next())
    }
}

struct NoCtrlEdges<E, I: Iterator<Item = E>>(I);

impl<E: EdgeRef<Weight = Edge>, I: Iterator<Item = E>> std::iter::Iterator for NoCtrlEdges<E, I> {
    type Item = E;
    fn next(&mut self) -> Option<Self::Item> {
        let eref = self.0.next()?;
        let mut weight = *eref.weight();
        weight.remove_type(EdgeType::Control);
        (!weight.is_empty()).then_some(eref).or_else(|| self.next())
    }
}

impl<G: IntoEdgesDirected + Data<EdgeWeight = Edge>> IntoNeighborsDirected for IgnoreCtrlEdges<G> {
    type NeighborsDirected = NoCtrlNeighbors<G::EdgeRef, G::EdgesDirected>;
    fn neighbors_directed(
        self,
        n: Self::NodeId,
        d: petgraph::Direction,
    ) -> Self::NeighborsDirected {
        NoCtrlNeighbors {
            inner: self.0.edges_directed(n, d),
            direction: d,
        }
    }
}

impl<G: GraphBase> petgraph::visit::GraphBase for IgnoreCtrlEdges<G> {
    type EdgeId = G::EdgeId;
    type NodeId = G::NodeId;
}

impl<G: GraphRef> GraphRef for IgnoreCtrlEdges<G> {}

impl<G: IntoEdges + Data<EdgeWeight = Edge>> petgraph::visit::IntoNeighbors for IgnoreCtrlEdges<G> {
    type Neighbors = NoCtrlNeighbors<G::EdgeRef, G::Edges>;
    fn neighbors(self, a: Self::NodeId) -> Self::Neighbors {
        NoCtrlNeighbors {
            inner: self.0.edges(a),
            direction: petgraph::Outgoing,
        }
    }
}

impl<G: Data> Data for IgnoreCtrlEdges<G> {
    type EdgeWeight = G::EdgeWeight;
    type NodeWeight = G::NodeWeight;
}

impl<G: IntoEdgeReferences + Data<EdgeWeight = Edge>> IntoEdgeReferences for IgnoreCtrlEdges<G> {
    type EdgeRef = G::EdgeRef;
    type EdgeReferences = NoCtrlEdges<Self::EdgeRef, G::EdgeReferences>;

    fn edge_references(self) -> Self::EdgeReferences {
        NoCtrlEdges(self.0.edge_references())
    }
}

impl<G: IntoNodeIdentifiers> IntoNodeIdentifiers for IgnoreCtrlEdges<G> {
    type NodeIdentifiers = G::NodeIdentifiers;

    fn node_identifiers(self) -> Self::NodeIdentifiers {
        self.0.node_identifiers()
    }
}

impl<G: IntoEdges + Data<EdgeWeight = Edge>> IntoEdges for IgnoreCtrlEdges<G> {
    type Edges = NoCtrlEdges<G::EdgeRef, G::Edges>;
    fn edges(self, a: Self::NodeId) -> Self::Edges {
        NoCtrlEdges(self.0.edges(a))
    }
}

impl<G: IntoEdgesDirected + Data<EdgeWeight = Edge>> IntoEdgesDirected for IgnoreCtrlEdges<G> {
    type EdgesDirected = NoCtrlEdges<G::EdgeRef, G::EdgesDirected>;

    fn edges_directed(self, a: Self::NodeId, dir: petgraph::Direction) -> Self::EdgesDirected {
        NoCtrlEdges(self.0.edges_directed(a, dir))
    }
}

impl<G: NodeIndexable> NodeIndexable for IgnoreCtrlEdges<G> {
    fn from_index(self: &Self, i: usize) -> Self::NodeId {
        self.0.from_index(i)
    }
    fn node_bound(self: &Self) -> usize {
        self.0.node_bound()
    }
    fn to_index(self: &Self, a: Self::NodeId) -> usize {
        self.0.to_index(a)
    }
}

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
        let (flow, _) =
            dfpp::dbg::read_non_transitive_graph_and_body(std::fs::File::open(&args.file).unwrap());

        let arena = dfpp::rust::rustc_arena::TypedArena::default();
        let interner = GlobalLocationInterner::new(&arena);
        let gli = GLI::new(&interner);

        let mut repl = Repl::from_flow_graph(&flow, gli);

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
