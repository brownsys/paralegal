//! Defines the commands that canb be run in the repl.

use clap::Parser;

use crate::graph::Node;

/// Direction in which we are querying edges/neigbors etc of a node
#[derive(Clone, Copy)]
pub enum Direction {
    In,
    Out,
    Both,
}

impl Direction {
    pub fn wants_in(self) -> bool {
        matches!(self, Direction::Both | Direction::In)
    }
    pub fn wants_out(self) -> bool {
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

/// Which kind of edges should be considered for this command
#[derive(Clone, Copy, Debug)]
pub enum PathType {
    Data,
    Control,
    Both,
}

impl std::str::FromStr for PathType {
    type Err = String;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "data" => Ok(PathType::Data),
            "control" => Ok(PathType::Control),
            "all" | "both" => Ok(PathType::Both),
            _ => Err(format!("Invalid path type {s}")),
        }
    }
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

/// Are we selecting a path with a specific metric.
#[derive(Clone, Copy, Debug)]
pub enum PathMetric {
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

impl std::str::FromStr for PathMetric {
    type Err = String;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "min-ctrl" => Ok(PathMetric::MinCtrl),
            "no" => Ok(PathMetric::None),
            "shortest" => Ok(PathMetric::Shortest),
            _ => Err(format!("Invalid path metric {s}")),
        }
    }
}

/// Unique name of a node that also lets us recover a [`dfpp::ir::GlobalLocation`].
///
/// Must be fully expanded basic block nodename, e.g. `bb39[2]@bb58[5]@bb0[4]`. You can find this in the
/// comments in analysis_result.frg.
#[derive(Eq, Ord, PartialEq, PartialOrd, Clone, Debug, Hash)]
pub struct NodeName(String);

impl std::str::FromStr for NodeName {
    type Err = !;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(s.into())
    }
}

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

/// Which format should we dump the graph in?
#[derive(Clone, Copy)]
pub enum GraphOutputFormat {
    Pdf,
    Graphviz,
}

impl std::fmt::Display for GraphOutputFormat {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            GraphOutputFormat::Graphviz => "graphviz",
            GraphOutputFormat::Pdf => "pdf",
        })
    }
}

impl std::str::FromStr for GraphOutputFormat {
    type Err = String;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "pdf" => Ok(GraphOutputFormat::Pdf),
            "gv" | "dot" | "graphviz" => Ok(GraphOutputFormat::Graphviz),
            _ => Err(format!("Invalid output format {s}")),
        }
    }
}

/// Description of commands that can be run in the explorer
#[derive(Clone, Parser)]
pub enum Command {
    /// Find out what a path is between two nodes.
    Paths {
        #[clap(short = 't', long, default_value_t = PathType::Both)]
        typ: PathType,
        from: NodeName,
        to: NodeName,
        #[clap(short, long, default_value_t = PathMetric::None)]
        metric: PathMetric,
        #[clap(short, long)]
        limit: Option<usize>,
    },
    /// Find out if a node is reachable from another node.
    Reachable {
        #[clap(short = 't', long, default_value_t = PathType::Both)]
        typ: PathType,
        from: NodeName,
        to: NodeName,
    },
    /// For a given node, return its inputs and/or outputs.
    Edges {
        from: NodeName,
        #[clap(long, short, default_value_t = Direction::Both)]
        direction: Direction,
        #[clap(short = 't', long, default_value_t = PathType::Both)]
        typ: PathType,
    },
    Alias {
        alias: NodeName,
        origin: NodeName,
    },
    /// Given a node and a length, give you a dot rendering expanding out from that node.
    DotSubgraph {
        from: NodeName,
        depth: usize,
        output: std::path::PathBuf,
        #[clap(long, short, default_value_t = GraphOutputFormat::Pdf)]
        format: GraphOutputFormat,
        #[clap(long, short, default_value_t = Direction::Both)]
        direction: Direction,
    },
    Size,
    /// For a given node, what is its call stack.
    CallChain {
        from: NodeName,
    },
    RenderErroneousFlow {
        input: std::path::PathBuf,
    },
    /// Load a path from a file, replading the currently loaded one (if any)
    Load {
        path: std::path::PathBuf,
    },
}

impl std::str::FromStr for Command {
    type Err = clap::Error;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Command::try_parse_from(["query"].into_iter().chain(s.split_ascii_whitespace()))
    }
}

impl std::fmt::Display for Command {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Command::Paths {
                typ,
                from,
                to,
                metric,
                limit,
            } => {
                write!(f, "paths -t {typ} {from} {to}",)?;
                if !matches!(metric, PathMetric::None) {
                    write!(f, " -m {metric}")?;
                }
                if let Some(lim) = limit {
                    write!(f, " -l {lim}")?;
                }
                Ok(())
            }
            Command::Edges {
                from,
                direction,
                typ,
            } => write!(f, "edges {from} -d {direction} -t {typ}"),
            Command::Alias { alias, origin } => write!(f, "alias {alias} {origin}"),
            Command::Size => write!(f, "size"),
            Command::Reachable { typ, from, to } => write!(f, "reachable -t {typ} {from} {to}"),
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
            Command::CallChain { from } => write!(f, "call-chain {from}"),
            Command::RenderErroneousFlow { input } => {
                write!(f, "render-erroneous-flow {}", input.display())
            }
            Command::Load { path } => write!(f, "load {}", path.display()),
        }
    }
}

impl std::str::FromStr for Direction {
    type Err = String;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "in" => Ok(Direction::In),
            "out" => Ok(Direction::Out),
            "both" | "inout" => Ok(Direction::Both),
            _ => Err(format!("Invalid direction {s}")),
        }
    }
}

#[derive(Debug)]
pub enum RunCommandErr {
    NodeNotFound(NodeName),
    Unimplemented(&'static str),
    EdgeWeightMissing(Node, Node),
    NonsensicalPathMetric(PathType, PathMetric),
    IOError(std::io::Error),
    DotError(Option<i32>),
    LispParseErr(sexpr::parse::Error),
    MinimalFlowParseError(&'static str),
    NoGraphLoaded,
}

impl From<sexpr::parse::Error> for RunCommandErr {
    fn from(e: sexpr::parse::Error) -> Self {
        RunCommandErr::LispParseErr(e)
    }
}

impl From<std::io::Error> for RunCommandErr {
    fn from(err: std::io::Error) -> Self {
        RunCommandErr::IOError(err)
    }
}

impl std::fmt::Display for RunCommandErr {
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
            LispParseErr(e) => write!(f, "Error parsing lisp: {e}"),
            MinimalFlowParseError(s) => write!(f, "Error parsing minimal flow: {s}"),
            NoGraphLoaded => {
                f.write_str("There is no graph loaded currently, load one using the `load` command")
            }
        }
    }
}
