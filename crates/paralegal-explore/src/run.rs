//! Executes the commands from [`crate::command`]

extern crate serde_lexpr as sexpr;
use std::fmt::Display;

use paralegal_flow::{
    ana::inline::{add_weighted_edge, Edge, EdgeType},
    ir::GlobalLocationS,
    serializers::Bodies,
    utils::{outfile_pls, write_sep, Print},
    Either, HashMap,
};

use petgraph::visit::{EdgeRef, IntoEdgesDirected};

use crate::command::*;
use crate::graph::*;

use crate::Repl;

impl Repl {
    fn translate_node(&self, name: NodeName) -> Result<Node, RunCommandErr> {
        let map = self
            .gloc_translation_map
            .as_ref()
            .ok_or(RunCommandErr::NoGraphLoaded)?;
        map
            .get(&name)
            .ok_or(())
            .or_else(|()|
                if self.prompt_for_missing_nodes {
                    println!("Could not find the node '{name}', did you mean instead: (press 'ESC' to abort)");
                    let mut selection = dl::FuzzySelect::new();
                    let items = map.keys().collect::<Vec<_>>();
                    selection.items(items.as_slice())
                        .with_initial_text(&name);
                    if let Some(idx) = selection.interact_opt()? {
                        Ok(&map[items[idx]])
                    } else {
                        Err(RunCommandErr::NodeNotFound(name))
                    }
                } else {
                    Err(RunCommandErr::NodeNotFound(name))
                })
            .map(|r| *r)
    }

    fn data_graph(&self) -> Result<IgnoreCtrlEdges<&'_ Graph>, RunCommandErr> {
        Ok(self.graph()?.into())
    }

    fn graph(&self) -> Result<&'_ Graph, RunCommandErr> {
        self.graph.as_ref().ok_or(RunCommandErr::NoGraphLoaded)
    }

    fn create_subgraph(
        &self,
        from: Node,
        depth: usize,
        direction: Direction,
    ) -> Result<Graph, RunCommandErr> {
        let graph = self.graph()?;
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
                .then(|| graph.edges(from).map(|(_, to, w)| (to, w, true)))
                .into_iter()
                .flatten()
                .chain(
                    direction
                        .wants_in()
                        .then(|| {
                            graph
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
        Ok(subg)
    }

    fn run_paths_command(
        &mut self,
        from: Node,
        to: Node,
        path_type: PathType,
        metric: PathMetric,
        limit: Option<usize>,
    ) -> Result<(), RunCommandErr> {
        let paths = match path_type {
            PathType::Both if matches!(metric, PathMetric::Shortest) => {
                let graph = self.graph()?;
                Ok(Box::new(
                    [{
                        let paths = petgraph::algo::bellman_ford(
                            &WithWeightedEdges::new(graph, &|_| 1.0),
                            from,
                        )
                        .unwrap();
                        let mut v = std::iter::successors(Some(to), |to| {
                            paths.predecessors[petgraph::visit::NodeIndexable::to_index(graph, *to)]
                        })
                        .collect::<Vec<_>>();
                        v.reverse();
                        v
                    }]
                    .into_iter(),
                ) as Box<dyn Iterator<Item = Vec<Node>>>)
            }
            PathType::Data if matches!(metric, PathMetric::Shortest) => {
                let graph = self.data_graph()?;
                Ok(Box::new(
                    [{
                        let paths = petgraph::algo::bellman_ford(
                            &WithWeightedEdges::new(graph, &|_| 1.0),
                            from,
                        )
                        .unwrap();
                        let mut v = std::iter::successors(Some(to), |to| {
                            paths.predecessors
                                [petgraph::visit::NodeIndexable::to_index(&graph, *to)]
                        })
                        .collect::<Vec<_>>();
                        v.reverse();
                        v
                    }]
                    .into_iter(),
                ) as Box<dyn Iterator<Item = Vec<Node>>>)
            }
            PathType::Both => Ok(Box::new(petgraph::algo::all_simple_paths::<Vec<_>, _>(
                self.graph()?,
                from,
                to,
                0,
                None,
            )) as Box<dyn Iterator<Item = Vec<Node>>>),
            PathType::Data => Ok(Box::new(petgraph::algo::all_simple_paths::<Vec<_>, _>(
                self.data_graph()?,
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
                                .graph()?
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
                        Print(|fmt| {
                            write_sep(fmt, "\n    -> ", &path, |node, fmt| {
                                write!(
                                    fmt,
                                    "{node}   {}",
                                    self.fn_name_for_node(*node).unwrap().unwrap_or("?")
                                )
                            })
                        })
                    );
                    println!("Extrema for {metric} metric found was {min}")
                }
            }
            PathMetric::None | PathMetric::Shortest => {
                let paths = if let Some(lim) = limit {
                    Either::Right(paths.take(lim))
                } else {
                    Either::Left(paths)
                };
                for path in paths {
                    println!(
                        "{}",
                        Print(|fmt| {
                            write_sep(fmt, "\n    -> ", &path, |node, fmt| {
                                write!(
                                    fmt,
                                    "{node}   {}",
                                    self.fn_name_for_node(*node).unwrap().unwrap_or("?")
                                )
                            })
                        })
                    );
                    println!();
                }
            }
        }
        Ok(())
    }

    fn fn_name_for_node(&self, n: Node) -> Result<Option<&str>, RunCommandErr> {
        if let Some(n) = n.location() {
            self.fn_name_for_loc(n.innermost())
        } else {
            Ok(Some("Return"))
        }
    }

    fn fn_name_for_loc(&self, n: GlobalLocationS) -> Result<Option<&str>, RunCommandErr> {
        Ok(self.bodies()?.0.get(&n.function).and_then(|body| {
            body.1
                 .0
                .iter()
                .find(|t| t.location == n.location)
                .map(|t| t.contents.as_str())
        }))
    }

    fn bodies(&self) -> Result<&'_ Bodies, RunCommandErr> {
        self.bodies.as_ref().ok_or(RunCommandErr::NoGraphLoaded)
    }

    fn run_edges<G: IntoEdgesDirected<NodeId = Node>>(&self, g: G, node: Node, direction: Direction)
    where
        G::EdgeWeight: Display,
    {
        let mut num = 0;
        if direction.wants_in() {
            for e in g.edges_directed(node, petgraph::Direction::Incoming) {
                num += 1;
                println!("in {} {}", e.source(), e.weight());
            }
        }
        if direction.wants_out() {
            for e in g.edges_directed(node, petgraph::Direction::Outgoing) {
                num += 1;
                println!("out {} {}", e.target(), e.weight());
            }
        }
        println!("Found {num} edges");
    }

    pub fn run_command(&mut self, command: Command) -> Result<(), RunCommandErr> {
        match command {
            Command::Load { path } => self.load_graph(&path),
            Command::DotSubgraph {
                from,
                depth,
                output,
                format,
                direction,
            } => {
                let from = self.translate_node(from)?;
                let subg = self.create_subgraph(from, depth, direction)?;
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
            Command::Reachable { typ, from, to } => {
                use petgraph::algo::has_path_connecting;
                let from = self.translate_node(from)?;
                let to = self.translate_node(to)?;
                let is_reachable = match typ {
                    PathType::Both => Ok(has_path_connecting(self.graph()?, from, to, None)),
                    PathType::Data => Ok(has_path_connecting(self.data_graph()?, from, to, None)),
                    PathType::Control => Err(RunCommandErr::Unimplemented("control-reachable")),
                }?;
                println!("{}", if is_reachable { "Yes" } else { "No" });
                Ok(())
            }
            Command::Paths {
                typ,
                from,
                to,
                metric,
                limit,
            } => {
                if matches!((typ, metric), (PathType::Data, PathMetric::MinCtrl)) {
                    return Err(RunCommandErr::NonsensicalPathMetric(typ, metric));
                }
                let from = self.translate_node(from)?;
                let to = self.translate_node(to)?;
                self.run_paths_command(from, to, typ, metric, limit)
            }
            Command::Edges {
                from,
                direction,
                typ,
            } => {
                let node = self.translate_node(from)?;
                match typ {
                    PathType::Both => self.run_edges(self.graph()?, node, direction),
                    PathType::Data => self.run_edges(self.data_graph()?, node, direction),
                    PathType::Control => return Err(RunCommandErr::Unimplemented("control edges")),
                }
                Ok(())
            }
            Command::Alias { alias, origin } => {
                let node = self.translate_node(origin)?;
                if let Some(old) = self
                    .gloc_translation_map
                    .as_mut()
                    .ok_or(RunCommandErr::NoGraphLoaded)?
                    .insert(alias, node)
                {
                    println!("Overwrote prior value {old}");
                }
                Ok(())
            }
            Command::Size => {
                println!(
                    "{} nodes, {} edges",
                    self.graph()?.node_count(),
                    self.graph()?
                        .all_edges()
                        .map(|(_, _, weight)| weight.count())
                        .sum::<u32>()
                );
                Ok(())
            }
            Command::CallChain { from } => {
                let node = self.translate_node(from)?;
                if let Some(loc) = node.location() {
                    println!(
                        "{}",
                        Print(|fmt| write_sep(
                            fmt,
                            "\n  called by ",
                            loc.as_slice().iter().rev(),
                            |node, fmt| fmt
                                .write_str(self.fn_name_for_loc(*node).unwrap().unwrap_or("?"))
                        ))
                    );
                } else {
                    println!("Return")
                }
                Ok(())
            }
            Command::RenderErroneousFlow { input } => {
                let mut file = std::fs::File::open(&input)?;
                let mut all = String::new();
                use std::io::Read;
                file.read_to_string(&mut all)?;
                let target = all
                    .split_once("'(#hash")
                    .ok_or(RunCommandErr::MinimalFlowParseError(
                        "Did not find pattern \"'(#hash\"",
                    ))?
                    .1;
                let target = target
                    .rsplit_once("'((")
                    .ok_or(RunCommandErr::MinimalFlowParseError(
                        "Did not find pattern \"'((\" at the file end",
                    ))?
                    .0;
                let target = target
                    .rsplit_once(')')
                    .ok_or(RunCommandErr::MinimalFlowParseError(
                        "Did not find pattern \")\" before \"'((\" at the file end",
                    ))?
                    .0;
                let value = sexpr::parse::from_str(target)?;
                let flow =
                    value
                        .get("minimal_subflow")
                        .ok_or(RunCommandErr::MinimalFlowParseError(
                            "Did not find 'minimal_subflow' key",
                        ))?;
                let arg_call_site =
                    value
                        .get("arg_call_site")
                        .ok_or(RunCommandErr::MinimalFlowParseError(
                            "Did not find 'arg_call_site' key",
                        ))?;
                let mut graph: petgraph::prelude::GraphMap<&str, u16, petgraph::Directed> = petgraph::graphmap::GraphMap::from_edges(
                    flow.list_iter()
                        .ok_or(RunCommandErr::MinimalFlowParseError("'minimal_subflow' is not an s-expression list"))?
                        .map(|v| match v.to_ref_vec().ok_or(RunCommandErr::MinimalFlowParseError("'minimal_subflow' elements are not lists"))?
                        .as_slice()
                        {
                            [_, from, to] => Ok((
                                from.as_symbol().ok_or(RunCommandErr::MinimalFlowParseError("Second elements of 'minimal_subflow' elements should be a symbol"))?, 
                                to.as_symbol().ok_or(RunCommandErr::MinimalFlowParseError("Third elements of 'minimal_subflow' elements should be a symbol"))?, 
                                0)),
                            _ => Err(RunCommandErr::MinimalFlowParseError("'minimal_subflow' list elements should be 3-tuples"))
                        })
                        .collect::<Result<Vec<_>, _>>()?
                    );

                for res in arg_call_site.list_iter()
                            .ok_or(RunCommandErr::MinimalFlowParseError("'arg_call_site' is not an s-expression list"))?
                            //.ok_or(RunCommandErr::MinimalFlowParseError)?
                            .map(|v| match v.to_ref_vec().ok_or(RunCommandErr::MinimalFlowParseError("'arg_call_site' elements are not lists"))?
                            .as_slice()
                            {
                                [from, to] => Ok((
                                    from.as_symbol().ok_or(RunCommandErr::MinimalFlowParseError("First elements of 'arg_call_site' elements should be a symbol"))?, 
                                    to.as_symbol().ok_or(RunCommandErr::MinimalFlowParseError("Second elements of 'arg_call_site' elements should be a symbol"))?, 
                                    )),
                                _ => Err(RunCommandErr::MinimalFlowParseError("'arg_call_site' list elements should be 2-tuples"))
                            }) {
                    let (arg, fun) = res?;
                    if graph.contains_node(arg) && graph.contains_node(fun) {
                        graph.add_edge(arg, fun, 0);
                    }
                }
                let mut outfile = outfile_pls(input.with_extension("gv"))?;
                use std::io::Write;
                write!(
                    outfile,
                    "{}",
                    petgraph::dot::Dot::with_attr_getters(
                        &graph,
                        &[],
                        &|_, _| "".to_string(),
                        &|_, _| "shape=box".to_string()
                    )
                )?;
                Ok(())
            }
        }
    }

    pub fn load_graph(&mut self, path: &std::path::Path) -> Result<(), RunCommandErr> {
        let (flow, bodies) =
            paralegal_flow::dbg::read_non_transitive_graph_and_body(std::fs::File::open(path).unwrap());
        let mut g = petgraph::graphmap::GraphMap::<_, _, petgraph::Directed>::new();
        let graph = &mut g;

        for (to, deps) in flow.location_dependencies.iter() {
            for (weight, deps) in deps
                .input_deps
                .iter()
                .enumerate()
                .map(|(i, deps)| (Edge::from_iter([EdgeType::Data(i as u32)]), deps))
                .chain([(Edge::from_iter([EdgeType::Control]), &deps.ctrl_deps)])
            {
                for from in deps {
                    add_weighted_edge(graph, (*from).into(), (*to).into(), weight);
                }
            }
        }

        for from in &flow.return_dependencies {
            add_weighted_edge(
                graph,
                (*from).into(),
                Node::return_(),
                Edge::from_iter([EdgeType::Data(0)]),
            );
        }

        let gloc_translation_map: HashMap<NodeName, Node> =
            g.nodes().map(|n| (format!("{n}").into(), n)).collect();
        self.gloc_translation_map = Some(gloc_translation_map);
        self.bodies = Some(bodies);
        self.graph = Some(g);
        Ok(())
    }
}
