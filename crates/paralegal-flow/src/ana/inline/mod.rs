//! The [`Inliner`]. The 30s summary of what this does is
//! 1. It starts from single-procedure analyses ([`regal::Body`])
//! 2. Turns them into graphs ([`ProcedureGraph`])
//! 3. Turns locations into global locations in both the graph and in the
//!    equations ([`InlinedGraph`])
//! 4. Inlines callees that are (un)marked. In the graphs the nodes are are
//!    replaced by the callee graph, reconnecting incoming and outgoing edges at
//!    the boundary. Callee locations are relativized ([`GliAt::relativize`]).
//!    Callee equations also have the bases rewritten
//!    ([`Inliner::relativize_eqs`]) before being added to the caller equations.
//! 5. Use the equations from place analysis prune edges
//!    ([`InlinedGraph::prune_impossible_edges`]) using the accumulated set of
//!    equations
mod graph;
pub mod judge;
