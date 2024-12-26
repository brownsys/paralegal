(function() {
    var type_impls = Object.fromEntries([["paralegal_policy",[["<details class=\"toggle implementors-toggle\" open><summary><section id=\"impl-Clone-for-GlobalNode\" class=\"impl\"><a class=\"src rightside\" href=\"src/paralegal_spdg/lib.rs.html#622\">Source</a><a href=\"#impl-Clone-for-GlobalNode\" class=\"anchor\">§</a><h3 class=\"code-header\">impl <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/clone/trait.Clone.html\" title=\"trait core::clone::Clone\">Clone</a> for <a class=\"struct\" href=\"paralegal_policy/struct.GlobalNode.html\" title=\"struct paralegal_policy::GlobalNode\">GlobalNode</a></h3></section></summary><div class=\"impl-items\"><details class=\"toggle method-toggle\" open><summary><section id=\"method.clone\" class=\"method trait-impl\"><a class=\"src rightside\" href=\"src/paralegal_spdg/lib.rs.html#622\">Source</a><a href=\"#method.clone\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"https://doc.rust-lang.org/nightly/core/clone/trait.Clone.html#tymethod.clone\" class=\"fn\">clone</a>(&amp;self) -&gt; <a class=\"struct\" href=\"paralegal_policy/struct.GlobalNode.html\" title=\"struct paralegal_policy::GlobalNode\">GlobalNode</a></h4></section></summary><div class='docblock'>Returns a copy of the value. <a href=\"https://doc.rust-lang.org/nightly/core/clone/trait.Clone.html#tymethod.clone\">Read more</a></div></details><details class=\"toggle method-toggle\" open><summary><section id=\"method.clone_from\" class=\"method trait-impl\"><span class=\"rightside\"><span class=\"since\" title=\"Stable since Rust version 1.0.0\">1.0.0</span> · <a class=\"src\" href=\"https://doc.rust-lang.org/nightly/src/core/clone.rs.html#174\">Source</a></span><a href=\"#method.clone_from\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"https://doc.rust-lang.org/nightly/core/clone/trait.Clone.html#method.clone_from\" class=\"fn\">clone_from</a>(&amp;mut self, source: &amp;Self)</h4></section></summary><div class='docblock'>Performs copy-assignment from <code>source</code>. <a href=\"https://doc.rust-lang.org/nightly/core/clone/trait.Clone.html#method.clone_from\">Read more</a></div></details></div></details>","Clone","paralegal_policy::context::MarkableId"],["<details class=\"toggle implementors-toggle\" open><summary><section id=\"impl-Debug-for-GlobalNode\" class=\"impl\"><a class=\"src rightside\" href=\"src/paralegal_spdg/lib.rs.html#622\">Source</a><a href=\"#impl-Debug-for-GlobalNode\" class=\"anchor\">§</a><h3 class=\"code-header\">impl <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/fmt/trait.Debug.html\" title=\"trait core::fmt::Debug\">Debug</a> for <a class=\"struct\" href=\"paralegal_policy/struct.GlobalNode.html\" title=\"struct paralegal_policy::GlobalNode\">GlobalNode</a></h3></section></summary><div class=\"impl-items\"><details class=\"toggle method-toggle\" open><summary><section id=\"method.fmt\" class=\"method trait-impl\"><a class=\"src rightside\" href=\"src/paralegal_spdg/lib.rs.html#622\">Source</a><a href=\"#method.fmt\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"https://doc.rust-lang.org/nightly/core/fmt/trait.Debug.html#tymethod.fmt\" class=\"fn\">fmt</a>(&amp;self, f: &amp;mut <a class=\"struct\" href=\"https://doc.rust-lang.org/nightly/core/fmt/struct.Formatter.html\" title=\"struct core::fmt::Formatter\">Formatter</a>&lt;'_&gt;) -&gt; <a class=\"enum\" href=\"https://doc.rust-lang.org/nightly/core/result/enum.Result.html\" title=\"enum core::result::Result\">Result</a>&lt;<a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.unit.html\">()</a>, <a class=\"struct\" href=\"https://doc.rust-lang.org/nightly/core/fmt/struct.Error.html\" title=\"struct core::fmt::Error\">Error</a>&gt;</h4></section></summary><div class='docblock'>Formats the value using the given formatter. <a href=\"https://doc.rust-lang.org/nightly/core/fmt/trait.Debug.html#tymethod.fmt\">Read more</a></div></details></div></details>","Debug","paralegal_policy::context::MarkableId"],["<details class=\"toggle implementors-toggle\" open><summary><section id=\"impl-GlobalNode\" class=\"impl\"><a class=\"src rightside\" href=\"src/paralegal_spdg/lib.rs.html#628\">Source</a><a href=\"#impl-GlobalNode\" class=\"anchor\">§</a><h3 class=\"code-header\">impl <a class=\"struct\" href=\"paralegal_policy/struct.GlobalNode.html\" title=\"struct paralegal_policy::GlobalNode\">GlobalNode</a></h3></section></summary><div class=\"impl-items\"><details class=\"toggle method-toggle\" open><summary><section id=\"method.unsafe_new\" class=\"method\"><a class=\"src rightside\" href=\"src/paralegal_spdg/lib.rs.html#631\">Source</a><h4 class=\"code-header\">pub fn <a href=\"paralegal_policy/struct.GlobalNode.html#tymethod.unsafe_new\" class=\"fn\">unsafe_new</a>(ctrl_id: <a class=\"struct\" href=\"https://doc.rust-lang.org/nightly/nightly-rustc/rustc_span/def_id/struct.DefId.html\" title=\"struct rustc_span::def_id::DefId\">DefId</a>, index: <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.usize.html\">usize</a>) -&gt; <a class=\"struct\" href=\"paralegal_policy/struct.GlobalNode.html\" title=\"struct paralegal_policy::GlobalNode\">GlobalNode</a></h4></section></summary><div class=\"docblock\"><p>Create a new node with no guarantee that it exists in the SPDG of the\ncontroller.</p>\n</div></details><details class=\"toggle method-toggle\" open><summary><section id=\"method.from_local_node\" class=\"method\"><a class=\"src rightside\" href=\"src/paralegal_spdg/lib.rs.html#642\">Source</a><h4 class=\"code-header\">pub fn <a href=\"paralegal_policy/struct.GlobalNode.html#tymethod.from_local_node\" class=\"fn\">from_local_node</a>(ctrl_id: <a class=\"struct\" href=\"https://doc.rust-lang.org/nightly/nightly-rustc/rustc_span/def_id/struct.DefId.html\" title=\"struct rustc_span::def_id::DefId\">DefId</a>, node: <a class=\"struct\" href=\"petgraph/graph_impl/struct.NodeIndex.html\" title=\"struct petgraph::graph_impl::NodeIndex\">NodeIndex</a>) -&gt; <a class=\"struct\" href=\"paralegal_policy/struct.GlobalNode.html\" title=\"struct paralegal_policy::GlobalNode\">GlobalNode</a></h4></section></summary><div class=\"docblock\"><p>Create a new globally identified node by pairing a node local to a\nparticular SPDG with it’s controller id.</p>\n<p>Meant for internal use only.</p>\n</div></details><details class=\"toggle method-toggle\" open><summary><section id=\"method.local_node\" class=\"method\"><a class=\"src rightside\" href=\"src/paralegal_spdg/lib.rs.html#650\">Source</a><h4 class=\"code-header\">pub fn <a href=\"paralegal_policy/struct.GlobalNode.html#tymethod.local_node\" class=\"fn\">local_node</a>(self) -&gt; <a class=\"struct\" href=\"petgraph/graph_impl/struct.NodeIndex.html\" title=\"struct petgraph::graph_impl::NodeIndex\">NodeIndex</a></h4></section></summary><div class=\"docblock\"><p>The local node in the SPDG</p>\n</div></details><details class=\"toggle method-toggle\" open><summary><section id=\"method.controller_id\" class=\"method\"><a class=\"src rightside\" href=\"src/paralegal_spdg/lib.rs.html#655\">Source</a><h4 class=\"code-header\">pub fn <a href=\"paralegal_policy/struct.GlobalNode.html#tymethod.controller_id\" class=\"fn\">controller_id</a>(self) -&gt; <a class=\"struct\" href=\"https://doc.rust-lang.org/nightly/nightly-rustc/rustc_span/def_id/struct.DefId.html\" title=\"struct rustc_span::def_id::DefId\">DefId</a></h4></section></summary><div class=\"docblock\"><p>The identifier for the SPDG this node is contained in</p>\n</div></details></div></details>",0,"paralegal_policy::context::MarkableId"],["<details class=\"toggle implementors-toggle\" open><summary><section id=\"impl-Hash-for-GlobalNode\" class=\"impl\"><a class=\"src rightside\" href=\"src/paralegal_spdg/lib.rs.html#622\">Source</a><a href=\"#impl-Hash-for-GlobalNode\" class=\"anchor\">§</a><h3 class=\"code-header\">impl <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/hash/trait.Hash.html\" title=\"trait core::hash::Hash\">Hash</a> for <a class=\"struct\" href=\"paralegal_policy/struct.GlobalNode.html\" title=\"struct paralegal_policy::GlobalNode\">GlobalNode</a></h3></section></summary><div class=\"impl-items\"><details class=\"toggle method-toggle\" open><summary><section id=\"method.hash\" class=\"method trait-impl\"><a class=\"src rightside\" href=\"src/paralegal_spdg/lib.rs.html#622\">Source</a><a href=\"#method.hash\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"https://doc.rust-lang.org/nightly/core/hash/trait.Hash.html#tymethod.hash\" class=\"fn\">hash</a>&lt;__H&gt;(&amp;self, state: <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.reference.html\">&amp;mut __H</a>)<div class=\"where\">where\n    __H: <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/hash/trait.Hasher.html\" title=\"trait core::hash::Hasher\">Hasher</a>,</div></h4></section></summary><div class='docblock'>Feeds this value into the given <a href=\"https://doc.rust-lang.org/nightly/core/hash/trait.Hasher.html\" title=\"trait core::hash::Hasher\"><code>Hasher</code></a>. <a href=\"https://doc.rust-lang.org/nightly/core/hash/trait.Hash.html#tymethod.hash\">Read more</a></div></details><details class=\"toggle method-toggle\" open><summary><section id=\"method.hash_slice\" class=\"method trait-impl\"><span class=\"rightside\"><span class=\"since\" title=\"Stable since Rust version 1.3.0\">1.3.0</span> · <a class=\"src\" href=\"https://doc.rust-lang.org/nightly/src/core/hash/mod.rs.html#235-237\">Source</a></span><a href=\"#method.hash_slice\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"https://doc.rust-lang.org/nightly/core/hash/trait.Hash.html#method.hash_slice\" class=\"fn\">hash_slice</a>&lt;H&gt;(data: &amp;[Self], state: <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.reference.html\">&amp;mut H</a>)<div class=\"where\">where\n    H: <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/hash/trait.Hasher.html\" title=\"trait core::hash::Hasher\">Hasher</a>,\n    Self: <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/marker/trait.Sized.html\" title=\"trait core::marker::Sized\">Sized</a>,</div></h4></section></summary><div class='docblock'>Feeds a slice of this type into the given <a href=\"https://doc.rust-lang.org/nightly/core/hash/trait.Hasher.html\" title=\"trait core::hash::Hasher\"><code>Hasher</code></a>. <a href=\"https://doc.rust-lang.org/nightly/core/hash/trait.Hash.html#method.hash_slice\">Read more</a></div></details></div></details>","Hash","paralegal_policy::context::MarkableId"],["<details class=\"toggle implementors-toggle\" open><summary><section id=\"impl-IntoIterGlobalNodes-for-GlobalNode\" class=\"impl\"><a class=\"src rightside\" href=\"src/paralegal_spdg/lib.rs.html#660\">Source</a><a href=\"#impl-IntoIterGlobalNodes-for-GlobalNode\" class=\"anchor\">§</a><h3 class=\"code-header\">impl <a class=\"trait\" href=\"paralegal_policy/trait.IntoIterGlobalNodes.html\" title=\"trait paralegal_policy::IntoIterGlobalNodes\">IntoIterGlobalNodes</a> for <a class=\"struct\" href=\"paralegal_policy/struct.GlobalNode.html\" title=\"struct paralegal_policy::GlobalNode\">GlobalNode</a></h3></section></summary><div class=\"impl-items\"><details class=\"toggle\" open><summary><section id=\"associatedtype.Iter\" class=\"associatedtype trait-impl\"><a class=\"src rightside\" href=\"src/paralegal_spdg/lib.rs.html#661\">Source</a><a href=\"#associatedtype.Iter\" class=\"anchor\">§</a><h4 class=\"code-header\">type <a href=\"paralegal_policy/trait.IntoIterGlobalNodes.html#associatedtype.Iter\" class=\"associatedtype\">Iter</a> = <a class=\"struct\" href=\"https://doc.rust-lang.org/nightly/core/iter/sources/once/struct.Once.html\" title=\"struct core::iter::sources::once::Once\">Once</a>&lt;<a class=\"struct\" href=\"petgraph/graph_impl/struct.NodeIndex.html\" title=\"struct petgraph::graph_impl::NodeIndex\">NodeIndex</a>&gt;</h4></section></summary><div class='docblock'>The iterator returned by <a href=\"paralegal_policy/trait.IntoIterGlobalNodes.html#tymethod.iter_nodes\" title=\"method paralegal_spdg::IntoIterGlobalNodes::iter_nodes::iter_nodes\"><code>Self::iter_nodes</code></a></div></details><details class=\"toggle method-toggle\" open><summary><section id=\"method.iter_nodes\" class=\"method trait-impl\"><a class=\"src rightside\" href=\"src/paralegal_spdg/lib.rs.html#662\">Source</a><a href=\"#method.iter_nodes\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"paralegal_policy/trait.IntoIterGlobalNodes.html#tymethod.iter_nodes\" class=\"fn\">iter_nodes</a>(self) -&gt; &lt;<a class=\"struct\" href=\"paralegal_policy/struct.GlobalNode.html\" title=\"struct paralegal_policy::GlobalNode\">GlobalNode</a> as <a class=\"trait\" href=\"paralegal_policy/trait.IntoIterGlobalNodes.html\" title=\"trait paralegal_policy::IntoIterGlobalNodes\">IntoIterGlobalNodes</a>&gt;::<a class=\"associatedtype\" href=\"paralegal_policy/trait.IntoIterGlobalNodes.html#associatedtype.Iter\" title=\"type paralegal_policy::IntoIterGlobalNodes::Iter\">Iter</a></h4></section></summary><div class='docblock'>iterate over the local nodes</div></details><details class=\"toggle method-toggle\" open><summary><section id=\"method.controller_id\" class=\"method trait-impl\"><a class=\"src rightside\" href=\"src/paralegal_spdg/lib.rs.html#666\">Source</a><a href=\"#method.controller_id\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"paralegal_policy/trait.IntoIterGlobalNodes.html#tymethod.controller_id\" class=\"fn\">controller_id</a>(self) -&gt; <a class=\"struct\" href=\"https://doc.rust-lang.org/nightly/nightly-rustc/rustc_span/def_id/struct.DefId.html\" title=\"struct rustc_span::def_id::DefId\">DefId</a></h4></section></summary><div class='docblock'>The controller id all of these nodes are located in.</div></details><details class=\"toggle method-toggle\" open><summary><section id=\"method.iter_global_nodes\" class=\"method trait-impl\"><a class=\"src rightside\" href=\"src/paralegal_spdg/lib.rs.html#592\">Source</a><a href=\"#method.iter_global_nodes\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"paralegal_policy/trait.IntoIterGlobalNodes.html#method.iter_global_nodes\" class=\"fn\">iter_global_nodes</a>(self) -&gt; <a class=\"struct\" href=\"paralegal_spdg/struct.GlobalNodeIter.html\" title=\"struct paralegal_spdg::GlobalNodeIter\">GlobalNodeIter</a>&lt;Self&gt;</h4></section></summary><div class='docblock'>Iterate all nodes as globally identified one’s. <a href=\"paralegal_policy/trait.IntoIterGlobalNodes.html#method.iter_global_nodes\">Read more</a></div></details><details class=\"toggle method-toggle\" open><summary><section id=\"method.extended\" class=\"method trait-impl\"><a class=\"src rightside\" href=\"src/paralegal_spdg/lib.rs.html#602\">Source</a><a href=\"#method.extended\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"paralegal_policy/trait.IntoIterGlobalNodes.html#method.extended\" class=\"fn\">extended</a>(self, other: impl <a class=\"trait\" href=\"paralegal_policy/trait.IntoIterGlobalNodes.html\" title=\"trait paralegal_policy::IntoIterGlobalNodes\">IntoIterGlobalNodes</a>) -&gt; <a class=\"enum\" href=\"https://doc.rust-lang.org/nightly/core/option/enum.Option.html\" title=\"enum core::option::Option\">Option</a>&lt;<a class=\"struct\" href=\"paralegal_spdg/node_cluster/struct.NodeCluster.html\" title=\"struct paralegal_spdg::node_cluster::NodeCluster\">NodeCluster</a>&gt;</h4></section></summary><div class='docblock'>A convenience method for gathering multiple node(cluster)s together. <a href=\"paralegal_policy/trait.IntoIterGlobalNodes.html#method.extended\">Read more</a></div></details><details class=\"toggle method-toggle\" open><summary><section id=\"method.to_local_cluster\" class=\"method trait-impl\"><a class=\"src rightside\" href=\"src/paralegal_spdg/lib.rs.html#613\">Source</a><a href=\"#method.to_local_cluster\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"paralegal_policy/trait.IntoIterGlobalNodes.html#method.to_local_cluster\" class=\"fn\">to_local_cluster</a>(self) -&gt; <a class=\"struct\" href=\"paralegal_spdg/node_cluster/struct.NodeCluster.html\" title=\"struct paralegal_spdg::node_cluster::NodeCluster\">NodeCluster</a></h4></section></summary><div class='docblock'>Collect the iterator into a cluster</div></details></div></details>","IntoIterGlobalNodes","paralegal_policy::context::MarkableId"],["<details class=\"toggle implementors-toggle\" open><summary><section id=\"impl-NodeExt-for-GlobalNode\" class=\"impl\"><a class=\"src rightside\" href=\"src/paralegal_policy/context.rs.html#869-973\">Source</a><a href=\"#impl-NodeExt-for-GlobalNode\" class=\"anchor\">§</a><h3 class=\"code-header\">impl <a class=\"trait\" href=\"paralegal_policy/context/trait.NodeExt.html\" title=\"trait paralegal_policy::context::NodeExt\">NodeExt</a> for <a class=\"struct\" href=\"paralegal_policy/struct.GlobalNode.html\" title=\"struct paralegal_policy::GlobalNode\">GlobalNode</a></h3></section></summary><div class=\"impl-items\"><details class=\"toggle method-toggle\" open><summary><section id=\"method.has_marker\" class=\"method trait-impl\"><a class=\"src rightside\" href=\"src/paralegal_policy/context.rs.html#926-936\">Source</a><a href=\"#method.has_marker\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"paralegal_policy/context/trait.NodeExt.html#tymethod.has_marker\" class=\"fn\">has_marker</a>&lt;C: <a class=\"trait\" href=\"paralegal_policy/diagnostics/trait.HasDiagnosticsBase.html\" title=\"trait paralegal_policy::diagnostics::HasDiagnosticsBase\">HasDiagnosticsBase</a>&gt;(self, ctx: C, marker: <a class=\"type\" href=\"paralegal_policy/context/type.Marker.html\" title=\"type paralegal_policy::context::Marker\">Marker</a>) -&gt; <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.bool.html\">bool</a></h4></section></summary><div class=\"docblock\"><p>Returns whether this Node has the marker applied to it directly or via its type.</p>\n</div></details><details class=\"toggle method-toggle\" open><summary><section id=\"method.has_type\" class=\"method trait-impl\"><a class=\"src rightside\" href=\"src/paralegal_policy/context.rs.html#870-875\">Source</a><a href=\"#method.has_type\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"paralegal_policy/context/trait.NodeExt.html#tymethod.has_type\" class=\"fn\">has_type</a>(self, t: <a class=\"type\" href=\"paralegal_spdg/type.TypeId.html\" title=\"type paralegal_spdg::TypeId\">TypeId</a>, ctx: &amp;<a class=\"struct\" href=\"paralegal_policy/context/struct.RootContext.html\" title=\"struct paralegal_policy::context::RootContext\">RootContext</a>) -&gt; <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.bool.html\">bool</a></h4></section></summary><div class='docblock'>Returns true if this node has the provided type</div></details><details class=\"toggle method-toggle\" open><summary><section id=\"method.associated_call_site\" class=\"method trait-impl\"><a class=\"src rightside\" href=\"src/paralegal_policy/context.rs.html#876-880\">Source</a><a href=\"#method.associated_call_site\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"paralegal_policy/context/trait.NodeExt.html#tymethod.associated_call_site\" class=\"fn\">associated_call_site</a>(self, ctx: &amp;<a class=\"struct\" href=\"paralegal_policy/context/struct.RootContext.html\" title=\"struct paralegal_policy::context::RootContext\">RootContext</a>) -&gt; <a class=\"struct\" href=\"flowistry_pdg/pdg/struct.CallString.html\" title=\"struct flowistry_pdg::pdg::CallString\">CallString</a></h4></section></summary><div class='docblock'>Find the call string for the statement or function that produced this node.</div></details><details class=\"toggle method-toggle\" open><summary><section id=\"method.types\" class=\"method trait-impl\"><a class=\"src rightside\" href=\"src/paralegal_policy/context.rs.html#882-887\">Source</a><a href=\"#method.types\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"paralegal_policy/context/trait.NodeExt.html#tymethod.types\" class=\"fn\">types</a>(self, ctx: &amp;<a class=\"struct\" href=\"paralegal_policy/context/struct.RootContext.html\" title=\"struct paralegal_policy::context::RootContext\">RootContext</a>) -&gt; &amp;[<a class=\"type\" href=\"paralegal_spdg/type.TypeId.html\" title=\"type paralegal_spdg::TypeId\">TypeId</a>]</h4></section></summary><div class='docblock'>Get the type(s) of a Node.</div></details><details class=\"toggle method-toggle\" open><summary><section id=\"method.describe\" class=\"method trait-impl\"><a class=\"src rightside\" href=\"src/paralegal_policy/context.rs.html#889-894\">Source</a><a href=\"#method.describe\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"paralegal_policy/context/trait.NodeExt.html#tymethod.describe\" class=\"fn\">describe</a>(self, ctx: &amp;<a class=\"struct\" href=\"paralegal_policy/context/struct.RootContext.html\" title=\"struct paralegal_policy::context::RootContext\">RootContext</a>) -&gt; <a class=\"struct\" href=\"paralegal_spdg/struct.DisplayNode.html\" title=\"struct paralegal_spdg::DisplayNode\">DisplayNode</a>&lt;'_&gt;</h4></section></summary><div class='docblock'>Returns a DisplayNode for the given Node</div></details><details class=\"toggle method-toggle\" open><summary><section id=\"method.info\" class=\"method trait-impl\"><a class=\"src rightside\" href=\"src/paralegal_policy/context.rs.html#896-898\">Source</a><a href=\"#method.info\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"paralegal_policy/context/trait.NodeExt.html#tymethod.info\" class=\"fn\">info</a>(self, ctx: &amp;<a class=\"struct\" href=\"paralegal_policy/context/struct.RootContext.html\" title=\"struct paralegal_policy::context::RootContext\">RootContext</a>) -&gt; &amp;<a class=\"struct\" href=\"paralegal_spdg/struct.NodeInfo.html\" title=\"struct paralegal_spdg::NodeInfo\">NodeInfo</a></h4></section></summary><div class='docblock'>Retrieve metadata about a node.</div></details><details class=\"toggle method-toggle\" open><summary><section id=\"method.instruction\" class=\"method trait-impl\"><a class=\"src rightside\" href=\"src/paralegal_policy/context.rs.html#900-902\">Source</a><a href=\"#method.instruction\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"paralegal_policy/context/trait.NodeExt.html#tymethod.instruction\" class=\"fn\">instruction</a>(self, ctx: &amp;<a class=\"struct\" href=\"paralegal_policy/context/struct.RootContext.html\" title=\"struct paralegal_policy::context::RootContext\">RootContext</a>) -&gt; &amp;<a class=\"struct\" href=\"paralegal_spdg/struct.InstructionInfo.html\" title=\"struct paralegal_spdg::InstructionInfo\">InstructionInfo</a></h4></section></summary><div class='docblock'>Retrieve metadata about the instruction executed by a specific node.</div></details><details class=\"toggle method-toggle\" open><summary><section id=\"method.successors\" class=\"method trait-impl\"><a class=\"src rightside\" href=\"src/paralegal_policy/context.rs.html#904-911\">Source</a><a href=\"#method.successors\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"paralegal_policy/context/trait.NodeExt.html#tymethod.successors\" class=\"fn\">successors</a>(\n    self,\n    ctx: &amp;<a class=\"struct\" href=\"paralegal_policy/context/struct.RootContext.html\" title=\"struct paralegal_policy::context::RootContext\">RootContext</a>,\n) -&gt; <a class=\"struct\" href=\"https://doc.rust-lang.org/nightly/alloc/boxed/struct.Box.html\" title=\"struct alloc::boxed::Box\">Box</a>&lt;dyn <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/iter/traits/iterator/trait.Iterator.html\" title=\"trait core::iter::traits::iterator::Iterator\">Iterator</a>&lt;Item = <a class=\"struct\" href=\"paralegal_policy/struct.GlobalNode.html\" title=\"struct paralegal_policy::GlobalNode\">GlobalNode</a>&gt; + '_&gt;</h4></section></summary><div class='docblock'>Return the immediate successors of this node</div></details><details class=\"toggle method-toggle\" open><summary><section id=\"method.predecessors\" class=\"method trait-impl\"><a class=\"src rightside\" href=\"src/paralegal_policy/context.rs.html#913-920\">Source</a><a href=\"#method.predecessors\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"paralegal_policy/context/trait.NodeExt.html#tymethod.predecessors\" class=\"fn\">predecessors</a>(\n    self,\n    ctx: &amp;<a class=\"struct\" href=\"paralegal_policy/context/struct.RootContext.html\" title=\"struct paralegal_policy::context::RootContext\">RootContext</a>,\n) -&gt; <a class=\"struct\" href=\"https://doc.rust-lang.org/nightly/alloc/boxed/struct.Box.html\" title=\"struct alloc::boxed::Box\">Box</a>&lt;dyn <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/iter/traits/iterator/trait.Iterator.html\" title=\"trait core::iter::traits::iterator::Iterator\">Iterator</a>&lt;Item = <a class=\"struct\" href=\"paralegal_policy/struct.GlobalNode.html\" title=\"struct paralegal_policy::GlobalNode\">GlobalNode</a>&gt; + '_&gt;</h4></section></summary><div class='docblock'>Return the immediate predecessors of this node</div></details><details class=\"toggle method-toggle\" open><summary><section id=\"method.get_location\" class=\"method trait-impl\"><a class=\"src rightside\" href=\"src/paralegal_policy/context.rs.html#921-923\">Source</a><a href=\"#method.get_location\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"paralegal_policy/context/trait.NodeExt.html#tymethod.get_location\" class=\"fn\">get_location</a>(self, ctx: &amp;<a class=\"struct\" href=\"paralegal_policy/context/struct.RootContext.html\" title=\"struct paralegal_policy::context::RootContext\">RootContext</a>) -&gt; &amp;<a class=\"struct\" href=\"paralegal_spdg/struct.Span.html\" title=\"struct paralegal_spdg::Span\">Span</a></h4></section></summary><div class='docblock'>Get the span of a node</div></details><details class=\"toggle method-toggle\" open><summary><section id=\"method.shortest_path\" class=\"method trait-impl\"><a class=\"src rightside\" href=\"src/paralegal_policy/context.rs.html#938-972\">Source</a><a href=\"#method.shortest_path\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"paralegal_policy/context/trait.NodeExt.html#tymethod.shortest_path\" class=\"fn\">shortest_path</a>(\n    self,\n    to: Self,\n    ctx: &amp;<a class=\"struct\" href=\"paralegal_policy/context/struct.RootContext.html\" title=\"struct paralegal_policy::context::RootContext\">RootContext</a>,\n    edge_selection: <a class=\"enum\" href=\"paralegal_policy/enum.EdgeSelection.html\" title=\"enum paralegal_policy::EdgeSelection\">EdgeSelection</a>,\n) -&gt; <a class=\"enum\" href=\"https://doc.rust-lang.org/nightly/core/option/enum.Option.html\" title=\"enum core::option::Option\">Option</a>&lt;<a class=\"struct\" href=\"https://doc.rust-lang.org/nightly/alloc/boxed/struct.Box.html\" title=\"struct alloc::boxed::Box\">Box</a>&lt;[Self]&gt;&gt;</h4></section></summary><span class=\"item-info\"><div class=\"stab deprecated\"><span class=\"emoji\">👎</span><span>Deprecated: This function is known to be buggy at the moment. Only use for debugging, don’t rely on it for policy correctness.</span></div></span><div class='docblock'>The shortest path between this and a target node</div></details></div></details>","NodeExt","paralegal_policy::context::MarkableId"],["<details class=\"toggle implementors-toggle\" open><summary><section id=\"impl-PartialEq-for-GlobalNode\" class=\"impl\"><a class=\"src rightside\" href=\"src/paralegal_spdg/lib.rs.html#622\">Source</a><a href=\"#impl-PartialEq-for-GlobalNode\" class=\"anchor\">§</a><h3 class=\"code-header\">impl <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/cmp/trait.PartialEq.html\" title=\"trait core::cmp::PartialEq\">PartialEq</a> for <a class=\"struct\" href=\"paralegal_policy/struct.GlobalNode.html\" title=\"struct paralegal_policy::GlobalNode\">GlobalNode</a></h3></section></summary><div class=\"impl-items\"><details class=\"toggle method-toggle\" open><summary><section id=\"method.eq\" class=\"method trait-impl\"><a class=\"src rightside\" href=\"src/paralegal_spdg/lib.rs.html#622\">Source</a><a href=\"#method.eq\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"https://doc.rust-lang.org/nightly/core/cmp/trait.PartialEq.html#tymethod.eq\" class=\"fn\">eq</a>(&amp;self, other: &amp;<a class=\"struct\" href=\"paralegal_policy/struct.GlobalNode.html\" title=\"struct paralegal_policy::GlobalNode\">GlobalNode</a>) -&gt; <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.bool.html\">bool</a></h4></section></summary><div class='docblock'>Tests for <code>self</code> and <code>other</code> values to be equal, and is used by <code>==</code>.</div></details><details class=\"toggle method-toggle\" open><summary><section id=\"method.ne\" class=\"method trait-impl\"><span class=\"rightside\"><span class=\"since\" title=\"Stable since Rust version 1.0.0\">1.0.0</span> · <a class=\"src\" href=\"https://doc.rust-lang.org/nightly/src/core/cmp.rs.html#261\">Source</a></span><a href=\"#method.ne\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"https://doc.rust-lang.org/nightly/core/cmp/trait.PartialEq.html#method.ne\" class=\"fn\">ne</a>(&amp;self, other: <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.reference.html\">&amp;Rhs</a>) -&gt; <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.bool.html\">bool</a></h4></section></summary><div class='docblock'>Tests for <code>!=</code>. The default implementation is almost always sufficient,\nand should not be overridden without very good reason.</div></details></div></details>","PartialEq","paralegal_policy::context::MarkableId"],["<section id=\"impl-Copy-for-GlobalNode\" class=\"impl\"><a class=\"src rightside\" href=\"src/paralegal_spdg/lib.rs.html#622\">Source</a><a href=\"#impl-Copy-for-GlobalNode\" class=\"anchor\">§</a><h3 class=\"code-header\">impl <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/marker/trait.Copy.html\" title=\"trait core::marker::Copy\">Copy</a> for <a class=\"struct\" href=\"paralegal_policy/struct.GlobalNode.html\" title=\"struct paralegal_policy::GlobalNode\">GlobalNode</a></h3></section>","Copy","paralegal_policy::context::MarkableId"],["<section id=\"impl-Eq-for-GlobalNode\" class=\"impl\"><a class=\"src rightside\" href=\"src/paralegal_spdg/lib.rs.html#622\">Source</a><a href=\"#impl-Eq-for-GlobalNode\" class=\"anchor\">§</a><h3 class=\"code-header\">impl <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/cmp/trait.Eq.html\" title=\"trait core::cmp::Eq\">Eq</a> for <a class=\"struct\" href=\"paralegal_policy/struct.GlobalNode.html\" title=\"struct paralegal_policy::GlobalNode\">GlobalNode</a></h3></section>","Eq","paralegal_policy::context::MarkableId"],["<section id=\"impl-Sealed-for-GlobalNode\" class=\"impl\"><a class=\"src rightside\" href=\"src/paralegal_policy/context.rs.html#834\">Source</a><a href=\"#impl-Sealed-for-GlobalNode\" class=\"anchor\">§</a><h3 class=\"code-header\">impl <a class=\"trait\" href=\"paralegal_policy/context/private/trait.Sealed.html\" title=\"trait paralegal_policy::context::private::Sealed\">Sealed</a> for <a class=\"struct\" href=\"paralegal_policy/struct.GlobalNode.html\" title=\"struct paralegal_policy::GlobalNode\">GlobalNode</a></h3></section>","Sealed","paralegal_policy::context::MarkableId"],["<section id=\"impl-StructuralPartialEq-for-GlobalNode\" class=\"impl\"><a class=\"src rightside\" href=\"src/paralegal_spdg/lib.rs.html#622\">Source</a><a href=\"#impl-StructuralPartialEq-for-GlobalNode\" class=\"anchor\">§</a><h3 class=\"code-header\">impl <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/marker/trait.StructuralPartialEq.html\" title=\"trait core::marker::StructuralPartialEq\">StructuralPartialEq</a> for <a class=\"struct\" href=\"paralegal_policy/struct.GlobalNode.html\" title=\"struct paralegal_policy::GlobalNode\">GlobalNode</a></h3></section>","StructuralPartialEq","paralegal_policy::context::MarkableId"]]]]);
    if (window.register_type_impls) {
        window.register_type_impls(type_impls);
    } else {
        window.pending_type_impls = type_impls;
    }
})()
//{"start":55,"fragment_lengths":[32454]}