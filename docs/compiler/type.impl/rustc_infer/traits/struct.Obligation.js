(function() {
    var type_impls = Object.fromEntries([["rustc_infer",[["<details class=\"toggle implementors-toggle\" open><summary><section id=\"impl-Clone-for-Obligation%3C'tcx,+T%3E\" class=\"impl\"><a class=\"src rightside\" href=\"src/rustc_infer/traits/mod.rs.html#38\">Source</a><a href=\"#impl-Clone-for-Obligation%3C'tcx,+T%3E\" class=\"anchor\">§</a><h3 class=\"code-header\">impl&lt;'tcx, T: <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/clone/trait.Clone.html\" title=\"trait core::clone::Clone\">Clone</a>&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/clone/trait.Clone.html\" title=\"trait core::clone::Clone\">Clone</a> for <a class=\"struct\" href=\"rustc_infer/traits/struct.Obligation.html\" title=\"struct rustc_infer::traits::Obligation\">Obligation</a>&lt;'tcx, T&gt;</h3></section></summary><div class=\"impl-items\"><details class=\"toggle method-toggle\" open><summary><section id=\"method.clone\" class=\"method trait-impl\"><a class=\"src rightside\" href=\"src/rustc_infer/traits/mod.rs.html#38\">Source</a><a href=\"#method.clone\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"https://doc.rust-lang.org/nightly/core/clone/trait.Clone.html#tymethod.clone\" class=\"fn\">clone</a>(&amp;self) -&gt; <a class=\"struct\" href=\"rustc_infer/traits/struct.Obligation.html\" title=\"struct rustc_infer::traits::Obligation\">Obligation</a>&lt;'tcx, T&gt;</h4></section></summary><div class='docblock'>Returns a copy of the value. <a href=\"https://doc.rust-lang.org/nightly/core/clone/trait.Clone.html#tymethod.clone\">Read more</a></div></details><details class=\"toggle method-toggle\" open><summary><section id=\"method.clone_from\" class=\"method trait-impl\"><span class=\"rightside\"><span class=\"since\" title=\"Stable since Rust version 1.0.0\">1.0.0</span> · <a class=\"src\" href=\"https://doc.rust-lang.org/nightly/src/core/clone.rs.html#174\">Source</a></span><a href=\"#method.clone_from\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"https://doc.rust-lang.org/nightly/core/clone/trait.Clone.html#method.clone_from\" class=\"fn\">clone_from</a>(&amp;mut self, source: &amp;Self)</h4></section></summary><div class='docblock'>Performs copy-assignment from <code>source</code>. <a href=\"https://doc.rust-lang.org/nightly/core/clone/trait.Clone.html#method.clone_from\">Read more</a></div></details></div></details>","Clone","rustc_infer::traits::PredicateObligation","rustc_infer::traits::TraitObligation","rustc_infer::traits::PolyTraitObligation"],["<details class=\"toggle implementors-toggle\" open><summary><section id=\"impl-Debug-for-Obligation%3C'tcx,+O%3E\" class=\"impl\"><a class=\"src rightside\" href=\"src/rustc_infer/traits/structural_impls.rs.html#19-31\">Source</a><a href=\"#impl-Debug-for-Obligation%3C'tcx,+O%3E\" class=\"anchor\">§</a><h3 class=\"code-header\">impl&lt;'tcx, O: <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/fmt/trait.Debug.html\" title=\"trait core::fmt::Debug\">Debug</a>&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/fmt/trait.Debug.html\" title=\"trait core::fmt::Debug\">Debug</a> for <a class=\"struct\" href=\"rustc_infer/traits/struct.Obligation.html\" title=\"struct rustc_infer::traits::Obligation\">Obligation</a>&lt;'tcx, O&gt;</h3></section></summary><div class=\"impl-items\"><details class=\"toggle method-toggle\" open><summary><section id=\"method.fmt\" class=\"method trait-impl\"><a class=\"src rightside\" href=\"src/rustc_infer/traits/structural_impls.rs.html#20-30\">Source</a><a href=\"#method.fmt\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"https://doc.rust-lang.org/nightly/core/fmt/trait.Debug.html#tymethod.fmt\" class=\"fn\">fmt</a>(&amp;self, f: &amp;mut <a class=\"struct\" href=\"https://doc.rust-lang.org/nightly/core/fmt/struct.Formatter.html\" title=\"struct core::fmt::Formatter\">Formatter</a>&lt;'_&gt;) -&gt; <a class=\"type\" href=\"https://doc.rust-lang.org/nightly/core/fmt/type.Result.html\" title=\"type core::fmt::Result\">Result</a></h4></section></summary><div class='docblock'>Formats the value using the given formatter. <a href=\"https://doc.rust-lang.org/nightly/core/fmt/trait.Debug.html#tymethod.fmt\">Read more</a></div></details></div></details>","Debug","rustc_infer::traits::PredicateObligation","rustc_infer::traits::TraitObligation","rustc_infer::traits::PolyTraitObligation"],["<details class=\"toggle implementors-toggle\" open><summary><section id=\"impl-Hash-for-Obligation%3C'_,+T%3E\" class=\"impl\"><a class=\"src rightside\" href=\"src/rustc_infer/traits/mod.rs.html#70-76\">Source</a><a href=\"#impl-Hash-for-Obligation%3C'_,+T%3E\" class=\"anchor\">§</a><h3 class=\"code-header\">impl&lt;T: <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/hash/trait.Hash.html\" title=\"trait core::hash::Hash\">Hash</a>&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/hash/trait.Hash.html\" title=\"trait core::hash::Hash\">Hash</a> for <a class=\"struct\" href=\"rustc_infer/traits/struct.Obligation.html\" title=\"struct rustc_infer::traits::Obligation\">Obligation</a>&lt;'_, T&gt;</h3></section></summary><div class=\"impl-items\"><details class=\"toggle method-toggle\" open><summary><section id=\"method.hash\" class=\"method trait-impl\"><a class=\"src rightside\" href=\"src/rustc_infer/traits/mod.rs.html#71-75\">Source</a><a href=\"#method.hash\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"https://doc.rust-lang.org/nightly/core/hash/trait.Hash.html#tymethod.hash\" class=\"fn\">hash</a>&lt;H: <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/hash/trait.Hasher.html\" title=\"trait core::hash::Hasher\">Hasher</a>&gt;(&amp;self, state: <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.reference.html\">&amp;mut H</a>)</h4></section></summary><div class='docblock'>Feeds this value into the given <a href=\"https://doc.rust-lang.org/nightly/core/hash/trait.Hasher.html\" title=\"trait core::hash::Hasher\"><code>Hasher</code></a>. <a href=\"https://doc.rust-lang.org/nightly/core/hash/trait.Hash.html#tymethod.hash\">Read more</a></div></details><details class=\"toggle method-toggle\" open><summary><section id=\"method.hash_slice\" class=\"method trait-impl\"><span class=\"rightside\"><span class=\"since\" title=\"Stable since Rust version 1.3.0\">1.3.0</span> · <a class=\"src\" href=\"https://doc.rust-lang.org/nightly/src/core/hash/mod.rs.html#235-237\">Source</a></span><a href=\"#method.hash_slice\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"https://doc.rust-lang.org/nightly/core/hash/trait.Hash.html#method.hash_slice\" class=\"fn\">hash_slice</a>&lt;H&gt;(data: &amp;[Self], state: <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.reference.html\">&amp;mut H</a>)<div class=\"where\">where\n    H: <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/hash/trait.Hasher.html\" title=\"trait core::hash::Hasher\">Hasher</a>,\n    Self: <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/marker/trait.Sized.html\" title=\"trait core::marker::Sized\">Sized</a>,</div></h4></section></summary><div class='docblock'>Feeds a slice of this type into the given <a href=\"https://doc.rust-lang.org/nightly/core/hash/trait.Hasher.html\" title=\"trait core::hash::Hasher\"><code>Hasher</code></a>. <a href=\"https://doc.rust-lang.org/nightly/core/hash/trait.Hash.html#method.hash_slice\">Read more</a></div></details></div></details>","Hash","rustc_infer::traits::PredicateObligation","rustc_infer::traits::TraitObligation","rustc_infer::traits::PolyTraitObligation"],["<details class=\"toggle implementors-toggle\" open><summary><section id=\"impl-Obligation%3C'tcx,+O%3E\" class=\"impl\"><a class=\"src rightside\" href=\"src/rustc_infer/traits/mod.rs.html#124-170\">Source</a><a href=\"#impl-Obligation%3C'tcx,+O%3E\" class=\"anchor\">§</a><h3 class=\"code-header\">impl&lt;'tcx, O&gt; <a class=\"struct\" href=\"rustc_infer/traits/struct.Obligation.html\" title=\"struct rustc_infer::traits::Obligation\">Obligation</a>&lt;'tcx, O&gt;</h3></section></summary><div class=\"impl-items\"><section id=\"method.new\" class=\"method\"><a class=\"src rightside\" href=\"src/rustc_infer/traits/mod.rs.html#125-132\">Source</a><h4 class=\"code-header\">pub fn <a href=\"rustc_infer/traits/struct.Obligation.html#tymethod.new\" class=\"fn\">new</a>(\n    tcx: <a class=\"struct\" href=\"rustc_middle/ty/context/struct.TyCtxt.html\" title=\"struct rustc_middle::ty::context::TyCtxt\">TyCtxt</a>&lt;'tcx&gt;,\n    cause: <a class=\"struct\" href=\"rustc_infer/traits/struct.ObligationCause.html\" title=\"struct rustc_infer::traits::ObligationCause\">ObligationCause</a>&lt;'tcx&gt;,\n    param_env: <a class=\"struct\" href=\"rustc_middle/ty/struct.ParamEnv.html\" title=\"struct rustc_middle::ty::ParamEnv\">ParamEnv</a>&lt;'tcx&gt;,\n    predicate: impl <a class=\"trait\" href=\"rustc_infer/infer/canonical/ir/trait.Upcast.html\" title=\"trait rustc_infer::infer::canonical::ir::Upcast\">Upcast</a>&lt;<a class=\"struct\" href=\"rustc_middle/ty/context/struct.TyCtxt.html\" title=\"struct rustc_middle::ty::context::TyCtxt\">TyCtxt</a>&lt;'tcx&gt;, O&gt;,\n) -&gt; <a class=\"struct\" href=\"rustc_infer/traits/struct.Obligation.html\" title=\"struct rustc_infer::traits::Obligation\">Obligation</a>&lt;'tcx, O&gt;</h4></section><details class=\"toggle method-toggle\" open><summary><section id=\"method.set_depth_from_parent\" class=\"method\"><a class=\"src rightside\" href=\"src/rustc_infer/traits/mod.rs.html#138-140\">Source</a><h4 class=\"code-header\">pub fn <a href=\"rustc_infer/traits/struct.Obligation.html#tymethod.set_depth_from_parent\" class=\"fn\">set_depth_from_parent</a>(&amp;mut self, parent_depth: <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.usize.html\">usize</a>)</h4></section></summary><div class=\"docblock\"><p>We often create nested obligations without setting the correct depth.</p>\n<p>To deal with this evaluate and fulfill explicitly update the depth\nof nested obligations using this function.</p>\n</div></details><section id=\"method.with_depth\" class=\"method\"><a class=\"src rightside\" href=\"src/rustc_infer/traits/mod.rs.html#142-151\">Source</a><h4 class=\"code-header\">pub fn <a href=\"rustc_infer/traits/struct.Obligation.html#tymethod.with_depth\" class=\"fn\">with_depth</a>(\n    tcx: <a class=\"struct\" href=\"rustc_middle/ty/context/struct.TyCtxt.html\" title=\"struct rustc_middle::ty::context::TyCtxt\">TyCtxt</a>&lt;'tcx&gt;,\n    cause: <a class=\"struct\" href=\"rustc_infer/traits/struct.ObligationCause.html\" title=\"struct rustc_infer::traits::ObligationCause\">ObligationCause</a>&lt;'tcx&gt;,\n    recursion_depth: <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.usize.html\">usize</a>,\n    param_env: <a class=\"struct\" href=\"rustc_middle/ty/struct.ParamEnv.html\" title=\"struct rustc_middle::ty::ParamEnv\">ParamEnv</a>&lt;'tcx&gt;,\n    predicate: impl <a class=\"trait\" href=\"rustc_infer/infer/canonical/ir/trait.Upcast.html\" title=\"trait rustc_infer::infer::canonical::ir::Upcast\">Upcast</a>&lt;<a class=\"struct\" href=\"rustc_middle/ty/context/struct.TyCtxt.html\" title=\"struct rustc_middle::ty::context::TyCtxt\">TyCtxt</a>&lt;'tcx&gt;, O&gt;,\n) -&gt; <a class=\"struct\" href=\"rustc_infer/traits/struct.Obligation.html\" title=\"struct rustc_infer::traits::Obligation\">Obligation</a>&lt;'tcx, O&gt;</h4></section><section id=\"method.misc\" class=\"method\"><a class=\"src rightside\" href=\"src/rustc_infer/traits/mod.rs.html#153-161\">Source</a><h4 class=\"code-header\">pub fn <a href=\"rustc_infer/traits/struct.Obligation.html#tymethod.misc\" class=\"fn\">misc</a>(\n    tcx: <a class=\"struct\" href=\"rustc_middle/ty/context/struct.TyCtxt.html\" title=\"struct rustc_middle::ty::context::TyCtxt\">TyCtxt</a>&lt;'tcx&gt;,\n    span: <a class=\"struct\" href=\"rustc_span/span_encoding/struct.Span.html\" title=\"struct rustc_span::span_encoding::Span\">Span</a>,\n    body_id: <a class=\"struct\" href=\"rustc_span/def_id/struct.LocalDefId.html\" title=\"struct rustc_span::def_id::LocalDefId\">LocalDefId</a>,\n    param_env: <a class=\"struct\" href=\"rustc_middle/ty/struct.ParamEnv.html\" title=\"struct rustc_middle::ty::ParamEnv\">ParamEnv</a>&lt;'tcx&gt;,\n    trait_ref: impl <a class=\"trait\" href=\"rustc_infer/infer/canonical/ir/trait.Upcast.html\" title=\"trait rustc_infer::infer::canonical::ir::Upcast\">Upcast</a>&lt;<a class=\"struct\" href=\"rustc_middle/ty/context/struct.TyCtxt.html\" title=\"struct rustc_middle::ty::context::TyCtxt\">TyCtxt</a>&lt;'tcx&gt;, O&gt;,\n) -&gt; <a class=\"struct\" href=\"rustc_infer/traits/struct.Obligation.html\" title=\"struct rustc_infer::traits::Obligation\">Obligation</a>&lt;'tcx, O&gt;</h4></section><section id=\"method.with\" class=\"method\"><a class=\"src rightside\" href=\"src/rustc_infer/traits/mod.rs.html#163-169\">Source</a><h4 class=\"code-header\">pub fn <a href=\"rustc_infer/traits/struct.Obligation.html#tymethod.with\" class=\"fn\">with</a>&lt;P&gt;(\n    &amp;self,\n    tcx: <a class=\"struct\" href=\"rustc_middle/ty/context/struct.TyCtxt.html\" title=\"struct rustc_middle::ty::context::TyCtxt\">TyCtxt</a>&lt;'tcx&gt;,\n    value: impl <a class=\"trait\" href=\"rustc_infer/infer/canonical/ir/trait.Upcast.html\" title=\"trait rustc_infer::infer::canonical::ir::Upcast\">Upcast</a>&lt;<a class=\"struct\" href=\"rustc_middle/ty/context/struct.TyCtxt.html\" title=\"struct rustc_middle::ty::context::TyCtxt\">TyCtxt</a>&lt;'tcx&gt;, P&gt;,\n) -&gt; <a class=\"struct\" href=\"rustc_infer/traits/struct.Obligation.html\" title=\"struct rustc_infer::traits::Obligation\">Obligation</a>&lt;'tcx, P&gt;</h4></section></div></details>",0,"rustc_infer::traits::PredicateObligation","rustc_infer::traits::TraitObligation","rustc_infer::traits::PolyTraitObligation"],["<details class=\"toggle implementors-toggle\" open><summary><section id=\"impl-PartialEq-for-Obligation%3C'tcx,+T%3E\" class=\"impl\"><a class=\"src rightside\" href=\"src/rustc_infer/traits/mod.rs.html#57-66\">Source</a><a href=\"#impl-PartialEq-for-Obligation%3C'tcx,+T%3E\" class=\"anchor\">§</a><h3 class=\"code-header\">impl&lt;'tcx, T: <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/cmp/trait.PartialEq.html\" title=\"trait core::cmp::PartialEq\">PartialEq</a>&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/cmp/trait.PartialEq.html\" title=\"trait core::cmp::PartialEq\">PartialEq</a> for <a class=\"struct\" href=\"rustc_infer/traits/struct.Obligation.html\" title=\"struct rustc_infer::traits::Obligation\">Obligation</a>&lt;'tcx, T&gt;</h3></section></summary><div class=\"impl-items\"><details class=\"toggle method-toggle\" open><summary><section id=\"method.eq\" class=\"method trait-impl\"><a class=\"src rightside\" href=\"src/rustc_infer/traits/mod.rs.html#59-65\">Source</a><a href=\"#method.eq\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"https://doc.rust-lang.org/nightly/core/cmp/trait.PartialEq.html#tymethod.eq\" class=\"fn\">eq</a>(&amp;self, other: &amp;<a class=\"struct\" href=\"rustc_infer/traits/struct.Obligation.html\" title=\"struct rustc_infer::traits::Obligation\">Obligation</a>&lt;'tcx, T&gt;) -&gt; <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.bool.html\">bool</a></h4></section></summary><div class='docblock'>Tests for <code>self</code> and <code>other</code> values to be equal, and is used by <code>==</code>.</div></details><details class=\"toggle method-toggle\" open><summary><section id=\"method.ne\" class=\"method trait-impl\"><span class=\"rightside\"><span class=\"since\" title=\"Stable since Rust version 1.0.0\">1.0.0</span> · <a class=\"src\" href=\"https://doc.rust-lang.org/nightly/src/core/cmp.rs.html#261\">Source</a></span><a href=\"#method.ne\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"https://doc.rust-lang.org/nightly/core/cmp/trait.PartialEq.html#method.ne\" class=\"fn\">ne</a>(&amp;self, other: <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.reference.html\">&amp;Rhs</a>) -&gt; <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.bool.html\">bool</a></h4></section></summary><div class='docblock'>Tests for <code>!=</code>. The default implementation is almost always sufficient,\nand should not be overridden without very good reason.</div></details></div></details>","PartialEq","rustc_infer::traits::PredicateObligation","rustc_infer::traits::TraitObligation","rustc_infer::traits::PolyTraitObligation"],["<details class=\"toggle implementors-toggle\" open><summary><section id=\"impl-TypeFoldable%3CTyCtxt%3C'tcx%3E%3E-for-Obligation%3C'tcx,+O%3E\" class=\"impl\"><a class=\"src rightside\" href=\"src/rustc_infer/traits/structural_impls.rs.html#42-56\">Source</a><a href=\"#impl-TypeFoldable%3CTyCtxt%3C'tcx%3E%3E-for-Obligation%3C'tcx,+O%3E\" class=\"anchor\">§</a><h3 class=\"code-header\">impl&lt;'tcx, O: <a class=\"trait\" href=\"rustc_infer/infer/canonical/ir/fold/trait.TypeFoldable.html\" title=\"trait rustc_infer::infer::canonical::ir::fold::TypeFoldable\">TypeFoldable</a>&lt;<a class=\"struct\" href=\"rustc_middle/ty/context/struct.TyCtxt.html\" title=\"struct rustc_middle::ty::context::TyCtxt\">TyCtxt</a>&lt;'tcx&gt;&gt;&gt; <a class=\"trait\" href=\"rustc_infer/infer/canonical/ir/fold/trait.TypeFoldable.html\" title=\"trait rustc_infer::infer::canonical::ir::fold::TypeFoldable\">TypeFoldable</a>&lt;<a class=\"struct\" href=\"rustc_middle/ty/context/struct.TyCtxt.html\" title=\"struct rustc_middle::ty::context::TyCtxt\">TyCtxt</a>&lt;'tcx&gt;&gt; for <a class=\"struct\" href=\"rustc_infer/traits/struct.Obligation.html\" title=\"struct rustc_infer::traits::Obligation\">Obligation</a>&lt;'tcx, O&gt;</h3></section></summary><div class=\"impl-items\"><details class=\"toggle method-toggle\" open><summary><section id=\"method.try_fold_with\" class=\"method trait-impl\"><a class=\"src rightside\" href=\"src/rustc_infer/traits/structural_impls.rs.html#45-55\">Source</a><a href=\"#method.try_fold_with\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"rustc_infer/infer/canonical/ir/fold/trait.TypeFoldable.html#tymethod.try_fold_with\" class=\"fn\">try_fold_with</a>&lt;F: <a class=\"trait\" href=\"rustc_infer/infer/canonical/ir/fold/trait.FallibleTypeFolder.html\" title=\"trait rustc_infer::infer::canonical::ir::fold::FallibleTypeFolder\">FallibleTypeFolder</a>&lt;<a class=\"struct\" href=\"rustc_middle/ty/context/struct.TyCtxt.html\" title=\"struct rustc_middle::ty::context::TyCtxt\">TyCtxt</a>&lt;'tcx&gt;&gt;&gt;(\n    self,\n    folder: <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.reference.html\">&amp;mut F</a>,\n) -&gt; <a class=\"enum\" href=\"https://doc.rust-lang.org/nightly/core/result/enum.Result.html\" title=\"enum core::result::Result\">Result</a>&lt;Self, F::<a class=\"associatedtype\" href=\"rustc_infer/infer/canonical/ir/fold/trait.FallibleTypeFolder.html#associatedtype.Error\" title=\"type rustc_infer::infer::canonical::ir::fold::FallibleTypeFolder::Error\">Error</a>&gt;</h4></section></summary><div class='docblock'>The entry point for folding. To fold a value <code>t</code> with a folder <code>f</code>\ncall: <code>t.try_fold_with(f)</code>. <a href=\"rustc_infer/infer/canonical/ir/fold/trait.TypeFoldable.html#tymethod.try_fold_with\">Read more</a></div></details><details class=\"toggle method-toggle\" open><summary><section id=\"method.fold_with\" class=\"method trait-impl\"><a class=\"src rightside\" href=\"src/rustc_type_ir/fold.rs.html#92\">Source</a><a href=\"#method.fold_with\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"rustc_infer/infer/canonical/ir/fold/trait.TypeFoldable.html#method.fold_with\" class=\"fn\">fold_with</a>&lt;F&gt;(self, folder: <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.reference.html\">&amp;mut F</a>) -&gt; Self<div class=\"where\">where\n    F: <a class=\"trait\" href=\"rustc_infer/infer/canonical/ir/fold/trait.TypeFolder.html\" title=\"trait rustc_infer::infer::canonical::ir::fold::TypeFolder\">TypeFolder</a>&lt;I&gt;,</div></h4></section></summary><div class='docblock'>A convenient alternative to <code>try_fold_with</code> for use with infallible\nfolders. Do not override this method, to ensure coherence with\n<code>try_fold_with</code>.</div></details></div></details>","TypeFoldable<TyCtxt<'tcx>>","rustc_infer::traits::PredicateObligation","rustc_infer::traits::TraitObligation","rustc_infer::traits::PolyTraitObligation"],["<details class=\"toggle implementors-toggle\" open><summary><section id=\"impl-TypeVisitable%3CTyCtxt%3C'tcx%3E%3E-for-Obligation%3C'tcx,+O%3E\" class=\"impl\"><a class=\"src rightside\" href=\"src/rustc_infer/traits/structural_impls.rs.html#58-65\">Source</a><a href=\"#impl-TypeVisitable%3CTyCtxt%3C'tcx%3E%3E-for-Obligation%3C'tcx,+O%3E\" class=\"anchor\">§</a><h3 class=\"code-header\">impl&lt;'tcx, O: <a class=\"trait\" href=\"rustc_infer/infer/canonical/ir/visit/trait.TypeVisitable.html\" title=\"trait rustc_infer::infer::canonical::ir::visit::TypeVisitable\">TypeVisitable</a>&lt;<a class=\"struct\" href=\"rustc_middle/ty/context/struct.TyCtxt.html\" title=\"struct rustc_middle::ty::context::TyCtxt\">TyCtxt</a>&lt;'tcx&gt;&gt;&gt; <a class=\"trait\" href=\"rustc_infer/infer/canonical/ir/visit/trait.TypeVisitable.html\" title=\"trait rustc_infer::infer::canonical::ir::visit::TypeVisitable\">TypeVisitable</a>&lt;<a class=\"struct\" href=\"rustc_middle/ty/context/struct.TyCtxt.html\" title=\"struct rustc_middle::ty::context::TyCtxt\">TyCtxt</a>&lt;'tcx&gt;&gt; for <a class=\"struct\" href=\"rustc_infer/traits/struct.Obligation.html\" title=\"struct rustc_infer::traits::Obligation\">Obligation</a>&lt;'tcx, O&gt;</h3></section></summary><div class=\"impl-items\"><details class=\"toggle method-toggle\" open><summary><section id=\"method.visit_with\" class=\"method trait-impl\"><a class=\"src rightside\" href=\"src/rustc_infer/traits/structural_impls.rs.html#61-64\">Source</a><a href=\"#method.visit_with\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"rustc_infer/infer/canonical/ir/visit/trait.TypeVisitable.html#tymethod.visit_with\" class=\"fn\">visit_with</a>&lt;V: <a class=\"trait\" href=\"rustc_infer/infer/canonical/ir/visit/trait.TypeVisitor.html\" title=\"trait rustc_infer::infer::canonical::ir::visit::TypeVisitor\">TypeVisitor</a>&lt;<a class=\"struct\" href=\"rustc_middle/ty/context/struct.TyCtxt.html\" title=\"struct rustc_middle::ty::context::TyCtxt\">TyCtxt</a>&lt;'tcx&gt;&gt;&gt;(&amp;self, visitor: <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.reference.html\">&amp;mut V</a>) -&gt; V::<a class=\"associatedtype\" href=\"rustc_infer/infer/canonical/ir/visit/trait.TypeVisitor.html#associatedtype.Result\" title=\"type rustc_infer::infer::canonical::ir::visit::TypeVisitor::Result\">Result</a></h4></section></summary><div class='docblock'>The entry point for visiting. To visit a value <code>t</code> with a visitor <code>v</code>\ncall: <code>t.visit_with(v)</code>. <a href=\"rustc_infer/infer/canonical/ir/visit/trait.TypeVisitable.html#tymethod.visit_with\">Read more</a></div></details></div></details>","TypeVisitable<TyCtxt<'tcx>>","rustc_infer::traits::PredicateObligation","rustc_infer::traits::TraitObligation","rustc_infer::traits::PolyTraitObligation"],["<section id=\"impl-Eq-for-Obligation%3C'_,+T%3E\" class=\"impl\"><a class=\"src rightside\" href=\"src/rustc_infer/traits/mod.rs.html#68\">Source</a><a href=\"#impl-Eq-for-Obligation%3C'_,+T%3E\" class=\"anchor\">§</a><h3 class=\"code-header\">impl&lt;T: <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/cmp/trait.Eq.html\" title=\"trait core::cmp::Eq\">Eq</a>&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/cmp/trait.Eq.html\" title=\"trait core::cmp::Eq\">Eq</a> for <a class=\"struct\" href=\"rustc_infer/traits/struct.Obligation.html\" title=\"struct rustc_infer::traits::Obligation\">Obligation</a>&lt;'_, T&gt;</h3></section>","Eq","rustc_infer::traits::PredicateObligation","rustc_infer::traits::TraitObligation","rustc_infer::traits::PolyTraitObligation"]]]]);
    if (window.register_type_impls) {
        window.register_type_impls(type_impls);
    } else {
        window.pending_type_impls = type_impls;
    }
})()
//{"start":55,"fragment_lengths":[24436]}