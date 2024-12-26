(function() {
    var type_impls = Object.fromEntries([["rustc_hir_typeck",[["<details class=\"toggle implementors-toggle\" open><summary><section id=\"impl-CoerceMany%3C'tcx,+'exprs,+E%3E\" class=\"impl\"><a class=\"src rightside\" href=\"src/rustc_hir_typeck/coercion.rs.html#1453-2030\">Source</a><a href=\"#impl-CoerceMany%3C'tcx,+'exprs,+E%3E\" class=\"anchor\">§</a><h3 class=\"code-header\">impl&lt;'tcx, 'exprs, E: <a class=\"trait\" href=\"rustc_hir_typeck/coercion/trait.AsCoercionSite.html\" title=\"trait rustc_hir_typeck::coercion::AsCoercionSite\">AsCoercionSite</a>&gt; <a class=\"struct\" href=\"rustc_hir_typeck/coercion/struct.CoerceMany.html\" title=\"struct rustc_hir_typeck::coercion::CoerceMany\">CoerceMany</a>&lt;'tcx, 'exprs, E&gt;</h3></section></summary><div class=\"impl-items\"><details class=\"toggle method-toggle\" open><summary><section id=\"method.new\" class=\"method\"><a class=\"src rightside\" href=\"src/rustc_hir_typeck/coercion.rs.html#1457-1459\">Source</a><h4 class=\"code-header\">pub(crate) fn <a href=\"rustc_hir_typeck/coercion/struct.CoerceMany.html#tymethod.new\" class=\"fn\">new</a>(expected_ty: <a class=\"struct\" href=\"rustc_middle/ty/struct.Ty.html\" title=\"struct rustc_middle::ty::Ty\">Ty</a>&lt;'tcx&gt;) -&gt; Self</h4></section></summary><div class=\"docblock\"><p>The usual case; collect the set of expressions dynamically.\nIf the full set of coercion sites is known before hand,\nconsider <code>with_coercion_sites()</code> instead to avoid allocation.</p>\n</div></details><details class=\"toggle method-toggle\" open><summary><section id=\"method.with_coercion_sites\" class=\"method\"><a class=\"src rightside\" href=\"src/rustc_hir_typeck/coercion.rs.html#1466-1468\">Source</a><h4 class=\"code-header\">pub(crate) fn <a href=\"rustc_hir_typeck/coercion/struct.CoerceMany.html#tymethod.with_coercion_sites\" class=\"fn\">with_coercion_sites</a>(\n    expected_ty: <a class=\"struct\" href=\"rustc_middle/ty/struct.Ty.html\" title=\"struct rustc_middle::ty::Ty\">Ty</a>&lt;'tcx&gt;,\n    coercion_sites: &amp;'exprs <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.slice.html\">[E]</a>,\n) -&gt; Self</h4></section></summary><div class=\"docblock\"><p>As an optimization, you can create a <code>CoerceMany</code> with a\npreexisting slice of expressions. In this case, you are\nexpected to pass each element in the slice to <code>coerce(...)</code> in\norder. This is used with arrays in particular to avoid\nneedlessly cloning the slice.</p>\n</div></details><section id=\"method.make\" class=\"method\"><a class=\"src rightside\" href=\"src/rustc_hir_typeck/coercion.rs.html#1470-1472\">Source</a><h4 class=\"code-header\">fn <a href=\"rustc_hir_typeck/coercion/struct.CoerceMany.html#tymethod.make\" class=\"fn\">make</a>(\n    expected_ty: <a class=\"struct\" href=\"rustc_middle/ty/struct.Ty.html\" title=\"struct rustc_middle::ty::Ty\">Ty</a>&lt;'tcx&gt;,\n    expressions: <a class=\"enum\" href=\"rustc_hir_typeck/coercion/enum.Expressions.html\" title=\"enum rustc_hir_typeck::coercion::Expressions\">Expressions</a>&lt;'tcx, 'exprs, E&gt;,\n) -&gt; Self</h4></section><details class=\"toggle method-toggle\" open><summary><section id=\"method.expected_ty\" class=\"method\"><a class=\"src rightside\" href=\"src/rustc_hir_typeck/coercion.rs.html#1482-1484\">Source</a><h4 class=\"code-header\">pub(crate) fn <a href=\"rustc_hir_typeck/coercion/struct.CoerceMany.html#tymethod.expected_ty\" class=\"fn\">expected_ty</a>(&amp;self) -&gt; <a class=\"struct\" href=\"rustc_middle/ty/struct.Ty.html\" title=\"struct rustc_middle::ty::Ty\">Ty</a>&lt;'tcx&gt;</h4></section></summary><div class=\"docblock\"><p>Returns the “expected type” with which this coercion was\nconstructed. This represents the “downward propagated” type\nthat was given to us at the start of typing whatever construct\nwe are typing (e.g., the match expression).</p>\n<p>Typically, this is used as the expected type when\ntype-checking each of the alternative expressions whose types\nwe are trying to merge.</p>\n</div></details><details class=\"toggle method-toggle\" open><summary><section id=\"method.merged_ty\" class=\"method\"><a class=\"src rightside\" href=\"src/rustc_hir_typeck/coercion.rs.html#1490-1492\">Source</a><h4 class=\"code-header\">pub(crate) fn <a href=\"rustc_hir_typeck/coercion/struct.CoerceMany.html#tymethod.merged_ty\" class=\"fn\">merged_ty</a>(&amp;self) -&gt; <a class=\"struct\" href=\"rustc_middle/ty/struct.Ty.html\" title=\"struct rustc_middle::ty::Ty\">Ty</a>&lt;'tcx&gt;</h4></section></summary><div class=\"docblock\"><p>Returns the current “merged type”, representing our best-guess\nat the LUB of the expressions we’ve seen so far (if any). This\nisn’t <em>final</em> until you call <code>self.complete()</code>, which will return\nthe merged type.</p>\n</div></details><details class=\"toggle method-toggle\" open><summary><section id=\"method.coerce\" class=\"method\"><a class=\"src rightside\" href=\"src/rustc_hir_typeck/coercion.rs.html#1499-1507\">Source</a><h4 class=\"code-header\">pub(crate) fn <a href=\"rustc_hir_typeck/coercion/struct.CoerceMany.html#tymethod.coerce\" class=\"fn\">coerce</a>&lt;'a&gt;(\n    &amp;mut self,\n    fcx: &amp;<a class=\"struct\" href=\"rustc_hir_typeck/fn_ctxt/struct.FnCtxt.html\" title=\"struct rustc_hir_typeck::fn_ctxt::FnCtxt\">FnCtxt</a>&lt;'a, 'tcx&gt;,\n    cause: &amp;<a class=\"struct\" href=\"rustc_middle/traits/struct.ObligationCause.html\" title=\"struct rustc_middle::traits::ObligationCause\">ObligationCause</a>&lt;'tcx&gt;,\n    expression: &amp;'tcx <a class=\"struct\" href=\"rustc_hir/hir/struct.Expr.html\" title=\"struct rustc_hir::hir::Expr\">Expr</a>&lt;'tcx&gt;,\n    expression_ty: <a class=\"struct\" href=\"rustc_middle/ty/struct.Ty.html\" title=\"struct rustc_middle::ty::Ty\">Ty</a>&lt;'tcx&gt;,\n)</h4></section></summary><div class=\"docblock\"><p>Indicates that the value generated by <code>expression</code>, which is\nof type <code>expression_ty</code>, is one of the possibilities that we\ncould coerce from. This will record <code>expression</code>, and later\ncalls to <code>coerce</code> may come back and add adjustments and things\nif necessary.</p>\n</div></details><details class=\"toggle method-toggle\" open><summary><section id=\"method.coerce_forced_unit\" class=\"method\"><a class=\"src rightside\" href=\"src/rustc_hir_typeck/coercion.rs.html#1521-1536\">Source</a><h4 class=\"code-header\">pub(crate) fn <a href=\"rustc_hir_typeck/coercion/struct.CoerceMany.html#tymethod.coerce_forced_unit\" class=\"fn\">coerce_forced_unit</a>&lt;'a&gt;(\n    &amp;mut self,\n    fcx: &amp;<a class=\"struct\" href=\"rustc_hir_typeck/fn_ctxt/struct.FnCtxt.html\" title=\"struct rustc_hir_typeck::fn_ctxt::FnCtxt\">FnCtxt</a>&lt;'a, 'tcx&gt;,\n    cause: &amp;<a class=\"struct\" href=\"rustc_middle/traits/struct.ObligationCause.html\" title=\"struct rustc_middle::traits::ObligationCause\">ObligationCause</a>&lt;'tcx&gt;,\n    augment_error: impl <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/ops/function/trait.FnOnce.html\" title=\"trait core::ops::function::FnOnce\">FnOnce</a>(&amp;mut <a class=\"struct\" href=\"rustc_errors/diagnostic/struct.Diag.html\" title=\"struct rustc_errors::diagnostic::Diag\">Diag</a>&lt;'_&gt;),\n    label_unit_as_expected: <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.bool.html\">bool</a>,\n)</h4></section></summary><div class=\"docblock\"><p>Indicates that one of the inputs is a “forced unit”. This\noccurs in a case like <code>if foo { ... };</code>, where the missing else\ngenerates a “forced unit”. Another example is a <code>loop { break; }</code>, where the <code>break</code> has no argument expression. We treat\nthese cases slightly differently for error-reporting\npurposes. Note that these tend to correspond to cases where\nthe <code>()</code> expression is implicit in the source, and hence we do\nnot take an expression argument.</p>\n<p>The <code>augment_error</code> gives you a chance to extend the error\nmessage, in case any results (e.g., we use this to suggest\nremoving a <code>;</code>).</p>\n</div></details><details class=\"toggle method-toggle\" open><summary><section id=\"method.coerce_inner\" class=\"method\"><a class=\"src rightside\" href=\"src/rustc_hir_typeck/coercion.rs.html#1541\">Source</a><h4 class=\"code-header\">pub(crate) fn <a href=\"rustc_hir_typeck/coercion/struct.CoerceMany.html#tymethod.coerce_inner\" class=\"fn\">coerce_inner</a>&lt;'a&gt;(\n    &amp;mut self,\n    fcx: &amp;<a class=\"struct\" href=\"rustc_hir_typeck/fn_ctxt/struct.FnCtxt.html\" title=\"struct rustc_hir_typeck::fn_ctxt::FnCtxt\">FnCtxt</a>&lt;'a, 'tcx&gt;,\n    cause: &amp;<a class=\"struct\" href=\"rustc_middle/traits/struct.ObligationCause.html\" title=\"struct rustc_middle::traits::ObligationCause\">ObligationCause</a>&lt;'tcx&gt;,\n    expression: <a class=\"enum\" href=\"https://doc.rust-lang.org/nightly/core/option/enum.Option.html\" title=\"enum core::option::Option\">Option</a>&lt;&amp;'tcx <a class=\"struct\" href=\"rustc_hir/hir/struct.Expr.html\" title=\"struct rustc_hir::hir::Expr\">Expr</a>&lt;'tcx&gt;&gt;,\n    expression_ty: <a class=\"struct\" href=\"rustc_middle/ty/struct.Ty.html\" title=\"struct rustc_middle::ty::Ty\">Ty</a>&lt;'tcx&gt;,\n    augment_error: impl <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/ops/function/trait.FnOnce.html\" title=\"trait core::ops::function::FnOnce\">FnOnce</a>(&amp;mut <a class=\"struct\" href=\"rustc_errors/diagnostic/struct.Diag.html\" title=\"struct rustc_errors::diagnostic::Diag\">Diag</a>&lt;'_&gt;),\n    label_expression_as_expected: <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.bool.html\">bool</a>,\n)</h4></section></summary><div class=\"docblock\"><p>The inner coercion “engine”. If <code>expression</code> is <code>None</code>, this\nis a forced-unit case, and hence <code>expression_ty</code> must be\n<code>Nil</code>.</p>\n</div></details><section id=\"method.suggest_boxing_tail_for_return_position_impl_trait\" class=\"method\"><a class=\"src rightside\" href=\"src/rustc_hir_typeck/coercion.rs.html#1838-1893\">Source</a><h4 class=\"code-header\">fn <a href=\"rustc_hir_typeck/coercion/struct.CoerceMany.html#tymethod.suggest_boxing_tail_for_return_position_impl_trait\" class=\"fn\">suggest_boxing_tail_for_return_position_impl_trait</a>(\n    &amp;self,\n    fcx: &amp;<a class=\"struct\" href=\"rustc_hir_typeck/fn_ctxt/struct.FnCtxt.html\" title=\"struct rustc_hir_typeck::fn_ctxt::FnCtxt\">FnCtxt</a>&lt;'_, 'tcx&gt;,\n    err: &amp;mut <a class=\"struct\" href=\"rustc_errors/diagnostic/struct.Diag.html\" title=\"struct rustc_errors::diagnostic::Diag\">Diag</a>&lt;'_&gt;,\n    rpit_def_id: <a class=\"struct\" href=\"rustc_span/def_id/struct.LocalDefId.html\" title=\"struct rustc_span::def_id::LocalDefId\">LocalDefId</a>,\n    a_ty: <a class=\"struct\" href=\"rustc_middle/ty/struct.Ty.html\" title=\"struct rustc_middle::ty::Ty\">Ty</a>&lt;'tcx&gt;,\n    b_ty: <a class=\"struct\" href=\"rustc_middle/ty/struct.Ty.html\" title=\"struct rustc_middle::ty::Ty\">Ty</a>&lt;'tcx&gt;,\n    arm_spans: impl <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/iter/traits/iterator/trait.Iterator.html\" title=\"trait core::iter::traits::iterator::Iterator\">Iterator</a>&lt;Item = <a class=\"struct\" href=\"rustc_span/span_encoding/struct.Span.html\" title=\"struct rustc_span::span_encoding::Span\">Span</a>&gt;,\n)</h4></section><section id=\"method.report_return_mismatched_types\" class=\"method\"><a class=\"src rightside\" href=\"src/rustc_hir_typeck/coercion.rs.html#1895-1998\">Source</a><h4 class=\"code-header\">fn <a href=\"rustc_hir_typeck/coercion/struct.CoerceMany.html#tymethod.report_return_mismatched_types\" class=\"fn\">report_return_mismatched_types</a>&lt;'infcx&gt;(\n    &amp;self,\n    cause: &amp;<a class=\"struct\" href=\"rustc_middle/traits/struct.ObligationCause.html\" title=\"struct rustc_middle::traits::ObligationCause\">ObligationCause</a>&lt;'tcx&gt;,\n    expected: <a class=\"struct\" href=\"rustc_middle/ty/struct.Ty.html\" title=\"struct rustc_middle::ty::Ty\">Ty</a>&lt;'tcx&gt;,\n    found: <a class=\"struct\" href=\"rustc_middle/ty/struct.Ty.html\" title=\"struct rustc_middle::ty::Ty\">Ty</a>&lt;'tcx&gt;,\n    ty_err: <a class=\"type\" href=\"rustc_middle/ty/error/type.TypeError.html\" title=\"type rustc_middle::ty::error::TypeError\">TypeError</a>&lt;'tcx&gt;,\n    fcx: &amp;'infcx <a class=\"struct\" href=\"rustc_hir_typeck/fn_ctxt/struct.FnCtxt.html\" title=\"struct rustc_hir_typeck::fn_ctxt::FnCtxt\">FnCtxt</a>&lt;'_, 'tcx&gt;,\n    block_or_return_id: <a class=\"struct\" href=\"rustc_hir/hir_id/struct.HirId.html\" title=\"struct rustc_hir::hir_id::HirId\">HirId</a>,\n    expression: <a class=\"enum\" href=\"https://doc.rust-lang.org/nightly/core/option/enum.Option.html\" title=\"enum core::option::Option\">Option</a>&lt;&amp;'tcx <a class=\"struct\" href=\"rustc_hir/hir/struct.Expr.html\" title=\"struct rustc_hir::hir::Expr\">Expr</a>&lt;'tcx&gt;&gt;,\n) -&gt; <a class=\"struct\" href=\"rustc_errors/diagnostic/struct.Diag.html\" title=\"struct rustc_errors::diagnostic::Diag\">Diag</a>&lt;'infcx&gt;</h4></section><details class=\"toggle method-toggle\" open><summary><section id=\"method.is_return_ty_definitely_unsized\" class=\"method\"><a class=\"src rightside\" href=\"src/rustc_hir_typeck/coercion.rs.html#2003-2018\">Source</a><h4 class=\"code-header\">fn <a href=\"rustc_hir_typeck/coercion/struct.CoerceMany.html#tymethod.is_return_ty_definitely_unsized\" class=\"fn\">is_return_ty_definitely_unsized</a>(&amp;self, fcx: &amp;<a class=\"struct\" href=\"rustc_hir_typeck/fn_ctxt/struct.FnCtxt.html\" title=\"struct rustc_hir_typeck::fn_ctxt::FnCtxt\">FnCtxt</a>&lt;'_, 'tcx&gt;) -&gt; <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.bool.html\">bool</a></h4></section></summary><div class=\"docblock\"><p>Checks whether the return type is unsized via an obligation, which makes\nsure we consider <code>dyn Trait: Sized</code> where clauses, which are trivially\nfalse but technically valid for typeck.</p>\n</div></details><section id=\"method.complete\" class=\"method\"><a class=\"src rightside\" href=\"src/rustc_hir_typeck/coercion.rs.html#2020-2029\">Source</a><h4 class=\"code-header\">pub(crate) fn <a href=\"rustc_hir_typeck/coercion/struct.CoerceMany.html#tymethod.complete\" class=\"fn\">complete</a>&lt;'a&gt;(self, fcx: &amp;<a class=\"struct\" href=\"rustc_hir_typeck/fn_ctxt/struct.FnCtxt.html\" title=\"struct rustc_hir_typeck::fn_ctxt::FnCtxt\">FnCtxt</a>&lt;'a, 'tcx&gt;) -&gt; <a class=\"struct\" href=\"rustc_middle/ty/struct.Ty.html\" title=\"struct rustc_middle::ty::Ty\">Ty</a>&lt;'tcx&gt;</h4></section></div></details>",0,"rustc_hir_typeck::coercion::DynamicCoerceMany"]]]]);
    if (window.register_type_impls) {
        window.register_type_impls(type_impls);
    } else {
        window.pending_type_impls = type_impls;
    }
})()
//{"start":55,"fragment_lengths":[14941]}