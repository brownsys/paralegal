(function() {
    var type_impls = Object.fromEntries([["gimli",[["<details class=\"toggle implementors-toggle\" open><summary><section id=\"impl-Clone-for-CompleteLineProgram%3CR,+Offset%3E\" class=\"impl\"><a class=\"src rightside\" href=\"src/gimli/read/line.rs.html#1503\">Source</a><a href=\"#impl-Clone-for-CompleteLineProgram%3CR,+Offset%3E\" class=\"anchor\">§</a><h3 class=\"code-header\">impl&lt;R, Offset&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/clone/trait.Clone.html\" title=\"trait core::clone::Clone\">Clone</a> for <a class=\"struct\" href=\"gimli/read/struct.CompleteLineProgram.html\" title=\"struct gimli::read::CompleteLineProgram\">CompleteLineProgram</a>&lt;R, Offset&gt;<div class=\"where\">where\n    R: <a class=\"trait\" href=\"gimli/read/trait.Reader.html\" title=\"trait gimli::read::Reader\">Reader</a>&lt;Offset = Offset&gt; + <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/clone/trait.Clone.html\" title=\"trait core::clone::Clone\">Clone</a>,\n    Offset: <a class=\"trait\" href=\"gimli/read/trait.ReaderOffset.html\" title=\"trait gimli::read::ReaderOffset\">ReaderOffset</a> + <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/clone/trait.Clone.html\" title=\"trait core::clone::Clone\">Clone</a>,</div></h3></section></summary><div class=\"impl-items\"><details class=\"toggle method-toggle\" open><summary><section id=\"method.clone\" class=\"method trait-impl\"><a class=\"src rightside\" href=\"src/gimli/read/line.rs.html#1503\">Source</a><a href=\"#method.clone\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"https://doc.rust-lang.org/nightly/core/clone/trait.Clone.html#tymethod.clone\" class=\"fn\">clone</a>(&amp;self) -&gt; <a class=\"struct\" href=\"gimli/read/struct.CompleteLineProgram.html\" title=\"struct gimli::read::CompleteLineProgram\">CompleteLineProgram</a>&lt;R, Offset&gt;</h4></section></summary><div class='docblock'>Returns a copy of the value. <a href=\"https://doc.rust-lang.org/nightly/core/clone/trait.Clone.html#tymethod.clone\">Read more</a></div></details><details class=\"toggle method-toggle\" open><summary><section id=\"method.clone_from\" class=\"method trait-impl\"><span class=\"rightside\"><span class=\"since\" title=\"Stable since Rust version 1.0.0\">1.0.0</span> · <a class=\"src\" href=\"https://doc.rust-lang.org/nightly/src/core/clone.rs.html#174\">Source</a></span><a href=\"#method.clone_from\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"https://doc.rust-lang.org/nightly/core/clone/trait.Clone.html#method.clone_from\" class=\"fn\">clone_from</a>(&amp;mut self, source: &amp;Self)</h4></section></summary><div class='docblock'>Performs copy-assignment from <code>source</code>. <a href=\"https://doc.rust-lang.org/nightly/core/clone/trait.Clone.html#method.clone_from\">Read more</a></div></details></div></details>","Clone","gimli::read::line::CompleteLineNumberProgram"],["<details class=\"toggle implementors-toggle\" open><summary><section id=\"impl-CompleteLineProgram%3CR,+Offset%3E\" class=\"impl\"><a class=\"src rightside\" href=\"src/gimli/read/line.rs.html#1512-1549\">Source</a><a href=\"#impl-CompleteLineProgram%3CR,+Offset%3E\" class=\"anchor\">§</a><h3 class=\"code-header\">impl&lt;R, Offset&gt; <a class=\"struct\" href=\"gimli/read/struct.CompleteLineProgram.html\" title=\"struct gimli::read::CompleteLineProgram\">CompleteLineProgram</a>&lt;R, Offset&gt;<div class=\"where\">where\n    R: <a class=\"trait\" href=\"gimli/read/trait.Reader.html\" title=\"trait gimli::read::Reader\">Reader</a>&lt;Offset = Offset&gt;,\n    Offset: <a class=\"trait\" href=\"gimli/read/trait.ReaderOffset.html\" title=\"trait gimli::read::ReaderOffset\">ReaderOffset</a>,</div></h3></section></summary><div class=\"impl-items\"><details class=\"toggle method-toggle\" open><summary><section id=\"method.header\" class=\"method\"><a class=\"src rightside\" href=\"src/gimli/read/line.rs.html#1518-1520\">Source</a><h4 class=\"code-header\">pub fn <a href=\"gimli/read/struct.CompleteLineProgram.html#tymethod.header\" class=\"fn\">header</a>(&amp;self) -&gt; &amp;<a class=\"struct\" href=\"gimli/read/struct.LineProgramHeader.html\" title=\"struct gimli::read::LineProgramHeader\">LineProgramHeader</a>&lt;R, Offset&gt;</h4></section></summary><div class=\"docblock\"><p>Retrieve the <code>LineProgramHeader</code> for this program.</p>\n</div></details><details class=\"toggle method-toggle\" open><summary><section id=\"method.resume_from\" class=\"method\"><a class=\"src rightside\" href=\"src/gimli/read/line.rs.html#1543-1548\">Source</a><h4 class=\"code-header\">pub fn <a href=\"gimli/read/struct.CompleteLineProgram.html#tymethod.resume_from\" class=\"fn\">resume_from</a>&lt;'program&gt;(\n    &amp;'program self,\n    sequence: &amp;<a class=\"struct\" href=\"gimli/read/struct.LineSequence.html\" title=\"struct gimli::read::LineSequence\">LineSequence</a>&lt;R&gt;,\n) -&gt; <a class=\"struct\" href=\"gimli/read/struct.LineRows.html\" title=\"struct gimli::read::LineRows\">LineRows</a>&lt;R, &amp;'program <a class=\"struct\" href=\"gimli/read/struct.CompleteLineProgram.html\" title=\"struct gimli::read::CompleteLineProgram\">CompleteLineProgram</a>&lt;R, Offset&gt;, Offset&gt;</h4></section></summary><div class=\"docblock\"><p>Construct a new <code>LineRows</code> for executing the subset of the line\nnumber program identified by ‘sequence’ and  generating the line information\nmatrix.</p>\n\n<div class=\"example-wrap\"><pre class=\"rust rust-example-rendered\"><code><span class=\"kw\">use </span>gimli::{IncompleteLineProgram, EndianSlice, NativeEndian};\n\n<span class=\"kw\">fn </span>get_line_number_program&lt;<span class=\"lifetime\">'a</span>&gt;() -&gt; IncompleteLineProgram&lt;EndianSlice&lt;<span class=\"lifetime\">'a</span>, NativeEndian&gt;&gt; {\n    <span class=\"comment\">// Get a line number program from some offset in a\n    // `.debug_line` section...\n</span>}\n\n<span class=\"kw\">let </span>program = get_line_number_program();\n<span class=\"kw\">let </span>(program, sequences) = program.sequences().unwrap();\n<span class=\"kw\">for </span>sequence <span class=\"kw\">in </span><span class=\"kw-2\">&amp;</span>sequences {\n    <span class=\"kw\">let </span><span class=\"kw-2\">mut </span>sm = program.resume_from(sequence);\n}</code></pre></div>\n</div></details></div></details>",0,"gimli::read::line::CompleteLineNumberProgram"],["<details class=\"toggle implementors-toggle\" open><summary><section id=\"impl-Debug-for-CompleteLineProgram%3CR,+Offset%3E\" class=\"impl\"><a class=\"src rightside\" href=\"src/gimli/read/line.rs.html#1503\">Source</a><a href=\"#impl-Debug-for-CompleteLineProgram%3CR,+Offset%3E\" class=\"anchor\">§</a><h3 class=\"code-header\">impl&lt;R, Offset&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/fmt/trait.Debug.html\" title=\"trait core::fmt::Debug\">Debug</a> for <a class=\"struct\" href=\"gimli/read/struct.CompleteLineProgram.html\" title=\"struct gimli::read::CompleteLineProgram\">CompleteLineProgram</a>&lt;R, Offset&gt;<div class=\"where\">where\n    R: <a class=\"trait\" href=\"gimli/read/trait.Reader.html\" title=\"trait gimli::read::Reader\">Reader</a>&lt;Offset = Offset&gt; + <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/fmt/trait.Debug.html\" title=\"trait core::fmt::Debug\">Debug</a>,\n    Offset: <a class=\"trait\" href=\"gimli/read/trait.ReaderOffset.html\" title=\"trait gimli::read::ReaderOffset\">ReaderOffset</a> + <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/fmt/trait.Debug.html\" title=\"trait core::fmt::Debug\">Debug</a>,</div></h3></section></summary><div class=\"impl-items\"><details class=\"toggle method-toggle\" open><summary><section id=\"method.fmt\" class=\"method trait-impl\"><a class=\"src rightside\" href=\"src/gimli/read/line.rs.html#1503\">Source</a><a href=\"#method.fmt\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"https://doc.rust-lang.org/nightly/core/fmt/trait.Debug.html#tymethod.fmt\" class=\"fn\">fmt</a>(&amp;self, f: &amp;mut <a class=\"struct\" href=\"https://doc.rust-lang.org/nightly/core/fmt/struct.Formatter.html\" title=\"struct core::fmt::Formatter\">Formatter</a>&lt;'_&gt;) -&gt; <a class=\"type\" href=\"https://doc.rust-lang.org/nightly/core/fmt/type.Result.html\" title=\"type core::fmt::Result\">Result</a></h4></section></summary><div class='docblock'>Formats the value using the given formatter. <a href=\"https://doc.rust-lang.org/nightly/core/fmt/trait.Debug.html#tymethod.fmt\">Read more</a></div></details></div></details>","Debug","gimli::read::line::CompleteLineNumberProgram"],["<details class=\"toggle implementors-toggle\" open><summary><section id=\"impl-PartialEq-for-CompleteLineProgram%3CR,+Offset%3E\" class=\"impl\"><a class=\"src rightside\" href=\"src/gimli/read/line.rs.html#1503\">Source</a><a href=\"#impl-PartialEq-for-CompleteLineProgram%3CR,+Offset%3E\" class=\"anchor\">§</a><h3 class=\"code-header\">impl&lt;R, Offset&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/cmp/trait.PartialEq.html\" title=\"trait core::cmp::PartialEq\">PartialEq</a> for <a class=\"struct\" href=\"gimli/read/struct.CompleteLineProgram.html\" title=\"struct gimli::read::CompleteLineProgram\">CompleteLineProgram</a>&lt;R, Offset&gt;<div class=\"where\">where\n    R: <a class=\"trait\" href=\"gimli/read/trait.Reader.html\" title=\"trait gimli::read::Reader\">Reader</a>&lt;Offset = Offset&gt; + <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/cmp/trait.PartialEq.html\" title=\"trait core::cmp::PartialEq\">PartialEq</a>,\n    Offset: <a class=\"trait\" href=\"gimli/read/trait.ReaderOffset.html\" title=\"trait gimli::read::ReaderOffset\">ReaderOffset</a> + <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/cmp/trait.PartialEq.html\" title=\"trait core::cmp::PartialEq\">PartialEq</a>,</div></h3></section></summary><div class=\"impl-items\"><details class=\"toggle method-toggle\" open><summary><section id=\"method.eq\" class=\"method trait-impl\"><a class=\"src rightside\" href=\"src/gimli/read/line.rs.html#1503\">Source</a><a href=\"#method.eq\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"https://doc.rust-lang.org/nightly/core/cmp/trait.PartialEq.html#tymethod.eq\" class=\"fn\">eq</a>(&amp;self, other: &amp;<a class=\"struct\" href=\"gimli/read/struct.CompleteLineProgram.html\" title=\"struct gimli::read::CompleteLineProgram\">CompleteLineProgram</a>&lt;R, Offset&gt;) -&gt; <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/core/primitive.bool.html\">bool</a></h4></section></summary><div class='docblock'>Tests for <code>self</code> and <code>other</code> values to be equal, and is used by <code>==</code>.</div></details><details class=\"toggle method-toggle\" open><summary><section id=\"method.ne\" class=\"method trait-impl\"><span class=\"rightside\"><span class=\"since\" title=\"Stable since Rust version 1.0.0\">1.0.0</span> · <a class=\"src\" href=\"https://doc.rust-lang.org/nightly/src/core/cmp.rs.html#261\">Source</a></span><a href=\"#method.ne\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"https://doc.rust-lang.org/nightly/core/cmp/trait.PartialEq.html#method.ne\" class=\"fn\">ne</a>(&amp;self, other: <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/core/primitive.reference.html\">&amp;Rhs</a>) -&gt; <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/core/primitive.bool.html\">bool</a></h4></section></summary><div class='docblock'>Tests for <code>!=</code>. The default implementation is almost always sufficient,\nand should not be overridden without very good reason.</div></details></div></details>","PartialEq","gimli::read::line::CompleteLineNumberProgram"],["<section id=\"impl-Eq-for-CompleteLineProgram%3CR,+Offset%3E\" class=\"impl\"><a class=\"src rightside\" href=\"src/gimli/read/line.rs.html#1503\">Source</a><a href=\"#impl-Eq-for-CompleteLineProgram%3CR,+Offset%3E\" class=\"anchor\">§</a><h3 class=\"code-header\">impl&lt;R, Offset&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/cmp/trait.Eq.html\" title=\"trait core::cmp::Eq\">Eq</a> for <a class=\"struct\" href=\"gimli/read/struct.CompleteLineProgram.html\" title=\"struct gimli::read::CompleteLineProgram\">CompleteLineProgram</a>&lt;R, Offset&gt;<div class=\"where\">where\n    R: <a class=\"trait\" href=\"gimli/read/trait.Reader.html\" title=\"trait gimli::read::Reader\">Reader</a>&lt;Offset = Offset&gt; + <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/cmp/trait.Eq.html\" title=\"trait core::cmp::Eq\">Eq</a>,\n    Offset: <a class=\"trait\" href=\"gimli/read/trait.ReaderOffset.html\" title=\"trait gimli::read::ReaderOffset\">ReaderOffset</a> + <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/cmp/trait.Eq.html\" title=\"trait core::cmp::Eq\">Eq</a>,</div></h3></section>","Eq","gimli::read::line::CompleteLineNumberProgram"],["<section id=\"impl-StructuralPartialEq-for-CompleteLineProgram%3CR,+Offset%3E\" class=\"impl\"><a class=\"src rightside\" href=\"src/gimli/read/line.rs.html#1503\">Source</a><a href=\"#impl-StructuralPartialEq-for-CompleteLineProgram%3CR,+Offset%3E\" class=\"anchor\">§</a><h3 class=\"code-header\">impl&lt;R, Offset&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/marker/trait.StructuralPartialEq.html\" title=\"trait core::marker::StructuralPartialEq\">StructuralPartialEq</a> for <a class=\"struct\" href=\"gimli/read/struct.CompleteLineProgram.html\" title=\"struct gimli::read::CompleteLineProgram\">CompleteLineProgram</a>&lt;R, Offset&gt;<div class=\"where\">where\n    R: <a class=\"trait\" href=\"gimli/read/trait.Reader.html\" title=\"trait gimli::read::Reader\">Reader</a>&lt;Offset = Offset&gt;,\n    Offset: <a class=\"trait\" href=\"gimli/read/trait.ReaderOffset.html\" title=\"trait gimli::read::ReaderOffset\">ReaderOffset</a>,</div></h3></section>","StructuralPartialEq","gimli::read::line::CompleteLineNumberProgram"]]]]);
    if (window.register_type_impls) {
        window.register_type_impls(type_impls);
    } else {
        window.pending_type_impls = type_impls;
    }
})()
//{"start":55,"fragment_lengths":[14080]}