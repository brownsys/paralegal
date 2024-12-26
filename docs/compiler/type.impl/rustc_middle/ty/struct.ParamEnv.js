(function() {
    var type_impls = Object.fromEntries([["rustc_middle",[["<details class=\"toggle implementors-toggle\" open><summary><section id=\"impl-Clone-for-ParamEnv%3C'tcx%3E\" class=\"impl\"><a class=\"src rightside\" href=\"src/rustc_middle/ty/mod.rs.html#963\">Source</a><a href=\"#impl-Clone-for-ParamEnv%3C'tcx%3E\" class=\"anchor\">§</a><h3 class=\"code-header\">impl&lt;'tcx&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/clone/trait.Clone.html\" title=\"trait core::clone::Clone\">Clone</a> for <a class=\"struct\" href=\"rustc_middle/ty/struct.ParamEnv.html\" title=\"struct rustc_middle::ty::ParamEnv\">ParamEnv</a>&lt;'tcx&gt;</h3></section></summary><div class=\"impl-items\"><details class=\"toggle method-toggle\" open><summary><section id=\"method.clone\" class=\"method trait-impl\"><a class=\"src rightside\" href=\"src/rustc_middle/ty/mod.rs.html#963\">Source</a><a href=\"#method.clone\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"https://doc.rust-lang.org/nightly/core/clone/trait.Clone.html#tymethod.clone\" class=\"fn\">clone</a>(&amp;self) -&gt; <a class=\"struct\" href=\"rustc_middle/ty/struct.ParamEnv.html\" title=\"struct rustc_middle::ty::ParamEnv\">ParamEnv</a>&lt;'tcx&gt;</h4></section></summary><div class='docblock'>Returns a copy of the value. <a href=\"https://doc.rust-lang.org/nightly/core/clone/trait.Clone.html#tymethod.clone\">Read more</a></div></details><details class=\"toggle method-toggle\" open><summary><section id=\"method.clone_from\" class=\"method trait-impl\"><span class=\"rightside\"><span class=\"since\" title=\"Stable since Rust version 1.0.0\">1.0.0</span> · <a class=\"src\" href=\"https://doc.rust-lang.org/nightly/src/core/clone.rs.html#174\">Source</a></span><a href=\"#method.clone_from\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"https://doc.rust-lang.org/nightly/core/clone/trait.Clone.html#method.clone_from\" class=\"fn\">clone_from</a>(&amp;mut self, source: &amp;Self)</h4></section></summary><div class='docblock'>Performs copy-assignment from <code>source</code>. <a href=\"https://doc.rust-lang.org/nightly/core/clone/trait.Clone.html#method.clone_from\">Read more</a></div></details></div></details>","Clone","rustc_middle::query::queries::param_env::Value","rustc_middle::query::queries::param_env::ProvidedValue","rustc_middle::query::queries::param_env_normalized_for_post_analysis::Value","rustc_middle::query::queries::param_env_normalized_for_post_analysis::ProvidedValue"],["<details class=\"toggle implementors-toggle\" open><summary><section id=\"impl-Debug-for-ParamEnv%3C'tcx%3E\" class=\"impl\"><a class=\"src rightside\" href=\"src/rustc_middle/ty/mod.rs.html#963\">Source</a><a href=\"#impl-Debug-for-ParamEnv%3C'tcx%3E\" class=\"anchor\">§</a><h3 class=\"code-header\">impl&lt;'tcx&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/fmt/trait.Debug.html\" title=\"trait core::fmt::Debug\">Debug</a> for <a class=\"struct\" href=\"rustc_middle/ty/struct.ParamEnv.html\" title=\"struct rustc_middle::ty::ParamEnv\">ParamEnv</a>&lt;'tcx&gt;</h3></section></summary><div class=\"impl-items\"><details class=\"toggle method-toggle\" open><summary><section id=\"method.fmt\" class=\"method trait-impl\"><a class=\"src rightside\" href=\"src/rustc_middle/ty/mod.rs.html#963\">Source</a><a href=\"#method.fmt\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"https://doc.rust-lang.org/nightly/core/fmt/trait.Debug.html#tymethod.fmt\" class=\"fn\">fmt</a>(&amp;self, f: &amp;mut <a class=\"struct\" href=\"https://doc.rust-lang.org/nightly/core/fmt/struct.Formatter.html\" title=\"struct core::fmt::Formatter\">Formatter</a>&lt;'_&gt;) -&gt; <a class=\"type\" href=\"https://doc.rust-lang.org/nightly/core/fmt/type.Result.html\" title=\"type core::fmt::Result\">Result</a></h4></section></summary><div class='docblock'>Formats the value using the given formatter. <a href=\"https://doc.rust-lang.org/nightly/core/fmt/trait.Debug.html#tymethod.fmt\">Read more</a></div></details></div></details>","Debug","rustc_middle::query::queries::param_env::Value","rustc_middle::query::queries::param_env::ProvidedValue","rustc_middle::query::queries::param_env_normalized_for_post_analysis::Value","rustc_middle::query::queries::param_env_normalized_for_post_analysis::ProvidedValue"],["<details class=\"toggle implementors-toggle\" open><summary><section id=\"impl-Decodable%3CD%3E-for-ParamEnv%3C'tcx%3E\" class=\"impl\"><a class=\"src rightside\" href=\"src/rustc_middle/ty/codec.rs.html#309-314\">Source</a><a href=\"#impl-Decodable%3CD%3E-for-ParamEnv%3C'tcx%3E\" class=\"anchor\">§</a><h3 class=\"code-header\">impl&lt;'tcx, D: <a class=\"trait\" href=\"rustc_middle/ty/trait.TyDecoder.html\" title=\"trait rustc_middle::ty::TyDecoder\">TyDecoder</a>&lt;I = <a class=\"struct\" href=\"rustc_middle/ty/context/struct.TyCtxt.html\" title=\"struct rustc_middle::ty::context::TyCtxt\">TyCtxt</a>&lt;'tcx&gt;&gt;&gt; <a class=\"trait\" href=\"rustc_serialize/serialize/trait.Decodable.html\" title=\"trait rustc_serialize::serialize::Decodable\">Decodable</a>&lt;D&gt; for <a class=\"struct\" href=\"rustc_middle/ty/struct.ParamEnv.html\" title=\"struct rustc_middle::ty::ParamEnv\">ParamEnv</a>&lt;'tcx&gt;</h3></section></summary><div class=\"impl-items\"><section id=\"method.decode\" class=\"method trait-impl\"><a class=\"src rightside\" href=\"src/rustc_middle/ty/codec.rs.html#310-313\">Source</a><a href=\"#method.decode\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"rustc_serialize/serialize/trait.Decodable.html#tymethod.decode\" class=\"fn\">decode</a>(d: <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.reference.html\">&amp;mut D</a>) -&gt; Self</h4></section></div></details>","Decodable<D>","rustc_middle::query::queries::param_env::Value","rustc_middle::query::queries::param_env::ProvidedValue","rustc_middle::query::queries::param_env_normalized_for_post_analysis::Value","rustc_middle::query::queries::param_env_normalized_for_post_analysis::ProvidedValue"],["<details class=\"toggle implementors-toggle\" open><summary><section id=\"impl-Encodable%3CE%3E-for-ParamEnv%3C'tcx%3E\" class=\"impl\"><a class=\"src rightside\" href=\"src/rustc_middle/ty/codec.rs.html#174-178\">Source</a><a href=\"#impl-Encodable%3CE%3E-for-ParamEnv%3C'tcx%3E\" class=\"anchor\">§</a><h3 class=\"code-header\">impl&lt;'tcx, E: <a class=\"trait\" href=\"rustc_middle/ty/trait.TyEncoder.html\" title=\"trait rustc_middle::ty::TyEncoder\">TyEncoder</a>&lt;I = <a class=\"struct\" href=\"rustc_middle/ty/context/struct.TyCtxt.html\" title=\"struct rustc_middle::ty::context::TyCtxt\">TyCtxt</a>&lt;'tcx&gt;&gt;&gt; <a class=\"trait\" href=\"rustc_serialize/serialize/trait.Encodable.html\" title=\"trait rustc_serialize::serialize::Encodable\">Encodable</a>&lt;E&gt; for <a class=\"struct\" href=\"rustc_middle/ty/struct.ParamEnv.html\" title=\"struct rustc_middle::ty::ParamEnv\">ParamEnv</a>&lt;'tcx&gt;</h3></section></summary><div class=\"impl-items\"><section id=\"method.encode\" class=\"method trait-impl\"><a class=\"src rightside\" href=\"src/rustc_middle/ty/codec.rs.html#175-177\">Source</a><a href=\"#method.encode\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"rustc_serialize/serialize/trait.Encodable.html#tymethod.encode\" class=\"fn\">encode</a>(&amp;self, e: <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.reference.html\">&amp;mut E</a>)</h4></section></div></details>","Encodable<E>","rustc_middle::query::queries::param_env::Value","rustc_middle::query::queries::param_env::ProvidedValue","rustc_middle::query::queries::param_env_normalized_for_post_analysis::Value","rustc_middle::query::queries::param_env_normalized_for_post_analysis::ProvidedValue"],["<details class=\"toggle implementors-toggle\" open><summary><section id=\"impl-EraseType-for-ParamEnv%3C'tcx%3E\" class=\"impl\"><a class=\"src rightside\" href=\"src/rustc_middle/query/erase.rs.html#352-390\">Source</a><a href=\"#impl-EraseType-for-ParamEnv%3C'tcx%3E\" class=\"anchor\">§</a><h3 class=\"code-header\">impl&lt;'tcx&gt; <a class=\"trait\" href=\"rustc_middle/query/erase/trait.EraseType.html\" title=\"trait rustc_middle::query::erase::EraseType\">EraseType</a> for <a class=\"struct\" href=\"rustc_middle/ty/struct.ParamEnv.html\" title=\"struct rustc_middle::ty::ParamEnv\">ParamEnv</a>&lt;'tcx&gt;</h3></section></summary><div class=\"impl-items\"><section id=\"associatedtype.Result\" class=\"associatedtype trait-impl\"><a class=\"src rightside\" href=\"src/rustc_middle/query/erase.rs.html#352-390\">Source</a><a href=\"#associatedtype.Result\" class=\"anchor\">§</a><h4 class=\"code-header\">type <a href=\"rustc_middle/query/erase/trait.EraseType.html#associatedtype.Result\" class=\"associatedtype\">Result</a> = [<a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.u8.html\">u8</a>; <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.array.html\">8</a>]</h4></section></div></details>","EraseType","rustc_middle::query::queries::param_env::Value","rustc_middle::query::queries::param_env::ProvidedValue","rustc_middle::query::queries::param_env_normalized_for_post_analysis::Value","rustc_middle::query::queries::param_env_normalized_for_post_analysis::ProvidedValue"],["<details class=\"toggle implementors-toggle\" open><summary><section id=\"impl-Hash-for-ParamEnv%3C'tcx%3E\" class=\"impl\"><a class=\"src rightside\" href=\"src/rustc_middle/ty/mod.rs.html#963\">Source</a><a href=\"#impl-Hash-for-ParamEnv%3C'tcx%3E\" class=\"anchor\">§</a><h3 class=\"code-header\">impl&lt;'tcx&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/hash/trait.Hash.html\" title=\"trait core::hash::Hash\">Hash</a> for <a class=\"struct\" href=\"rustc_middle/ty/struct.ParamEnv.html\" title=\"struct rustc_middle::ty::ParamEnv\">ParamEnv</a>&lt;'tcx&gt;</h3></section></summary><div class=\"impl-items\"><details class=\"toggle method-toggle\" open><summary><section id=\"method.hash\" class=\"method trait-impl\"><a class=\"src rightside\" href=\"src/rustc_middle/ty/mod.rs.html#963\">Source</a><a href=\"#method.hash\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"https://doc.rust-lang.org/nightly/core/hash/trait.Hash.html#tymethod.hash\" class=\"fn\">hash</a>&lt;__H: <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/hash/trait.Hasher.html\" title=\"trait core::hash::Hasher\">Hasher</a>&gt;(&amp;self, state: <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.reference.html\">&amp;mut __H</a>)</h4></section></summary><div class='docblock'>Feeds this value into the given <a href=\"https://doc.rust-lang.org/nightly/core/hash/trait.Hasher.html\" title=\"trait core::hash::Hasher\"><code>Hasher</code></a>. <a href=\"https://doc.rust-lang.org/nightly/core/hash/trait.Hash.html#tymethod.hash\">Read more</a></div></details><details class=\"toggle method-toggle\" open><summary><section id=\"method.hash_slice\" class=\"method trait-impl\"><span class=\"rightside\"><span class=\"since\" title=\"Stable since Rust version 1.3.0\">1.3.0</span> · <a class=\"src\" href=\"https://doc.rust-lang.org/nightly/src/core/hash/mod.rs.html#235-237\">Source</a></span><a href=\"#method.hash_slice\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"https://doc.rust-lang.org/nightly/core/hash/trait.Hash.html#method.hash_slice\" class=\"fn\">hash_slice</a>&lt;H&gt;(data: &amp;[Self], state: <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.reference.html\">&amp;mut H</a>)<div class=\"where\">where\n    H: <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/hash/trait.Hasher.html\" title=\"trait core::hash::Hasher\">Hasher</a>,\n    Self: <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/marker/trait.Sized.html\" title=\"trait core::marker::Sized\">Sized</a>,</div></h4></section></summary><div class='docblock'>Feeds a slice of this type into the given <a href=\"https://doc.rust-lang.org/nightly/core/hash/trait.Hasher.html\" title=\"trait core::hash::Hasher\"><code>Hasher</code></a>. <a href=\"https://doc.rust-lang.org/nightly/core/hash/trait.Hash.html#method.hash_slice\">Read more</a></div></details></div></details>","Hash","rustc_middle::query::queries::param_env::Value","rustc_middle::query::queries::param_env::ProvidedValue","rustc_middle::query::queries::param_env_normalized_for_post_analysis::Value","rustc_middle::query::queries::param_env_normalized_for_post_analysis::ProvidedValue"],["<details class=\"toggle implementors-toggle\" open><summary><section id=\"impl-HashStable%3CStableHashingContext%3C'__ctx%3E%3E-for-ParamEnv%3C'tcx%3E\" class=\"impl\"><a class=\"src rightside\" href=\"src/rustc_middle/ty/mod.rs.html#964\">Source</a><a href=\"#impl-HashStable%3CStableHashingContext%3C'__ctx%3E%3E-for-ParamEnv%3C'tcx%3E\" class=\"anchor\">§</a><h3 class=\"code-header\">impl&lt;'tcx, '__ctx&gt; <a class=\"trait\" href=\"rustc_data_structures/stable_hasher/trait.HashStable.html\" title=\"trait rustc_data_structures::stable_hasher::HashStable\">HashStable</a>&lt;<a class=\"struct\" href=\"rustc_query_system/ich/hcx/struct.StableHashingContext.html\" title=\"struct rustc_query_system::ich::hcx::StableHashingContext\">StableHashingContext</a>&lt;'__ctx&gt;&gt; for <a class=\"struct\" href=\"rustc_middle/ty/struct.ParamEnv.html\" title=\"struct rustc_middle::ty::ParamEnv\">ParamEnv</a>&lt;'tcx&gt;</h3></section></summary><div class=\"impl-items\"><section id=\"method.hash_stable\" class=\"method trait-impl\"><a class=\"src rightside\" href=\"src/rustc_middle/ty/mod.rs.html#964\">Source</a><a href=\"#method.hash_stable\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"rustc_data_structures/stable_hasher/trait.HashStable.html#tymethod.hash_stable\" class=\"fn\">hash_stable</a>(\n    &amp;self,\n    __hcx: &amp;mut <a class=\"struct\" href=\"rustc_query_system/ich/hcx/struct.StableHashingContext.html\" title=\"struct rustc_query_system::ich::hcx::StableHashingContext\">StableHashingContext</a>&lt;'__ctx&gt;,\n    __hasher: &amp;mut <a class=\"type\" href=\"https://docs.rs/rustc-stable-hash/0.1.0/rustc_stable_hash/hashers/type.StableSipHasher128.html\" title=\"type rustc_stable_hash::hashers::StableSipHasher128\">StableHasher</a>,\n)</h4></section></div></details>","HashStable<StableHashingContext<'__ctx>>","rustc_middle::query::queries::param_env::Value","rustc_middle::query::queries::param_env::ProvidedValue","rustc_middle::query::queries::param_env_normalized_for_post_analysis::Value","rustc_middle::query::queries::param_env_normalized_for_post_analysis::ProvidedValue"],["<details class=\"toggle implementors-toggle\" open><summary><section id=\"impl-Key-for-ParamEnv%3C'tcx%3E\" class=\"impl\"><a class=\"src rightside\" href=\"src/rustc_middle/query/keys.rs.html#460-466\">Source</a><a href=\"#impl-Key-for-ParamEnv%3C'tcx%3E\" class=\"anchor\">§</a><h3 class=\"code-header\">impl&lt;'tcx&gt; <a class=\"trait\" href=\"rustc_middle/query/keys/trait.Key.html\" title=\"trait rustc_middle::query::keys::Key\">Key</a> for <a class=\"struct\" href=\"rustc_middle/ty/struct.ParamEnv.html\" title=\"struct rustc_middle::ty::ParamEnv\">ParamEnv</a>&lt;'tcx&gt;</h3></section></summary><div class=\"impl-items\"><section id=\"associatedtype.Cache\" class=\"associatedtype trait-impl\"><a class=\"src rightside\" href=\"src/rustc_middle/query/keys.rs.html#461\">Source</a><a href=\"#associatedtype.Cache\" class=\"anchor\">§</a><h4 class=\"code-header\">type <a href=\"rustc_middle/query/keys/trait.Key.html#associatedtype.Cache\" class=\"associatedtype\">Cache</a>&lt;V&gt; = <a class=\"struct\" href=\"rustc_query_system/query/caches/struct.DefaultCache.html\" title=\"struct rustc_query_system::query::caches::DefaultCache\">DefaultCache</a>&lt;<a class=\"struct\" href=\"rustc_middle/ty/struct.ParamEnv.html\" title=\"struct rustc_middle::ty::ParamEnv\">ParamEnv</a>&lt;'tcx&gt;, V&gt;</h4></section><details class=\"toggle method-toggle\" open><summary><section id=\"method.default_span\" class=\"method trait-impl\"><a class=\"src rightside\" href=\"src/rustc_middle/query/keys.rs.html#463-465\">Source</a><a href=\"#method.default_span\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"rustc_middle/query/keys/trait.Key.html#tymethod.default_span\" class=\"fn\">default_span</a>(&amp;self, _: <a class=\"struct\" href=\"rustc_middle/ty/context/struct.TyCtxt.html\" title=\"struct rustc_middle::ty::context::TyCtxt\">TyCtxt</a>&lt;'_&gt;) -&gt; <a class=\"struct\" href=\"rustc_span/span_encoding/struct.Span.html\" title=\"struct rustc_span::span_encoding::Span\">Span</a></h4></section></summary><div class='docblock'>In the event that a cycle occurs, if no explicit span has been\ngiven for a query with key <code>self</code>, what span should we use?</div></details><details class=\"toggle method-toggle\" open><summary><section id=\"method.key_as_def_id\" class=\"method trait-impl\"><a class=\"src rightside\" href=\"src/rustc_middle/query/keys.rs.html#40-42\">Source</a><a href=\"#method.key_as_def_id\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"rustc_middle/query/keys/trait.Key.html#method.key_as_def_id\" class=\"fn\">key_as_def_id</a>(&amp;self) -&gt; <a class=\"enum\" href=\"https://doc.rust-lang.org/nightly/core/option/enum.Option.html\" title=\"enum core::option::Option\">Option</a>&lt;<a class=\"struct\" href=\"rustc_span/def_id/struct.DefId.html\" title=\"struct rustc_span::def_id::DefId\">DefId</a>&gt;</h4></section></summary><div class='docblock'>If the key is a <a href=\"rustc_span/def_id/struct.DefId.html\" title=\"struct rustc_span::def_id::DefId\"><code>DefId</code></a> or <code>DefId</code>–equivalent, return that <code>DefId</code>.\nOtherwise, return <code>None</code>.</div></details><details class=\"toggle method-toggle\" open><summary><section id=\"method.def_id_for_ty_in_cycle\" class=\"method trait-impl\"><a class=\"src rightside\" href=\"src/rustc_middle/query/keys.rs.html#45-47\">Source</a><a href=\"#method.def_id_for_ty_in_cycle\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"rustc_middle/query/keys/trait.Key.html#method.def_id_for_ty_in_cycle\" class=\"fn\">def_id_for_ty_in_cycle</a>(&amp;self) -&gt; <a class=\"enum\" href=\"https://doc.rust-lang.org/nightly/core/option/enum.Option.html\" title=\"enum core::option::Option\">Option</a>&lt;<a class=\"struct\" href=\"rustc_span/def_id/struct.DefId.html\" title=\"struct rustc_span::def_id::DefId\">DefId</a>&gt;</h4></section></summary><div class='docblock'>Used to detect when ADT def ids are used as keys in a cycle for better error reporting.</div></details></div></details>","Key","rustc_middle::query::queries::param_env::Value","rustc_middle::query::queries::param_env::ProvidedValue","rustc_middle::query::queries::param_env_normalized_for_post_analysis::Value","rustc_middle::query::queries::param_env_normalized_for_post_analysis::ProvidedValue"],["<details class=\"toggle implementors-toggle\" open><summary><section id=\"impl-ParamEnv%3C'tcx%3E\" class=\"impl\"><a class=\"src rightside\" href=\"src/rustc_middle/ty/mod.rs.html#980-1013\">Source</a><a href=\"#impl-ParamEnv%3C'tcx%3E\" class=\"anchor\">§</a><h3 class=\"code-header\">impl&lt;'tcx&gt; <a class=\"struct\" href=\"rustc_middle/ty/struct.ParamEnv.html\" title=\"struct rustc_middle::ty::ParamEnv\">ParamEnv</a>&lt;'tcx&gt;</h3></section></summary><div class=\"impl-items\"><details class=\"toggle method-toggle\" open><summary><section id=\"method.empty\" class=\"method\"><a class=\"src rightside\" href=\"src/rustc_middle/ty/mod.rs.html#988-990\">Source</a><h4 class=\"code-header\">pub fn <a href=\"rustc_middle/ty/struct.ParamEnv.html#tymethod.empty\" class=\"fn\">empty</a>() -&gt; Self</h4></section></summary><div class=\"docblock\"><p>Construct a trait environment suitable for contexts where there are\nno where-clauses in scope. In the majority of cases it is incorrect\nto use an empty environment. See the <a href=\"https://rustc-dev-guide.rust-lang.org/param_env/param_env_summary.html\">dev guide section</a>\nfor information on what a <code>ParamEnv</code> is and how to acquire one.</p>\n</div></details><section id=\"method.caller_bounds\" class=\"method\"><a class=\"src rightside\" href=\"src/rustc_middle/ty/mod.rs.html#993-995\">Source</a><h4 class=\"code-header\">pub fn <a href=\"rustc_middle/ty/struct.ParamEnv.html#tymethod.caller_bounds\" class=\"fn\">caller_bounds</a>(self) -&gt; <a class=\"type\" href=\"rustc_middle/ty/type.Clauses.html\" title=\"type rustc_middle::ty::Clauses\">Clauses</a>&lt;'tcx&gt;</h4></section><details class=\"toggle method-toggle\" open><summary><section id=\"method.new\" class=\"method\"><a class=\"src rightside\" href=\"src/rustc_middle/ty/mod.rs.html#999-1001\">Source</a><h4 class=\"code-header\">pub fn <a href=\"rustc_middle/ty/struct.ParamEnv.html#tymethod.new\" class=\"fn\">new</a>(caller_bounds: <a class=\"type\" href=\"rustc_middle/ty/type.Clauses.html\" title=\"type rustc_middle::ty::Clauses\">Clauses</a>&lt;'tcx&gt;) -&gt; Self</h4></section></summary><div class=\"docblock\"><p>Construct a trait environment with the given set of predicates.</p>\n</div></details><details class=\"toggle method-toggle\" open><summary><section id=\"method.without_caller_bounds\" class=\"method\"><a class=\"src rightside\" href=\"src/rustc_middle/ty/mod.rs.html#1005-1007\">Source</a><h4 class=\"code-header\">pub fn <a href=\"rustc_middle/ty/struct.ParamEnv.html#tymethod.without_caller_bounds\" class=\"fn\">without_caller_bounds</a>(self) -&gt; Self</h4></section></summary><div class=\"docblock\"><p>Returns this same environment but with no caller bounds.</p>\n</div></details><details class=\"toggle method-toggle\" open><summary><section id=\"method.and\" class=\"method\"><a class=\"src rightside\" href=\"src/rustc_middle/ty/mod.rs.html#1010-1012\">Source</a><h4 class=\"code-header\">pub fn <a href=\"rustc_middle/ty/struct.ParamEnv.html#tymethod.and\" class=\"fn\">and</a>&lt;T: <a class=\"trait\" href=\"rustc_middle/ty/trait.TypeVisitable.html\" title=\"trait rustc_middle::ty::TypeVisitable\">TypeVisitable</a>&lt;<a class=\"struct\" href=\"rustc_middle/ty/context/struct.TyCtxt.html\" title=\"struct rustc_middle::ty::context::TyCtxt\">TyCtxt</a>&lt;'tcx&gt;&gt;&gt;(\n    self,\n    value: T,\n) -&gt; <a class=\"struct\" href=\"rustc_middle/ty/struct.ParamEnvAnd.html\" title=\"struct rustc_middle::ty::ParamEnvAnd\">ParamEnvAnd</a>&lt;'tcx, T&gt;</h4></section></summary><div class=\"docblock\"><p>Creates a pair of param-env and value for use in queries.</p>\n</div></details></div></details>",0,"rustc_middle::query::queries::param_env::Value","rustc_middle::query::queries::param_env::ProvidedValue","rustc_middle::query::queries::param_env_normalized_for_post_analysis::Value","rustc_middle::query::queries::param_env_normalized_for_post_analysis::ProvidedValue"],["<details class=\"toggle implementors-toggle\" open><summary><section id=\"impl-ParamEnv%3CTyCtxt%3C'tcx%3E%3E-for-ParamEnv%3C'tcx%3E\" class=\"impl\"><a class=\"src rightside\" href=\"src/rustc_middle/ty/mod.rs.html#974-978\">Source</a><a href=\"#impl-ParamEnv%3CTyCtxt%3C'tcx%3E%3E-for-ParamEnv%3C'tcx%3E\" class=\"anchor\">§</a><h3 class=\"code-header\">impl&lt;'tcx&gt; <a class=\"trait\" href=\"rustc_middle/ty/inherent/trait.ParamEnv.html\" title=\"trait rustc_middle::ty::inherent::ParamEnv\">ParamEnv</a>&lt;<a class=\"struct\" href=\"rustc_middle/ty/context/struct.TyCtxt.html\" title=\"struct rustc_middle::ty::context::TyCtxt\">TyCtxt</a>&lt;'tcx&gt;&gt; for <a class=\"struct\" href=\"rustc_middle/ty/struct.ParamEnv.html\" title=\"struct rustc_middle::ty::ParamEnv\">ParamEnv</a>&lt;'tcx&gt;</h3></section></summary><div class=\"impl-items\"><section id=\"method.caller_bounds\" class=\"method trait-impl\"><a class=\"src rightside\" href=\"src/rustc_middle/ty/mod.rs.html#975-977\">Source</a><a href=\"#method.caller_bounds\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"rustc_middle/ty/inherent/trait.ParamEnv.html#tymethod.caller_bounds\" class=\"fn\">caller_bounds</a>(self) -&gt; impl <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/iter/traits/collect/trait.IntoIterator.html\" title=\"trait core::iter::traits::collect::IntoIterator\">IntoIterator</a>&lt;Item = <a class=\"struct\" href=\"rustc_middle/ty/predicate/struct.Clause.html\" title=\"struct rustc_middle::ty::predicate::Clause\">Clause</a>&lt;'tcx&gt;&gt;</h4></section></div></details>","ParamEnv<TyCtxt<'tcx>>","rustc_middle::query::queries::param_env::Value","rustc_middle::query::queries::param_env::ProvidedValue","rustc_middle::query::queries::param_env_normalized_for_post_analysis::Value","rustc_middle::query::queries::param_env_normalized_for_post_analysis::ProvidedValue"],["<details class=\"toggle implementors-toggle\" open><summary><section id=\"impl-PartialEq-for-ParamEnv%3C'tcx%3E\" class=\"impl\"><a class=\"src rightside\" href=\"src/rustc_middle/ty/mod.rs.html#963\">Source</a><a href=\"#impl-PartialEq-for-ParamEnv%3C'tcx%3E\" class=\"anchor\">§</a><h3 class=\"code-header\">impl&lt;'tcx&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/cmp/trait.PartialEq.html\" title=\"trait core::cmp::PartialEq\">PartialEq</a> for <a class=\"struct\" href=\"rustc_middle/ty/struct.ParamEnv.html\" title=\"struct rustc_middle::ty::ParamEnv\">ParamEnv</a>&lt;'tcx&gt;</h3></section></summary><div class=\"impl-items\"><details class=\"toggle method-toggle\" open><summary><section id=\"method.eq\" class=\"method trait-impl\"><a class=\"src rightside\" href=\"src/rustc_middle/ty/mod.rs.html#963\">Source</a><a href=\"#method.eq\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"https://doc.rust-lang.org/nightly/core/cmp/trait.PartialEq.html#tymethod.eq\" class=\"fn\">eq</a>(&amp;self, other: &amp;<a class=\"struct\" href=\"rustc_middle/ty/struct.ParamEnv.html\" title=\"struct rustc_middle::ty::ParamEnv\">ParamEnv</a>&lt;'tcx&gt;) -&gt; <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.bool.html\">bool</a></h4></section></summary><div class='docblock'>Tests for <code>self</code> and <code>other</code> values to be equal, and is used by <code>==</code>.</div></details><details class=\"toggle method-toggle\" open><summary><section id=\"method.ne\" class=\"method trait-impl\"><span class=\"rightside\"><span class=\"since\" title=\"Stable since Rust version 1.0.0\">1.0.0</span> · <a class=\"src\" href=\"https://doc.rust-lang.org/nightly/src/core/cmp.rs.html#261\">Source</a></span><a href=\"#method.ne\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"https://doc.rust-lang.org/nightly/core/cmp/trait.PartialEq.html#method.ne\" class=\"fn\">ne</a>(&amp;self, other: <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.reference.html\">&amp;Rhs</a>) -&gt; <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.bool.html\">bool</a></h4></section></summary><div class='docblock'>Tests for <code>!=</code>. The default implementation is almost always sufficient,\nand should not be overridden without very good reason.</div></details></div></details>","PartialEq","rustc_middle::query::queries::param_env::Value","rustc_middle::query::queries::param_env::ProvidedValue","rustc_middle::query::queries::param_env_normalized_for_post_analysis::Value","rustc_middle::query::queries::param_env_normalized_for_post_analysis::ProvidedValue"],["<details class=\"toggle implementors-toggle\" open><summary><section id=\"impl-TypeFoldable%3CTyCtxt%3C'tcx%3E%3E-for-ParamEnv%3C'tcx%3E\" class=\"impl\"><a class=\"src rightside\" href=\"src/rustc_middle/ty/mod.rs.html#964\">Source</a><a href=\"#impl-TypeFoldable%3CTyCtxt%3C'tcx%3E%3E-for-ParamEnv%3C'tcx%3E\" class=\"anchor\">§</a><h3 class=\"code-header\">impl&lt;'tcx&gt; <a class=\"trait\" href=\"rustc_middle/ty/trait.TypeFoldable.html\" title=\"trait rustc_middle::ty::TypeFoldable\">TypeFoldable</a>&lt;<a class=\"struct\" href=\"rustc_middle/ty/context/struct.TyCtxt.html\" title=\"struct rustc_middle::ty::context::TyCtxt\">TyCtxt</a>&lt;'tcx&gt;&gt; for <a class=\"struct\" href=\"rustc_middle/ty/struct.ParamEnv.html\" title=\"struct rustc_middle::ty::ParamEnv\">ParamEnv</a>&lt;'tcx&gt;</h3></section></summary><div class=\"impl-items\"><details class=\"toggle method-toggle\" open><summary><section id=\"method.try_fold_with\" class=\"method trait-impl\"><a class=\"src rightside\" href=\"src/rustc_middle/ty/mod.rs.html#964\">Source</a><a href=\"#method.try_fold_with\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"rustc_middle/ty/trait.TypeFoldable.html#tymethod.try_fold_with\" class=\"fn\">try_fold_with</a>&lt;__F: <a class=\"trait\" href=\"rustc_middle/ty/trait.FallibleTypeFolder.html\" title=\"trait rustc_middle::ty::FallibleTypeFolder\">FallibleTypeFolder</a>&lt;<a class=\"struct\" href=\"rustc_middle/ty/context/struct.TyCtxt.html\" title=\"struct rustc_middle::ty::context::TyCtxt\">TyCtxt</a>&lt;'tcx&gt;&gt;&gt;(\n    self,\n    __folder: <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.reference.html\">&amp;mut __F</a>,\n) -&gt; <a class=\"enum\" href=\"https://doc.rust-lang.org/nightly/core/result/enum.Result.html\" title=\"enum core::result::Result\">Result</a>&lt;Self, __F::<a class=\"associatedtype\" href=\"rustc_middle/ty/trait.FallibleTypeFolder.html#associatedtype.Error\" title=\"type rustc_middle::ty::FallibleTypeFolder::Error\">Error</a>&gt;</h4></section></summary><div class='docblock'>The entry point for folding. To fold a value <code>t</code> with a folder <code>f</code>\ncall: <code>t.try_fold_with(f)</code>. <a href=\"rustc_middle/ty/trait.TypeFoldable.html#tymethod.try_fold_with\">Read more</a></div></details><details class=\"toggle method-toggle\" open><summary><section id=\"method.fold_with\" class=\"method trait-impl\"><a class=\"src rightside\" href=\"src/rustc_type_ir/fold.rs.html#92\">Source</a><a href=\"#method.fold_with\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"rustc_middle/ty/trait.TypeFoldable.html#method.fold_with\" class=\"fn\">fold_with</a>&lt;F&gt;(self, folder: <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.reference.html\">&amp;mut F</a>) -&gt; Self<div class=\"where\">where\n    F: <a class=\"trait\" href=\"rustc_middle/ty/trait.TypeFolder.html\" title=\"trait rustc_middle::ty::TypeFolder\">TypeFolder</a>&lt;I&gt;,</div></h4></section></summary><div class='docblock'>A convenient alternative to <code>try_fold_with</code> for use with infallible\nfolders. Do not override this method, to ensure coherence with\n<code>try_fold_with</code>.</div></details></div></details>","TypeFoldable<TyCtxt<'tcx>>","rustc_middle::query::queries::param_env::Value","rustc_middle::query::queries::param_env::ProvidedValue","rustc_middle::query::queries::param_env_normalized_for_post_analysis::Value","rustc_middle::query::queries::param_env_normalized_for_post_analysis::ProvidedValue"],["<details class=\"toggle implementors-toggle\" open><summary><section id=\"impl-TypeVisitable%3CTyCtxt%3C'tcx%3E%3E-for-ParamEnv%3C'tcx%3E\" class=\"impl\"><a class=\"src rightside\" href=\"src/rustc_middle/ty/mod.rs.html#964\">Source</a><a href=\"#impl-TypeVisitable%3CTyCtxt%3C'tcx%3E%3E-for-ParamEnv%3C'tcx%3E\" class=\"anchor\">§</a><h3 class=\"code-header\">impl&lt;'tcx&gt; <a class=\"trait\" href=\"rustc_middle/ty/trait.TypeVisitable.html\" title=\"trait rustc_middle::ty::TypeVisitable\">TypeVisitable</a>&lt;<a class=\"struct\" href=\"rustc_middle/ty/context/struct.TyCtxt.html\" title=\"struct rustc_middle::ty::context::TyCtxt\">TyCtxt</a>&lt;'tcx&gt;&gt; for <a class=\"struct\" href=\"rustc_middle/ty/struct.ParamEnv.html\" title=\"struct rustc_middle::ty::ParamEnv\">ParamEnv</a>&lt;'tcx&gt;</h3></section></summary><div class=\"impl-items\"><details class=\"toggle method-toggle\" open><summary><section id=\"method.visit_with\" class=\"method trait-impl\"><a class=\"src rightside\" href=\"src/rustc_middle/ty/mod.rs.html#964\">Source</a><a href=\"#method.visit_with\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"rustc_middle/ty/trait.TypeVisitable.html#tymethod.visit_with\" class=\"fn\">visit_with</a>&lt;__V: <a class=\"trait\" href=\"rustc_middle/ty/trait.TypeVisitor.html\" title=\"trait rustc_middle::ty::TypeVisitor\">TypeVisitor</a>&lt;<a class=\"struct\" href=\"rustc_middle/ty/context/struct.TyCtxt.html\" title=\"struct rustc_middle::ty::context::TyCtxt\">TyCtxt</a>&lt;'tcx&gt;&gt;&gt;(\n    &amp;self,\n    __visitor: <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.reference.html\">&amp;mut __V</a>,\n) -&gt; __V::<a class=\"associatedtype\" href=\"rustc_middle/ty/trait.TypeVisitor.html#associatedtype.Result\" title=\"type rustc_middle::ty::TypeVisitor::Result\">Result</a></h4></section></summary><div class='docblock'>The entry point for visiting. To visit a value <code>t</code> with a visitor <code>v</code>\ncall: <code>t.visit_with(v)</code>. <a href=\"rustc_middle/ty/trait.TypeVisitable.html#tymethod.visit_with\">Read more</a></div></details></div></details>","TypeVisitable<TyCtxt<'tcx>>","rustc_middle::query::queries::param_env::Value","rustc_middle::query::queries::param_env::ProvidedValue","rustc_middle::query::queries::param_env_normalized_for_post_analysis::Value","rustc_middle::query::queries::param_env_normalized_for_post_analysis::ProvidedValue"],["<section id=\"impl-Copy-for-ParamEnv%3C'tcx%3E\" class=\"impl\"><a class=\"src rightside\" href=\"src/rustc_middle/ty/mod.rs.html#963\">Source</a><a href=\"#impl-Copy-for-ParamEnv%3C'tcx%3E\" class=\"anchor\">§</a><h3 class=\"code-header\">impl&lt;'tcx&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/marker/trait.Copy.html\" title=\"trait core::marker::Copy\">Copy</a> for <a class=\"struct\" href=\"rustc_middle/ty/struct.ParamEnv.html\" title=\"struct rustc_middle::ty::ParamEnv\">ParamEnv</a>&lt;'tcx&gt;</h3></section>","Copy","rustc_middle::query::queries::param_env::Value","rustc_middle::query::queries::param_env::ProvidedValue","rustc_middle::query::queries::param_env_normalized_for_post_analysis::Value","rustc_middle::query::queries::param_env_normalized_for_post_analysis::ProvidedValue"],["<section id=\"impl-Eq-for-ParamEnv%3C'tcx%3E\" class=\"impl\"><a class=\"src rightside\" href=\"src/rustc_middle/ty/mod.rs.html#963\">Source</a><a href=\"#impl-Eq-for-ParamEnv%3C'tcx%3E\" class=\"anchor\">§</a><h3 class=\"code-header\">impl&lt;'tcx&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/cmp/trait.Eq.html\" title=\"trait core::cmp::Eq\">Eq</a> for <a class=\"struct\" href=\"rustc_middle/ty/struct.ParamEnv.html\" title=\"struct rustc_middle::ty::ParamEnv\">ParamEnv</a>&lt;'tcx&gt;</h3></section>","Eq","rustc_middle::query::queries::param_env::Value","rustc_middle::query::queries::param_env::ProvidedValue","rustc_middle::query::queries::param_env_normalized_for_post_analysis::Value","rustc_middle::query::queries::param_env_normalized_for_post_analysis::ProvidedValue"],["<section id=\"impl-StructuralPartialEq-for-ParamEnv%3C'tcx%3E\" class=\"impl\"><a class=\"src rightside\" href=\"src/rustc_middle/ty/mod.rs.html#963\">Source</a><a href=\"#impl-StructuralPartialEq-for-ParamEnv%3C'tcx%3E\" class=\"anchor\">§</a><h3 class=\"code-header\">impl&lt;'tcx&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/marker/trait.StructuralPartialEq.html\" title=\"trait core::marker::StructuralPartialEq\">StructuralPartialEq</a> for <a class=\"struct\" href=\"rustc_middle/ty/struct.ParamEnv.html\" title=\"struct rustc_middle::ty::ParamEnv\">ParamEnv</a>&lt;'tcx&gt;</h3></section>","StructuralPartialEq","rustc_middle::query::queries::param_env::Value","rustc_middle::query::queries::param_env::ProvidedValue","rustc_middle::query::queries::param_env_normalized_for_post_analysis::Value","rustc_middle::query::queries::param_env_normalized_for_post_analysis::ProvidedValue"]]]]);
    if (window.register_type_impls) {
        window.register_type_impls(type_impls);
    } else {
        window.pending_type_impls = type_impls;
    }
})()
//{"start":55,"fragment_lengths":[36205]}