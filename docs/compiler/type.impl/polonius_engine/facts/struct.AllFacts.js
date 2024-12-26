(function() {
    var type_impls = Object.fromEntries([["rustc_borrowck",[["<details class=\"toggle implementors-toggle\" open><summary><section id=\"impl-Clone-for-AllFacts%3CT%3E\" class=\"impl\"><a class=\"src rightside\" href=\"https://docs.rs/polonius-engine/0.13.0/src/polonius_engine/facts.rs.html#5\">Source</a><a href=\"#impl-Clone-for-AllFacts%3CT%3E\" class=\"anchor\">§</a><h3 class=\"code-header\">impl&lt;T&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/clone/trait.Clone.html\" title=\"trait core::clone::Clone\">Clone</a> for <a class=\"struct\" href=\"https://docs.rs/polonius-engine/0.13.0/polonius_engine/facts/struct.AllFacts.html\" title=\"struct polonius_engine::facts::AllFacts\">AllFacts</a>&lt;T&gt;<div class=\"where\">where\n    T: <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/clone/trait.Clone.html\" title=\"trait core::clone::Clone\">Clone</a> + <a class=\"trait\" href=\"https://docs.rs/polonius-engine/0.13.0/polonius_engine/facts/trait.FactTypes.html\" title=\"trait polonius_engine::facts::FactTypes\">FactTypes</a>,\n    &lt;T as <a class=\"trait\" href=\"https://docs.rs/polonius-engine/0.13.0/polonius_engine/facts/trait.FactTypes.html\" title=\"trait polonius_engine::facts::FactTypes\">FactTypes</a>&gt;::<a class=\"associatedtype\" href=\"https://docs.rs/polonius-engine/0.13.0/polonius_engine/facts/trait.FactTypes.html#associatedtype.Origin\" title=\"type polonius_engine::facts::FactTypes::Origin\">Origin</a>: <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/clone/trait.Clone.html\" title=\"trait core::clone::Clone\">Clone</a>,\n    &lt;T as <a class=\"trait\" href=\"https://docs.rs/polonius-engine/0.13.0/polonius_engine/facts/trait.FactTypes.html\" title=\"trait polonius_engine::facts::FactTypes\">FactTypes</a>&gt;::<a class=\"associatedtype\" href=\"https://docs.rs/polonius-engine/0.13.0/polonius_engine/facts/trait.FactTypes.html#associatedtype.Loan\" title=\"type polonius_engine::facts::FactTypes::Loan\">Loan</a>: <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/clone/trait.Clone.html\" title=\"trait core::clone::Clone\">Clone</a>,\n    &lt;T as <a class=\"trait\" href=\"https://docs.rs/polonius-engine/0.13.0/polonius_engine/facts/trait.FactTypes.html\" title=\"trait polonius_engine::facts::FactTypes\">FactTypes</a>&gt;::<a class=\"associatedtype\" href=\"https://docs.rs/polonius-engine/0.13.0/polonius_engine/facts/trait.FactTypes.html#associatedtype.Point\" title=\"type polonius_engine::facts::FactTypes::Point\">Point</a>: <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/clone/trait.Clone.html\" title=\"trait core::clone::Clone\">Clone</a>,\n    &lt;T as <a class=\"trait\" href=\"https://docs.rs/polonius-engine/0.13.0/polonius_engine/facts/trait.FactTypes.html\" title=\"trait polonius_engine::facts::FactTypes\">FactTypes</a>&gt;::<a class=\"associatedtype\" href=\"https://docs.rs/polonius-engine/0.13.0/polonius_engine/facts/trait.FactTypes.html#associatedtype.Variable\" title=\"type polonius_engine::facts::FactTypes::Variable\">Variable</a>: <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/clone/trait.Clone.html\" title=\"trait core::clone::Clone\">Clone</a>,\n    &lt;T as <a class=\"trait\" href=\"https://docs.rs/polonius-engine/0.13.0/polonius_engine/facts/trait.FactTypes.html\" title=\"trait polonius_engine::facts::FactTypes\">FactTypes</a>&gt;::<a class=\"associatedtype\" href=\"https://docs.rs/polonius-engine/0.13.0/polonius_engine/facts/trait.FactTypes.html#associatedtype.Path\" title=\"type polonius_engine::facts::FactTypes::Path\">Path</a>: <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/clone/trait.Clone.html\" title=\"trait core::clone::Clone\">Clone</a>,</div></h3></section></summary><div class=\"impl-items\"><details class=\"toggle method-toggle\" open><summary><section id=\"method.clone\" class=\"method trait-impl\"><a class=\"src rightside\" href=\"https://docs.rs/polonius-engine/0.13.0/src/polonius_engine/facts.rs.html#5\">Source</a><a href=\"#method.clone\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"https://doc.rust-lang.org/nightly/core/clone/trait.Clone.html#tymethod.clone\" class=\"fn\">clone</a>(&amp;self) -&gt; <a class=\"struct\" href=\"https://docs.rs/polonius-engine/0.13.0/polonius_engine/facts/struct.AllFacts.html\" title=\"struct polonius_engine::facts::AllFacts\">AllFacts</a>&lt;T&gt;</h4></section></summary><div class='docblock'>Returns a copy of the value. <a href=\"https://doc.rust-lang.org/nightly/core/clone/trait.Clone.html#tymethod.clone\">Read more</a></div></details><details class=\"toggle method-toggle\" open><summary><section id=\"method.clone_from\" class=\"method trait-impl\"><span class=\"rightside\"><span class=\"since\" title=\"Stable since Rust version 1.0.0\">1.0.0</span> · <a class=\"src\" href=\"https://doc.rust-lang.org/nightly/src/core/clone.rs.html#174\">Source</a></span><a href=\"#method.clone_from\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"https://doc.rust-lang.org/nightly/core/clone/trait.Clone.html#method.clone_from\" class=\"fn\">clone_from</a>(&amp;mut self, source: &amp;Self)</h4></section></summary><div class='docblock'>Performs copy-assignment from <code>source</code>. <a href=\"https://doc.rust-lang.org/nightly/core/clone/trait.Clone.html#method.clone_from\">Read more</a></div></details></div></details>","Clone","rustc_borrowck::facts::AllFacts"],["<details class=\"toggle implementors-toggle\" open><summary><section id=\"impl-Debug-for-AllFacts%3CT%3E\" class=\"impl\"><a class=\"src rightside\" href=\"https://docs.rs/polonius-engine/0.13.0/src/polonius_engine/facts.rs.html#5\">Source</a><a href=\"#impl-Debug-for-AllFacts%3CT%3E\" class=\"anchor\">§</a><h3 class=\"code-header\">impl&lt;T&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/fmt/trait.Debug.html\" title=\"trait core::fmt::Debug\">Debug</a> for <a class=\"struct\" href=\"https://docs.rs/polonius-engine/0.13.0/polonius_engine/facts/struct.AllFacts.html\" title=\"struct polonius_engine::facts::AllFacts\">AllFacts</a>&lt;T&gt;<div class=\"where\">where\n    T: <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/fmt/trait.Debug.html\" title=\"trait core::fmt::Debug\">Debug</a> + <a class=\"trait\" href=\"https://docs.rs/polonius-engine/0.13.0/polonius_engine/facts/trait.FactTypes.html\" title=\"trait polonius_engine::facts::FactTypes\">FactTypes</a>,\n    &lt;T as <a class=\"trait\" href=\"https://docs.rs/polonius-engine/0.13.0/polonius_engine/facts/trait.FactTypes.html\" title=\"trait polonius_engine::facts::FactTypes\">FactTypes</a>&gt;::<a class=\"associatedtype\" href=\"https://docs.rs/polonius-engine/0.13.0/polonius_engine/facts/trait.FactTypes.html#associatedtype.Origin\" title=\"type polonius_engine::facts::FactTypes::Origin\">Origin</a>: <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/fmt/trait.Debug.html\" title=\"trait core::fmt::Debug\">Debug</a>,\n    &lt;T as <a class=\"trait\" href=\"https://docs.rs/polonius-engine/0.13.0/polonius_engine/facts/trait.FactTypes.html\" title=\"trait polonius_engine::facts::FactTypes\">FactTypes</a>&gt;::<a class=\"associatedtype\" href=\"https://docs.rs/polonius-engine/0.13.0/polonius_engine/facts/trait.FactTypes.html#associatedtype.Loan\" title=\"type polonius_engine::facts::FactTypes::Loan\">Loan</a>: <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/fmt/trait.Debug.html\" title=\"trait core::fmt::Debug\">Debug</a>,\n    &lt;T as <a class=\"trait\" href=\"https://docs.rs/polonius-engine/0.13.0/polonius_engine/facts/trait.FactTypes.html\" title=\"trait polonius_engine::facts::FactTypes\">FactTypes</a>&gt;::<a class=\"associatedtype\" href=\"https://docs.rs/polonius-engine/0.13.0/polonius_engine/facts/trait.FactTypes.html#associatedtype.Point\" title=\"type polonius_engine::facts::FactTypes::Point\">Point</a>: <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/fmt/trait.Debug.html\" title=\"trait core::fmt::Debug\">Debug</a>,\n    &lt;T as <a class=\"trait\" href=\"https://docs.rs/polonius-engine/0.13.0/polonius_engine/facts/trait.FactTypes.html\" title=\"trait polonius_engine::facts::FactTypes\">FactTypes</a>&gt;::<a class=\"associatedtype\" href=\"https://docs.rs/polonius-engine/0.13.0/polonius_engine/facts/trait.FactTypes.html#associatedtype.Variable\" title=\"type polonius_engine::facts::FactTypes::Variable\">Variable</a>: <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/fmt/trait.Debug.html\" title=\"trait core::fmt::Debug\">Debug</a>,\n    &lt;T as <a class=\"trait\" href=\"https://docs.rs/polonius-engine/0.13.0/polonius_engine/facts/trait.FactTypes.html\" title=\"trait polonius_engine::facts::FactTypes\">FactTypes</a>&gt;::<a class=\"associatedtype\" href=\"https://docs.rs/polonius-engine/0.13.0/polonius_engine/facts/trait.FactTypes.html#associatedtype.Path\" title=\"type polonius_engine::facts::FactTypes::Path\">Path</a>: <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/fmt/trait.Debug.html\" title=\"trait core::fmt::Debug\">Debug</a>,</div></h3></section></summary><div class=\"impl-items\"><details class=\"toggle method-toggle\" open><summary><section id=\"method.fmt\" class=\"method trait-impl\"><a class=\"src rightside\" href=\"https://docs.rs/polonius-engine/0.13.0/src/polonius_engine/facts.rs.html#5\">Source</a><a href=\"#method.fmt\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"https://doc.rust-lang.org/nightly/core/fmt/trait.Debug.html#tymethod.fmt\" class=\"fn\">fmt</a>(&amp;self, f: &amp;mut <a class=\"struct\" href=\"https://doc.rust-lang.org/nightly/core/fmt/struct.Formatter.html\" title=\"struct core::fmt::Formatter\">Formatter</a>&lt;'_&gt;) -&gt; <a class=\"enum\" href=\"https://doc.rust-lang.org/nightly/core/result/enum.Result.html\" title=\"enum core::result::Result\">Result</a>&lt;<a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.unit.html\">()</a>, <a class=\"struct\" href=\"https://doc.rust-lang.org/nightly/core/fmt/struct.Error.html\" title=\"struct core::fmt::Error\">Error</a>&gt;</h4></section></summary><div class='docblock'>Formats the value using the given formatter. <a href=\"https://doc.rust-lang.org/nightly/core/fmt/trait.Debug.html#tymethod.fmt\">Read more</a></div></details></div></details>","Debug","rustc_borrowck::facts::AllFacts"],["<details class=\"toggle implementors-toggle\" open><summary><section id=\"impl-Default-for-AllFacts%3CT%3E\" class=\"impl\"><a class=\"src rightside\" href=\"https://docs.rs/polonius-engine/0.13.0/src/polonius_engine/facts.rs.html#92\">Source</a><a href=\"#impl-Default-for-AllFacts%3CT%3E\" class=\"anchor\">§</a><h3 class=\"code-header\">impl&lt;T&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/default/trait.Default.html\" title=\"trait core::default::Default\">Default</a> for <a class=\"struct\" href=\"https://docs.rs/polonius-engine/0.13.0/polonius_engine/facts/struct.AllFacts.html\" title=\"struct polonius_engine::facts::AllFacts\">AllFacts</a>&lt;T&gt;<div class=\"where\">where\n    T: <a class=\"trait\" href=\"https://docs.rs/polonius-engine/0.13.0/polonius_engine/facts/trait.FactTypes.html\" title=\"trait polonius_engine::facts::FactTypes\">FactTypes</a>,</div></h3></section></summary><div class=\"impl-items\"><details class=\"toggle method-toggle\" open><summary><section id=\"method.default\" class=\"method trait-impl\"><a class=\"src rightside\" href=\"https://docs.rs/polonius-engine/0.13.0/src/polonius_engine/facts.rs.html#93\">Source</a><a href=\"#method.default\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"https://doc.rust-lang.org/nightly/core/default/trait.Default.html#tymethod.default\" class=\"fn\">default</a>() -&gt; <a class=\"struct\" href=\"https://docs.rs/polonius-engine/0.13.0/polonius_engine/facts/struct.AllFacts.html\" title=\"struct polonius_engine::facts::AllFacts\">AllFacts</a>&lt;T&gt;</h4></section></summary><div class='docblock'>Returns the “default value” for a type. <a href=\"https://doc.rust-lang.org/nightly/core/default/trait.Default.html#tymethod.default\">Read more</a></div></details></div></details>","Default","rustc_borrowck::facts::AllFacts"]]]]);
    if (window.register_type_impls) {
        window.register_type_impls(type_impls);
    } else {
        window.pending_type_impls = type_impls;
    }
})()
//{"start":55,"fragment_lengths":[12270]}