(function() {
    var type_impls = Object.fromEntries([["rustc_data_structures",[["<details class=\"toggle implementors-toggle\" open><summary><section id=\"impl-Debug-for-Entry%3C'_,+K,+V%3E\" class=\"impl\"><a class=\"src rightside\" href=\"https://docs.rs/indexmap/2.7.0/src/indexmap/map/core/entry.rs.html#133\">Source</a><a href=\"#impl-Debug-for-Entry%3C'_,+K,+V%3E\" class=\"anchor\">§</a><h3 class=\"code-header\">impl&lt;K, V&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/fmt/trait.Debug.html\" title=\"trait core::fmt::Debug\">Debug</a> for <a class=\"enum\" href=\"https://docs.rs/indexmap/2.7.0/indexmap/map/core/entry/enum.Entry.html\" title=\"enum indexmap::map::core::entry::Entry\">Entry</a>&lt;'_, K, V&gt;<div class=\"where\">where\n    K: <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/fmt/trait.Debug.html\" title=\"trait core::fmt::Debug\">Debug</a>,\n    V: <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/fmt/trait.Debug.html\" title=\"trait core::fmt::Debug\">Debug</a>,</div></h3></section></summary><div class=\"impl-items\"><details class=\"toggle method-toggle\" open><summary><section id=\"method.fmt\" class=\"method trait-impl\"><a class=\"src rightside\" href=\"https://docs.rs/indexmap/2.7.0/src/indexmap/map/core/entry.rs.html#134\">Source</a><a href=\"#method.fmt\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"https://doc.rust-lang.org/nightly/core/fmt/trait.Debug.html#tymethod.fmt\" class=\"fn\">fmt</a>(&amp;self, f: &amp;mut <a class=\"struct\" href=\"https://doc.rust-lang.org/nightly/core/fmt/struct.Formatter.html\" title=\"struct core::fmt::Formatter\">Formatter</a>&lt;'_&gt;) -&gt; <a class=\"enum\" href=\"https://doc.rust-lang.org/nightly/core/result/enum.Result.html\" title=\"enum core::result::Result\">Result</a>&lt;<a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.unit.html\">()</a>, <a class=\"struct\" href=\"https://doc.rust-lang.org/nightly/core/fmt/struct.Error.html\" title=\"struct core::fmt::Error\">Error</a>&gt;</h4></section></summary><div class='docblock'>Formats the value using the given formatter. <a href=\"https://doc.rust-lang.org/nightly/core/fmt/trait.Debug.html#tymethod.fmt\">Read more</a></div></details></div></details>","Debug","rustc_data_structures::fx::IndexEntry"],["<details class=\"toggle implementors-toggle\" open><summary><section id=\"impl-Entry%3C'a,+K,+V%3E\" class=\"impl\"><a class=\"src rightside\" href=\"https://docs.rs/indexmap/2.7.0/src/indexmap/map/core/entry.rs.html#33\">Source</a><a href=\"#impl-Entry%3C'a,+K,+V%3E\" class=\"anchor\">§</a><h3 class=\"code-header\">impl&lt;'a, K, V&gt; <a class=\"enum\" href=\"https://docs.rs/indexmap/2.7.0/indexmap/map/core/entry/enum.Entry.html\" title=\"enum indexmap::map::core::entry::Entry\">Entry</a>&lt;'a, K, V&gt;</h3></section></summary><div class=\"impl-items\"><details class=\"toggle method-toggle\" open><summary><section id=\"method.index\" class=\"method\"><a class=\"src rightside\" href=\"https://docs.rs/indexmap/2.7.0/src/indexmap/map/core/entry.rs.html#35\">Source</a><h4 class=\"code-header\">pub fn <a href=\"https://docs.rs/indexmap/2.7.0/indexmap/map/core/entry/enum.Entry.html#tymethod.index\" class=\"fn\">index</a>(&amp;self) -&gt; <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.usize.html\">usize</a></h4></section></summary><div class=\"docblock\"><p>Return the index where the key-value pair exists or will be inserted.</p>\n</div></details><details class=\"toggle method-toggle\" open><summary><section id=\"method.insert_entry\" class=\"method\"><a class=\"src rightside\" href=\"https://docs.rs/indexmap/2.7.0/src/indexmap/map/core/entry.rs.html#45\">Source</a><h4 class=\"code-header\">pub fn <a href=\"https://docs.rs/indexmap/2.7.0/indexmap/map/core/entry/enum.Entry.html#tymethod.insert_entry\" class=\"fn\">insert_entry</a>(self, value: V) -&gt; <a class=\"struct\" href=\"https://docs.rs/indexmap/2.7.0/indexmap/map/core/entry/struct.OccupiedEntry.html\" title=\"struct indexmap::map::core::entry::OccupiedEntry\">OccupiedEntry</a>&lt;'a, K, V&gt;</h4></section></summary><div class=\"docblock\"><p>Sets the value of the entry (after inserting if vacant), and returns an <code>OccupiedEntry</code>.</p>\n<p>Computes in <strong>O(1)</strong> time (amortized average).</p>\n</div></details><details class=\"toggle method-toggle\" open><summary><section id=\"method.or_insert\" class=\"method\"><a class=\"src rightside\" href=\"https://docs.rs/indexmap/2.7.0/src/indexmap/map/core/entry.rs.html#59\">Source</a><h4 class=\"code-header\">pub fn <a href=\"https://docs.rs/indexmap/2.7.0/indexmap/map/core/entry/enum.Entry.html#tymethod.or_insert\" class=\"fn\">or_insert</a>(self, default: V) -&gt; <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.reference.html\">&amp;'a mut V</a></h4></section></summary><div class=\"docblock\"><p>Inserts the given default value in the entry if it is vacant and returns a mutable\nreference to it. Otherwise a mutable reference to an already existent value is returned.</p>\n<p>Computes in <strong>O(1)</strong> time (amortized average).</p>\n</div></details><details class=\"toggle method-toggle\" open><summary><section id=\"method.or_insert_with\" class=\"method\"><a class=\"src rightside\" href=\"https://docs.rs/indexmap/2.7.0/src/indexmap/map/core/entry.rs.html#70-72\">Source</a><h4 class=\"code-header\">pub fn <a href=\"https://docs.rs/indexmap/2.7.0/indexmap/map/core/entry/enum.Entry.html#tymethod.or_insert_with\" class=\"fn\">or_insert_with</a>&lt;F&gt;(self, call: F) -&gt; <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.reference.html\">&amp;'a mut V</a><div class=\"where\">where\n    F: <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/ops/function/trait.FnOnce.html\" title=\"trait core::ops::function::FnOnce\">FnOnce</a>() -&gt; V,</div></h4></section></summary><div class=\"docblock\"><p>Inserts the result of the <code>call</code> function in the entry if it is vacant and returns a mutable\nreference to it. Otherwise a mutable reference to an already existent value is returned.</p>\n<p>Computes in <strong>O(1)</strong> time (amortized average).</p>\n</div></details><details class=\"toggle method-toggle\" open><summary><section id=\"method.or_insert_with_key\" class=\"method\"><a class=\"src rightside\" href=\"https://docs.rs/indexmap/2.7.0/src/indexmap/map/core/entry.rs.html#85-87\">Source</a><h4 class=\"code-header\">pub fn <a href=\"https://docs.rs/indexmap/2.7.0/indexmap/map/core/entry/enum.Entry.html#tymethod.or_insert_with_key\" class=\"fn\">or_insert_with_key</a>&lt;F&gt;(self, call: F) -&gt; <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.reference.html\">&amp;'a mut V</a><div class=\"where\">where\n    F: <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/ops/function/trait.FnOnce.html\" title=\"trait core::ops::function::FnOnce\">FnOnce</a>(<a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.reference.html\">&amp;K</a>) -&gt; V,</div></h4></section></summary><div class=\"docblock\"><p>Inserts the result of the <code>call</code> function with a reference to the entry’s key if it is\nvacant, and returns a mutable reference to the new value. Otherwise a mutable reference to\nan already existent value is returned.</p>\n<p>Computes in <strong>O(1)</strong> time (amortized average).</p>\n</div></details><details class=\"toggle method-toggle\" open><summary><section id=\"method.key\" class=\"method\"><a class=\"src rightside\" href=\"https://docs.rs/indexmap/2.7.0/src/indexmap/map/core/entry.rs.html#100\">Source</a><h4 class=\"code-header\">pub fn <a href=\"https://docs.rs/indexmap/2.7.0/indexmap/map/core/entry/enum.Entry.html#tymethod.key\" class=\"fn\">key</a>(&amp;self) -&gt; <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.reference.html\">&amp;K</a></h4></section></summary><div class=\"docblock\"><p>Gets a reference to the entry’s key, either within the map if occupied,\nor else the new key that was used to find the entry.</p>\n</div></details><details class=\"toggle method-toggle\" open><summary><section id=\"method.and_modify\" class=\"method\"><a class=\"src rightside\" href=\"https://docs.rs/indexmap/2.7.0/src/indexmap/map/core/entry.rs.html#108-110\">Source</a><h4 class=\"code-header\">pub fn <a href=\"https://docs.rs/indexmap/2.7.0/indexmap/map/core/entry/enum.Entry.html#tymethod.and_modify\" class=\"fn\">and_modify</a>&lt;F&gt;(self, f: F) -&gt; <a class=\"enum\" href=\"https://docs.rs/indexmap/2.7.0/indexmap/map/core/entry/enum.Entry.html\" title=\"enum indexmap::map::core::entry::Entry\">Entry</a>&lt;'a, K, V&gt;<div class=\"where\">where\n    F: <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/ops/function/trait.FnOnce.html\" title=\"trait core::ops::function::FnOnce\">FnOnce</a>(<a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.reference.html\">&amp;mut V</a>),</div></h4></section></summary><div class=\"docblock\"><p>Modifies the entry if it is occupied.</p>\n</div></details><details class=\"toggle method-toggle\" open><summary><section id=\"method.or_default\" class=\"method\"><a class=\"src rightside\" href=\"https://docs.rs/indexmap/2.7.0/src/indexmap/map/core/entry.rs.html#122-124\">Source</a><h4 class=\"code-header\">pub fn <a href=\"https://docs.rs/indexmap/2.7.0/indexmap/map/core/entry/enum.Entry.html#tymethod.or_default\" class=\"fn\">or_default</a>(self) -&gt; <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.reference.html\">&amp;'a mut V</a><div class=\"where\">where\n    V: <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/default/trait.Default.html\" title=\"trait core::default::Default\">Default</a>,</div></h4></section></summary><div class=\"docblock\"><p>Inserts a default-constructed value in the entry if it is vacant and returns a mutable\nreference to it. Otherwise a mutable reference to an already existent value is returned.</p>\n<p>Computes in <strong>O(1)</strong> time (amortized average).</p>\n</div></details></div></details>",0,"rustc_data_structures::fx::IndexEntry"],["<details class=\"toggle implementors-toggle\" open><summary><section id=\"impl-MutableEntryKey-for-Entry%3C'_,+K,+V%3E\" class=\"impl\"><a class=\"src rightside\" href=\"https://docs.rs/indexmap/2.7.0/src/indexmap/map/mutable.rs.html#118\">Source</a><a href=\"#impl-MutableEntryKey-for-Entry%3C'_,+K,+V%3E\" class=\"anchor\">§</a><h3 class=\"code-header\">impl&lt;K, V&gt; <a class=\"trait\" href=\"https://docs.rs/indexmap/2.7.0/indexmap/map/mutable/trait.MutableEntryKey.html\" title=\"trait indexmap::map::mutable::MutableEntryKey\">MutableEntryKey</a> for <a class=\"enum\" href=\"https://docs.rs/indexmap/2.7.0/indexmap/map/core/entry/enum.Entry.html\" title=\"enum indexmap::map::core::entry::Entry\">Entry</a>&lt;'_, K, V&gt;</h3><div class=\"docblock\"><p>Opt-in mutable access to <a href=\"https://docs.rs/indexmap/2.7.0/indexmap/map/core/entry/enum.Entry.html\" title=\"enum indexmap::map::core::entry::Entry\"><code>Entry</code></a> keys.</p>\n</div></section></summary><div class=\"docblock\"><p>See <a href=\"https://docs.rs/indexmap/2.7.0/indexmap/map/mutable/trait.MutableEntryKey.html\" title=\"trait indexmap::map::mutable::MutableEntryKey\"><code>MutableEntryKey</code></a> for more information.</p>\n</div><div class=\"impl-items\"><section id=\"associatedtype.Key\" class=\"associatedtype trait-impl\"><a class=\"src rightside\" href=\"https://docs.rs/indexmap/2.7.0/src/indexmap/map/mutable.rs.html#119\">Source</a><a href=\"#associatedtype.Key\" class=\"anchor\">§</a><h4 class=\"code-header\">type <a href=\"https://docs.rs/indexmap/2.7.0/indexmap/map/mutable/trait.MutableEntryKey.html#associatedtype.Key\" class=\"associatedtype\">Key</a> = K</h4></section><details class=\"toggle method-toggle\" open><summary><section id=\"method.key_mut\" class=\"method trait-impl\"><a class=\"src rightside\" href=\"https://docs.rs/indexmap/2.7.0/src/indexmap/map/mutable.rs.html#120\">Source</a><a href=\"#method.key_mut\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"https://docs.rs/indexmap/2.7.0/indexmap/map/mutable/trait.MutableEntryKey.html#tymethod.key_mut\" class=\"fn\">key_mut</a>(&amp;mut self) -&gt; <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.reference.html\">&amp;mut K</a></h4></section></summary><div class='docblock'>Gets a mutable reference to the entry’s key, either within the map if occupied,\nor else the new key that was used to find the entry.</div></details></div></details>","MutableEntryKey","rustc_data_structures::fx::IndexEntry"]]]]);
    if (window.register_type_impls) {
        window.register_type_impls(type_impls);
    } else {
        window.pending_type_impls = type_impls;
    }
})()
//{"start":55,"fragment_lengths":[12801]}