(function() {
    var implementors = Object.fromEntries([["allocator_api2",[["impl&lt;T: ?<a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/marker/trait.Sized.html\" title=\"trait core::marker::Sized\">Sized</a>, A: <a class=\"trait\" href=\"allocator_api2/alloc/trait.Allocator.html\" title=\"trait allocator_api2::alloc::Allocator\">Allocator</a>&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/borrow/trait.Borrow.html\" title=\"trait core::borrow::Borrow\">Borrow</a>&lt;T&gt; for <a class=\"struct\" href=\"allocator_api2/boxed/struct.Box.html\" title=\"struct allocator_api2::boxed::Box\">Box</a>&lt;T, A&gt;"]]],["arrayvec",[["impl&lt;A&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/borrow/trait.Borrow.html\" title=\"trait core::borrow::Borrow\">Borrow</a>&lt;<a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.str.html\">str</a>&gt; for <a class=\"struct\" href=\"arrayvec/struct.ArrayString.html\" title=\"struct arrayvec::ArrayString\">ArrayString</a>&lt;A&gt;<div class=\"where\">where\n    A: <a class=\"trait\" href=\"arrayvec/trait.Array.html\" title=\"trait arrayvec::Array\">Array</a>&lt;Item = <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.u8.html\">u8</a>&gt; + <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/marker/trait.Copy.html\" title=\"trait core::marker::Copy\">Copy</a>,</div>"],["impl&lt;A: <a class=\"trait\" href=\"arrayvec/trait.Array.html\" title=\"trait arrayvec::Array\">Array</a>&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/borrow/trait.Borrow.html\" title=\"trait core::borrow::Borrow\">Borrow</a>&lt;[&lt;A as <a class=\"trait\" href=\"arrayvec/trait.Array.html\" title=\"trait arrayvec::Array\">Array</a>&gt;::<a class=\"associatedtype\" href=\"arrayvec/trait.Array.html#associatedtype.Item\" title=\"type arrayvec::Array::Item\">Item</a>]&gt; for <a class=\"struct\" href=\"arrayvec/struct.ArrayVec.html\" title=\"struct arrayvec::ArrayVec\">ArrayVec</a>&lt;A&gt;"]]],["bitvec",[["impl&lt;A, O&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/borrow/trait.Borrow.html\" title=\"trait core::borrow::Borrow\">Borrow</a>&lt;<a class=\"struct\" href=\"bitvec/slice/struct.BitSlice.html\" title=\"struct bitvec::slice::BitSlice\">BitSlice</a>&lt;&lt;A as <a class=\"trait\" href=\"bitvec/view/trait.BitView.html\" title=\"trait bitvec::view::BitView\">BitView</a>&gt;::<a class=\"associatedtype\" href=\"bitvec/view/trait.BitView.html#associatedtype.Store\" title=\"type bitvec::view::BitView::Store\">Store</a>, O&gt;&gt; for <a class=\"struct\" href=\"bitvec/array/struct.BitArray.html\" title=\"struct bitvec::array::BitArray\">BitArray</a>&lt;A, O&gt;<div class=\"where\">where\n    A: <a class=\"trait\" href=\"bitvec/view/trait.BitViewSized.html\" title=\"trait bitvec::view::BitViewSized\">BitViewSized</a>,\n    O: <a class=\"trait\" href=\"bitvec/order/trait.BitOrder.html\" title=\"trait bitvec::order::BitOrder\">BitOrder</a>,</div>"],["impl&lt;T, O&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/borrow/trait.Borrow.html\" title=\"trait core::borrow::Borrow\">Borrow</a>&lt;<a class=\"struct\" href=\"bitvec/slice/struct.BitSlice.html\" title=\"struct bitvec::slice::BitSlice\">BitSlice</a>&lt;T, O&gt;&gt; for <a class=\"struct\" href=\"bitvec/boxed/struct.BitBox.html\" title=\"struct bitvec::boxed::BitBox\">BitBox</a>&lt;T, O&gt;<div class=\"where\">where\n    T: <a class=\"trait\" href=\"bitvec/store/trait.BitStore.html\" title=\"trait bitvec::store::BitStore\">BitStore</a>,\n    O: <a class=\"trait\" href=\"bitvec/order/trait.BitOrder.html\" title=\"trait bitvec::order::BitOrder\">BitOrder</a>,</div>"],["impl&lt;T, O&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/borrow/trait.Borrow.html\" title=\"trait core::borrow::Borrow\">Borrow</a>&lt;<a class=\"struct\" href=\"bitvec/slice/struct.BitSlice.html\" title=\"struct bitvec::slice::BitSlice\">BitSlice</a>&lt;T, O&gt;&gt; for <a class=\"struct\" href=\"bitvec/vec/struct.BitVec.html\" title=\"struct bitvec::vec::BitVec\">BitVec</a>&lt;T, O&gt;<div class=\"where\">where\n    T: <a class=\"trait\" href=\"bitvec/store/trait.BitStore.html\" title=\"trait bitvec::store::BitStore\">BitStore</a>,\n    O: <a class=\"trait\" href=\"bitvec/order/trait.BitOrder.html\" title=\"trait bitvec::order::BitOrder\">BitOrder</a>,</div>"]]],["camino",[["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/borrow/trait.Borrow.html\" title=\"trait core::borrow::Borrow\">Borrow</a>&lt;<a class=\"struct\" href=\"camino/struct.Utf8Path.html\" title=\"struct camino::Utf8Path\">Utf8Path</a>&gt; for <a class=\"struct\" href=\"camino/struct.Utf8PathBuf.html\" title=\"struct camino::Utf8PathBuf\">Utf8PathBuf</a>"]]],["clap_builder",[["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/borrow/trait.Borrow.html\" title=\"trait core::borrow::Borrow\">Borrow</a>&lt;<a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.str.html\">str</a>&gt; for <a class=\"struct\" href=\"clap_builder/builder/struct.Str.html\" title=\"struct clap_builder::builder::Str\">Str</a>"],["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/borrow/trait.Borrow.html\" title=\"trait core::borrow::Borrow\">Borrow</a>&lt;<a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.str.html\">str</a>&gt; for <a class=\"struct\" href=\"clap_builder/struct.Id.html\" title=\"struct clap_builder::Id\">Id</a>"],["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/borrow/trait.Borrow.html\" title=\"trait core::borrow::Borrow\">Borrow</a>&lt;<a class=\"struct\" href=\"https://doc.rust-lang.org/nightly/std/ffi/os_str/struct.OsStr.html\" title=\"struct std::ffi::os_str::OsStr\">OsStr</a>&gt; for <a class=\"struct\" href=\"clap_builder/builder/struct.OsStr.html\" title=\"struct clap_builder::builder::OsStr\">OsStr</a>"]]],["deranged",[["impl&lt;const MIN: <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.i128.html\">i128</a>, const MAX: <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.i128.html\">i128</a>&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/borrow/trait.Borrow.html\" title=\"trait core::borrow::Borrow\">Borrow</a>&lt;<a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.i128.html\">i128</a>&gt; for <a class=\"struct\" href=\"deranged/struct.RangedI128.html\" title=\"struct deranged::RangedI128\">RangedI128</a>&lt;MIN, MAX&gt;"],["impl&lt;const MIN: <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.i16.html\">i16</a>, const MAX: <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.i16.html\">i16</a>&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/borrow/trait.Borrow.html\" title=\"trait core::borrow::Borrow\">Borrow</a>&lt;<a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.i16.html\">i16</a>&gt; for <a class=\"struct\" href=\"deranged/struct.RangedI16.html\" title=\"struct deranged::RangedI16\">RangedI16</a>&lt;MIN, MAX&gt;"],["impl&lt;const MIN: <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.i32.html\">i32</a>, const MAX: <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.i32.html\">i32</a>&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/borrow/trait.Borrow.html\" title=\"trait core::borrow::Borrow\">Borrow</a>&lt;<a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.i32.html\">i32</a>&gt; for <a class=\"struct\" href=\"deranged/struct.RangedI32.html\" title=\"struct deranged::RangedI32\">RangedI32</a>&lt;MIN, MAX&gt;"],["impl&lt;const MIN: <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.i64.html\">i64</a>, const MAX: <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.i64.html\">i64</a>&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/borrow/trait.Borrow.html\" title=\"trait core::borrow::Borrow\">Borrow</a>&lt;<a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.i64.html\">i64</a>&gt; for <a class=\"struct\" href=\"deranged/struct.RangedI64.html\" title=\"struct deranged::RangedI64\">RangedI64</a>&lt;MIN, MAX&gt;"],["impl&lt;const MIN: <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.i8.html\">i8</a>, const MAX: <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.i8.html\">i8</a>&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/borrow/trait.Borrow.html\" title=\"trait core::borrow::Borrow\">Borrow</a>&lt;<a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.i8.html\">i8</a>&gt; for <a class=\"struct\" href=\"deranged/struct.RangedI8.html\" title=\"struct deranged::RangedI8\">RangedI8</a>&lt;MIN, MAX&gt;"],["impl&lt;const MIN: <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.isize.html\">isize</a>, const MAX: <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.isize.html\">isize</a>&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/borrow/trait.Borrow.html\" title=\"trait core::borrow::Borrow\">Borrow</a>&lt;<a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.isize.html\">isize</a>&gt; for <a class=\"struct\" href=\"deranged/struct.RangedIsize.html\" title=\"struct deranged::RangedIsize\">RangedIsize</a>&lt;MIN, MAX&gt;"],["impl&lt;const MIN: <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.u128.html\">u128</a>, const MAX: <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.u128.html\">u128</a>&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/borrow/trait.Borrow.html\" title=\"trait core::borrow::Borrow\">Borrow</a>&lt;<a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.u128.html\">u128</a>&gt; for <a class=\"struct\" href=\"deranged/struct.RangedU128.html\" title=\"struct deranged::RangedU128\">RangedU128</a>&lt;MIN, MAX&gt;"],["impl&lt;const MIN: <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.u16.html\">u16</a>, const MAX: <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.u16.html\">u16</a>&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/borrow/trait.Borrow.html\" title=\"trait core::borrow::Borrow\">Borrow</a>&lt;<a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.u16.html\">u16</a>&gt; for <a class=\"struct\" href=\"deranged/struct.RangedU16.html\" title=\"struct deranged::RangedU16\">RangedU16</a>&lt;MIN, MAX&gt;"],["impl&lt;const MIN: <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.u32.html\">u32</a>, const MAX: <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.u32.html\">u32</a>&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/borrow/trait.Borrow.html\" title=\"trait core::borrow::Borrow\">Borrow</a>&lt;<a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.u32.html\">u32</a>&gt; for <a class=\"struct\" href=\"deranged/struct.RangedU32.html\" title=\"struct deranged::RangedU32\">RangedU32</a>&lt;MIN, MAX&gt;"],["impl&lt;const MIN: <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.u64.html\">u64</a>, const MAX: <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.u64.html\">u64</a>&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/borrow/trait.Borrow.html\" title=\"trait core::borrow::Borrow\">Borrow</a>&lt;<a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.u64.html\">u64</a>&gt; for <a class=\"struct\" href=\"deranged/struct.RangedU64.html\" title=\"struct deranged::RangedU64\">RangedU64</a>&lt;MIN, MAX&gt;"],["impl&lt;const MIN: <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.u8.html\">u8</a>, const MAX: <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.u8.html\">u8</a>&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/borrow/trait.Borrow.html\" title=\"trait core::borrow::Borrow\">Borrow</a>&lt;<a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.u8.html\">u8</a>&gt; for <a class=\"struct\" href=\"deranged/struct.RangedU8.html\" title=\"struct deranged::RangedU8\">RangedU8</a>&lt;MIN, MAX&gt;"],["impl&lt;const MIN: <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.usize.html\">usize</a>, const MAX: <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.usize.html\">usize</a>&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/borrow/trait.Borrow.html\" title=\"trait core::borrow::Borrow\">Borrow</a>&lt;<a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.usize.html\">usize</a>&gt; for <a class=\"struct\" href=\"deranged/struct.RangedUsize.html\" title=\"struct deranged::RangedUsize\">RangedUsize</a>&lt;MIN, MAX&gt;"]]],["index_vec",[["impl&lt;I: <a class=\"trait\" href=\"index_vec/trait.Idx.html\" title=\"trait index_vec::Idx\">Idx</a>, T&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/borrow/trait.Borrow.html\" title=\"trait core::borrow::Borrow\">Borrow</a>&lt;<a class=\"struct\" href=\"index_vec/struct.IndexSlice.html\" title=\"struct index_vec::IndexSlice\">IndexSlice</a>&lt;I, <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/core/primitive.slice.html\">[T]</a>&gt;&gt; for <a class=\"struct\" href=\"index_vec/struct.IndexVec.html\" title=\"struct index_vec::IndexVec\">IndexVec</a>&lt;I, T&gt;"]]],["powerfmt",[["impl&lt;const SIZE: <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/core/primitive.usize.html\">usize</a>&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/borrow/trait.Borrow.html\" title=\"trait core::borrow::Borrow\">Borrow</a>&lt;<a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/core/primitive.str.html\">str</a>&gt; for <a class=\"struct\" href=\"powerfmt/buf/struct.WriteBuffer.html\" title=\"struct powerfmt::buf::WriteBuffer\">WriteBuffer</a>&lt;SIZE&gt;"]]],["serde_spanned",[["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/borrow/trait.Borrow.html\" title=\"trait core::borrow::Borrow\">Borrow</a>&lt;<a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.str.html\">str</a>&gt; for <a class=\"struct\" href=\"serde_spanned/struct.Spanned.html\" title=\"struct serde_spanned::Spanned\">Spanned</a>&lt;<a class=\"struct\" href=\"https://doc.rust-lang.org/nightly/alloc/string/struct.String.html\" title=\"struct alloc::string::String\">String</a>&gt;"]]],["smallvec",[["impl&lt;A: <a class=\"trait\" href=\"smallvec/trait.Array.html\" title=\"trait smallvec::Array\">Array</a>&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/borrow/trait.Borrow.html\" title=\"trait core::borrow::Borrow\">Borrow</a>&lt;[&lt;A as <a class=\"trait\" href=\"smallvec/trait.Array.html\" title=\"trait smallvec::Array\">Array</a>&gt;::<a class=\"associatedtype\" href=\"smallvec/trait.Array.html#associatedtype.Item\" title=\"type smallvec::Array::Item\">Item</a>]&gt; for <a class=\"struct\" href=\"smallvec/struct.SmallVec.html\" title=\"struct smallvec::SmallVec\">SmallVec</a>&lt;A&gt;"]]],["toml_edit",[["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/borrow/trait.Borrow.html\" title=\"trait core::borrow::Borrow\">Borrow</a>&lt;<a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.str.html\">str</a>&gt; for <a class=\"struct\" href=\"toml_edit/struct.InternalString.html\" title=\"struct toml_edit::InternalString\">InternalString</a>"],["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/borrow/trait.Borrow.html\" title=\"trait core::borrow::Borrow\">Borrow</a>&lt;<a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.str.html\">str</a>&gt; for <a class=\"struct\" href=\"toml_edit/struct.Key.html\" title=\"struct toml_edit::Key\">Key</a>"]]],["winnow",[["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/borrow/trait.Borrow.html\" title=\"trait core::borrow::Borrow\">Borrow</a>&lt;<a class=\"struct\" href=\"winnow/stream/struct.BStr.html\" title=\"struct winnow::stream::BStr\">BStr</a>&gt; for <a class=\"struct\" href=\"https://doc.rust-lang.org/nightly/alloc/vec/struct.Vec.html\" title=\"struct alloc::vec::Vec\">Vec</a>&lt;<a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.u8.html\">u8</a>&gt;"],["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/borrow/trait.Borrow.html\" title=\"trait core::borrow::Borrow\">Borrow</a>&lt;<a class=\"struct\" href=\"winnow/stream/struct.Bytes.html\" title=\"struct winnow::stream::Bytes\">Bytes</a>&gt; for <a class=\"struct\" href=\"https://doc.rust-lang.org/nightly/alloc/vec/struct.Vec.html\" title=\"struct alloc::vec::Vec\">Vec</a>&lt;<a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.u8.html\">u8</a>&gt;"]]]]);
    if (window.register_implementors) {
        window.register_implementors(implementors);
    } else {
        window.pending_implementors = implementors;
    }
})()
//{"start":57,"fragment_lengths":[597,1413,2395,390,1180,7347,629,532,544,639,753,1014]}