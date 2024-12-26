searchState.loadedDescShard("wyz", 0, "<code>wyz</code> – myrrlyn’s wyzyrdly library\nA bidirectional iterator that only checks its direction …\nTrait-level <code>co</code>nst/<code>mu</code>table tracking.\nFormat forwarding\nRange utilities.\nAn iterator that conditionally reverses itself upon …\nExtension trait that provides <code>.bidi()</code> for all double-ended …\nConditionally reverses the direction of iteration.\nReturns the argument unchanged.\nCalls <code>U::from(self)</code>.\nApplies the <code>Bidi</code> adapter to a double-ended iterator and …\nA generic non-null pointer with type-system mutability …\nMarks whether this type contains mutability permissions …\nA basic <code>const</code> marker.\nThe dangling pointer.\nThe type of the element pointer.\nA frozen wrapper over some other <code>Mutability</code> marker.\nA basic <code>mut</code> marker.\nGeneralized mutability permissions.\n<code>Address</code> cannot be constructed over null pointers.\nCounts the layers of <code>Frozen&lt;&gt;</code> wrapping around a base <code>Const</code> …\nOne of <code>*const</code> or <code>*mut</code>.\nThe created reference type. Must be one of <code>&amp;T</code> or <code>&amp;mut T</code>.\nA generically-mutable reference.\nAllows an <code>Address</code> to produce an ordinary reference.\nAllow instances to be constructed generically.\nAllows an <code>Address&lt;M, [T]&gt;</code> to produce an ordinary slice …\nApplies <code>&lt;*T&gt;::add</code>.\nApplies <code>&lt;*T&gt;::align_offset</code>.\nApplies <code>&lt;*T&gt;::as_mut</code>.\nApplies <code>&lt;*T&gt;::as_ref</code>.\nForce an <code>Address&lt;Const&gt;</code> to be <code>Address&lt;Mut&gt;</code>.\nApplies <code>&lt;*T&gt;::cast</code>.\nApplies <code>&lt;*T&gt;::copy_from</code>.\nApplies <code>&lt;*T&gt;::copy_from_nonoverlapping</code>.\nApplies <code>&lt;*T&gt;::copy_to</code>.\nApplies <code>&lt;*T&gt;::copy_to_nonoverlapping</code>.\nApplies <code>&lt;*T&gt;::drop_in_place</code>.\nFreeze this type, wrapping it in a <code>const</code> marker that may …\nFreezes the <code>Address</code> so that it is read-only.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nConstructs an ordinary slice reference from a base-address …\nConverts a reference back into an <code>Address</code>.\nPermanently converts an <code>Address&lt;_&gt;</code> into an <code>Address&lt;Const&gt;</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nRemoves the <code>Address</code> type marker, returning the original …\nConstructs a new <code>Address</code> over some pointer value.\nApplies <code>&lt;*T&gt;::offset</code>.\nApplies <code>&lt;*T&gt;::offset_from</code>.\nApplies <code>&lt;*T&gt;::read</code>.\nApplies <code>&lt;*T&gt;::read_unaligned</code>.\nApplies <code>&lt;*T&gt;::read_volatile</code>.\nApplies <code>&lt;*T&gt;::replace</code>.\nApplies <code>&lt;*T&gt;::sub</code>.\nApplies <code>&lt;*T&gt;::swap</code>.\nThaw a previously-frozen type, removing its <code>Frozen</code> marker …\nThaws the <code>Address</code> to its original mutability permission.\nGets the address as a read-only pointer.\nGets the address as a write-capable pointer.\nConverts the <code>Address</code> to a reference.\nApplies <code>&lt;*T&gt;::wrapping_add</code>.\nApplies <code>&lt;*T&gt;::wrapping_offset</code>.\nApplies <code>&lt;*T&gt;::wrapping_sub</code>.\nApplies <code>&lt;*T&gt;::write</code>.\nApplies <code>&lt;*T&gt;::write_unaligned</code>.\nApplies <code>&lt;*T&gt;::write_volatile</code>.\nForwards a type’s <code>Binary</code> formatting implementation to …\nForwards a type’s <code>Display</code> formatting implementation to …\nWraps any value with a format-forward to <code>Debug</code>.\nRenders each element of a stream into a list.\nForwards a type’s <code>LowerExp</code> formatting implementation to …\nForwards a type’s <code>LowerHex</code> formatting implementation to …\nForwards a type’s <code>Octal</code> formatting implementation to …\nForwards a type’s <code>Pointer</code> formatting implementation to …\nForwards a type’s <code>UpperExp</code> formatting implementation to …\nForwards a type’s <code>UpperHex</code> formatting implementation to …\nCauses <code>self</code> to use its <code>Binary</code> implementation when <code>Debug</code>…\nCauses <code>self</code> to use its <code>Display</code> implementation when <code>Debug</code>…\nFormats each item in a sequence.\nCauses <code>self</code> to use its <code>LowerExp</code> implementation when <code>Debug</code>…\nCauses <code>self</code> to use its <code>LowerHex</code> implementation when <code>Debug</code>…\nCauses <code>self</code> to use its <code>Octal</code> implementation when <code>Debug</code>…\nCauses <code>self</code> to use its <code>Pointer</code> implementation when <code>Debug</code>…\nCauses <code>self</code> to use its <code>UpperExp</code> implementation when <code>Debug</code>…\nCauses <code>self</code> to use its <code>UpperHex</code> implementation when <code>Debug</code>…\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nExtension methods for working with various range types.\nFinds the intersection between two range-likes. The …\nNormalizes a range-like type to a canonical half-open <code>Range</code>…\nFinds the union between two range-likes. The produced <code>Range</code>…")