searchState.loadedDescShard("rustc_error_messages", 0, "Failed to add <code>FluentResource</code> to <code>FluentBundle</code>.\nBorrowed data.\nAbstraction over a message in a diagnostic to support both …\nFluent messages can use arguments in order to …\nAttribute of a Fluent message. Needs to be combined with a …\nCore error type for Fluent runtime system.\nIdentifier for the Fluent message/attribute corresponding …\nIdentifier of a Fluent message. Instances of this variant …\nIdentifier for a Fluent message (with optional attribute) …\nCustom types can implement the <code>FluentType</code> trait in order …\nThe <code>FluentValue</code> enum represents values which can be …\n<code>LanguageIdentifier</code> is a core struct representing a Unicode …\nType alias for the result of <code>fallback_fluent_bundle</code> - a …\n<code>$sysroot/share/locale/$locale</code> is not a directory.\n<code>$sysroot/share/locale/$locale</code> does not exist.\nA collection of <code>Span</code>s.\nAn error which occurs when <code>FluentBundle::add_resource</code> adds …\nOwned data.\nFailed to parse contents of <code>.ftl</code> file.\nFailed to read from <code>.ftl</code> file.\nCannot read directory entries of …\nCannot read directory entry of …\nA span together with some additional data.\nNon-translatable diagnostic message.\nNon-translatable diagnostic message.\nAbstraction over a message in a subdiagnostic (i.e. label, …\nTranslatable message which has already been translated …\nTranslatable message which has been already translated.\nConvert the custom type into a string value, for instance …\nConverts the <code>FluentValue</code> to a string.\nConvert the custom type into a string value, for instance …\nReturns character direction of the <code>LanguageIdentifier</code>.\nClears variant subtags of the <code>LanguageIdentifier</code>.\nClone this <code>MultiSpan</code> without keeping any of the span …\nCreate a clone of the underlying type.\nReturn the default <code>FluentBundle</code> with standard “en-US” …\nReturns Fluent bundle with the user’s locale resources …\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nA constructor which takes a utf8 slice, parses it and …\nA constructor which takes optional subtags as <code>AsRef&lt;[u8]&gt;</code>, …\nUnchecked\nGets the <code>FluentValue</code> at the <code>key</code> if it exists.\nReturns <code>true</code> if any of the primary spans are displayable.\nReturns <code>true</code> if any of the span labels is displayable.\nTests if a variant subtag is present in the …\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nConsumes <code>LanguageIdentifier</code> and produces raw internal …\nConverts the <code>FluentValue</code> to a string.\nReturns <code>true</code> if this contains only a dummy primary span …\nIs this a primary span? This is the “locus” of the …\nIterate over a tuple of the key an <code>FluentValue</code>.\nWhat label should we attach to this span (if any)?\nCompares a <code>LanguageIdentifier</code> to another …\nChecks to see if two <code>FluentValues</code> match each other by …\nCreates a new empty argument map.\nSelects the first primary span (if any).\nReturns all primary spans.\nReplaces all occurrences of one Span with another. Used to …\nSets the key value pair.\nSets variant subtags of the <code>LanguageIdentifier</code>.\nThe span we are going to include in the final snippet.\nReturns the strings to highlight. We always ensure that …\nAttempts to parse the string representation of a <code>value</code> …\nReturns a vector of variants subtags of the …\nPre-allocates capacity for arguments.\nGiven a <code>SubdiagMessage</code> which may contain a Fluent …\nWrite out a string version of the <code>FluentValue</code> to <code>W</code>.")