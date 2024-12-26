searchState.loadedDescShard("flowistry", 0, "This crate provides the Flowistry API, a modular …\nExtra features for evaluating / ablating the precision of …\nThe core information flow analysis.\nInfrastructure for analyzing MIR that supports the …\nImprecise behavior, assume all pointers alias\nWhether Flowistry should attempt to recurse into …\nPrecise behavior, distinguish them\nA combination of all the precision levers.\nImprecise behavior, do not distinguish them (assume …\nWhether Flowistry should ignore the distinction between …\nWhether Flowistry should use lifetimes to distinguish …\nPrecise behavior, use lifetimes\nPrecise behavior, recurse into call sites when possible\nImprecise behavior, only use the modular approximation\nEquivalent to <code>f(&amp;iter.collect::&lt;Vec&lt;_&gt;&gt;())</code>.\nEquivalent to <code>f(&amp;iter.collect::&lt;Vec&lt;_&gt;&gt;())</code>.\nEquivalent to <code>f(&amp;iter.collect::&lt;Vec&lt;_&gt;&gt;())</code>.\nEquivalent to <code>f(&amp;iter.collect::&lt;Vec&lt;_&gt;&gt;())</code>.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nThings that affect the source\nBoth forward and backward\nWhich way to look for dependencies\nData structure that holds context for performing the …\nRepresents the information flows at a given instruction. …\nThe output of the information flow analysis.\nThings affects by the source\nThe underlying analysis that was used to generate the …\nThe body being analyzed.\nEquivalent to <code>f(&amp;iter.collect::&lt;Vec&lt;_&gt;&gt;())</code>.\nEquivalent to <code>f(&amp;iter.collect::&lt;Vec&lt;_&gt;&gt;())</code>.\nComputes the dependencies of a place $p$ at a location …\nWraps <code>compute_dependencies</code> by translating each <code>Location</code> to …\nComputes information flow for a MIR body.\nThe ID of the body being analyzed.\nReturns all the dependencies of <code>place</code> within <code>state</code>.\nReturns the argument unchanged.\nReturns the argument unchanged.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nReturns the <code>LocationOrArgDomain</code> used by the analysis.\nIdentifies the mutated places in a MIR instruction via …\nConstructs (but does not execute) a new FlowAnalysis.\nThe metadata about places used in the analysis.\nThe type context used for the analysis.\nIt was a function argument\nIt was target of an assign (via return or regular assign)\nA place is definitely mutated, e.g. <code>x = y</code> definitely …\nMIR visitor that invokes a callback for every <code>Mutation</code> in …\nInformation about a particular mutation.\nIndicator of certainty about whether a place is being …\nA place is possibly mutated, e.g. <code>f(&amp;mut x)</code> possibly …\nWhy did this mutation occur\nEquivalent to <code>f(&amp;iter.collect::&lt;Vec&lt;_&gt;&gt;())</code>.\nEquivalent to <code>f(&amp;iter.collect::&lt;Vec&lt;_&gt;&gt;())</code>.\nEquivalent to <code>f(&amp;iter.collect::&lt;Vec&lt;_&gt;&gt;())</code>.\nEquivalent to <code>f(&amp;iter.collect::&lt;Vec&lt;_&gt;&gt;())</code>.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nThe set of inputs to the mutating operation.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nThe place that is being mutated.\nConstructs a new visitor.\nSimplified reason why this mutation occurred.\nThe certainty of whether the mutation is happening.\nThe per-procedure information the analysis needs. Most of …\nAlias analysis to determine the points-to set of a …\nThis module re-implements <code>rustc_mir_dataflow::Engine</code> for …\nUtilities for analyzing places: children, aliases, etc.\nA potpourri of utilities for working with the MIR, …\nData structure for computing and storing aliases.\nGiven a <code>place</code>, returns the set of direct places it could …\nRuns the alias analysis on a given <code>body_with_facts</code>.\nEquivalent to <code>f(&amp;iter.collect::&lt;Vec&lt;_&gt;&gt;())</code>.\nReturns the argument unchanged.\nCalls <code>U::from(self)</code>.\nAn alternative implementation of …\nThe underlying analysis that was used to generate the …\nEquivalent to <code>f(&amp;iter.collect::&lt;Vec&lt;_&gt;&gt;())</code>.\nReturns the argument unchanged.\nCalls <code>U::from(self)</code>.\nRuns a given <code>Analysis</code> to a fixpoint over the given <code>Body</code>.\nGets the computed <code>AnalysisDomain</code> at a given <code>Location</code>.\nUtilities for analyzing places: children, aliases, etc.\nComputes the aliases of a place (cached).\nReturns all direct places reachable from arguments to the …\nComputes all the metadata about places used within the …\nComputes all the metadata about places used within the …\nReturns all reachable fields of <code>place</code> without going …\nEquivalent to <code>f(&amp;iter.collect::&lt;Vec&lt;_&gt;&gt;())</code>.\nReturns all places that <em>directly</em> conflict with <code>place</code>, i.e. …\nReturns the argument unchanged.\nCalls <code>U::from(self)</code>.\nReturns the <code>LocationOrArgDomain</code> for the current body.\nNormalizes a place via <code>PlaceExt::normalize</code> (cached).\nReturns all direct places that are reachable from <code>place</code> …\nA hack to temporary hack to reduce spurious dependencies …\nAn unordered collections of MIR <code>Place</code>s.\nGiven the arguments to a function, returns all projections …\nGiven the arguments to a function, returns all places in …\nEquivalent to <code>f(&amp;iter.collect::&lt;Vec&lt;_&gt;&gt;())</code>.\nReturns the argument unchanged.\nCalls <code>U::from(self)</code>.")