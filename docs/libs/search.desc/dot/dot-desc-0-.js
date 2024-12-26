searchState.loadedDescShard("dot", 0, "Generate files suitable for use with Graphviz\nThis structure holds all information that can describe an …\nThis enumeration represents all possible arrow edge as …\nBorrowed data.\nBorrowed data.\nArrow ending in a small square box\nAllowed values for compass points. Used for specifying …\nArrow ending in a three branching lines also called crow’…\nArrow ending in a curve\nArrow ending in an diamond shaped rectangular shape.\nArrow ending in a circle.\nThis kind of label uses the graphviz label escString type: …\nArrow modifier that determines if the shape is empty or …\nGraphWalk is an abstraction over a graph = (nodes,edges) …\nThis uses a graphviz HTML string label. The string is …\nArrow ending in an inverted curve\n<code>Id</code> is a Graphviz <code>ID</code>.\nArrow ending in an inverted triangle.\nGraph kind determines if <code>digraph</code> or <code>graph</code> is used as …\nThis kind of label preserves the text directly as is.\nThe text for a graphviz label on a node or edge.\nEach instance of a type that implements <code>Label&lt;C&gt;</code> maps to a …\nNo arrow will be displayed\nArrow that ends in a triangle. Basically a normal arrow. …\nOwned data.\nOwned data.\nThe direction to draw directed graphs (one rank at a time) …\nArrow modifier that determines if the shape is clipped. …\nThe style for a node or edge. See …\nArrow ending with a T shaped arrow.\nArrow ending with a V shaped arrow.\nConstructor which returns a regular box arrow.\nConstructor which returns a regular crow arrow.\nConstructor which returns a regular curve arrow.\nArrow constructor which returns a default arrow\nReturns vec holding all the default render options.\nConstructor which returns a diamond arrow.\nConstructor which returns a circle shaped arrow.\nMaps <code>e</code> to one of the graphviz <code>color</code> names. If <code>None</code> is …\nMaps <code>e</code> to arrow style that will be used on the end of an …\nMaps <code>e</code> to a label that will be used in the rendered output.\nMaps <code>e</code> to arrow style that will be used on the end of an …\nMaps <code>e</code> to a style that will be used in the rendered output.\nReturns all of the edges in this graph.\nEscape tags in such a way that it is suitable for …\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nArrow constructor which returns an arrow created by a …\nMust return a DOT compatible identifier naming the graph.\nConstructor which returns an inverted curve arrow.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nConstructor which returns an inverted triangle arrow.\nThe kind of graph, defaults to <code>Kind::Digraph</code>.\nCreates an <code>Id</code> named <code>name</code>.\nMaps <code>n</code> to one of the graphviz <code>color</code> names. If <code>None</code> is …\nMaps <code>n</code> to a unique identifier with respect to <code>self</code>. The …\nMaps <code>n</code> to a label that will be used in the rendered output.\nMaps <code>n</code> to one of the graphviz <code>shape</code> names. If <code>None</code> is …\nMaps <code>n</code> to a style that will be used in the rendered output.\nReturns all the nodes in this graph.\nArrow constructor which returns an empty arrow\nConstructor which returns no arrow.\nArrow constructor which returns a regular triangle arrow, …\nConstructor which returns normal arrow.\nPuts <code>prefix</code> on a line above this label, with a blank line …\nReturn an explicit rank dir to use for directed graphs.\nRenders graph <code>g</code> into the writer <code>w</code> in DOT syntax. (Simple …\nRenders graph <code>g</code> into the writer <code>w</code> in DOT syntax. (Main …\nThe source node for <code>edge</code>.\nSpecify a subpart of the source node for the origin of the …\nPuts <code>suffix</code> on a line below this label, with a blank line …\nThe target node for <code>edge</code>.\nSame as <code>source_port_position</code> but for the target end of the …\nConstructor which returns a T shaped arrow.\nRenders text as string suitable for a label in a .dot file.\nFunction which converts given arrow into a renderable form.\nFunction which renders given ArrowShape into a String for …\nConstructor which returns a V shaped arrow.")