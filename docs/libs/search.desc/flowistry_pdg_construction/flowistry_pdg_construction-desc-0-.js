searchState.loadedDescShard("flowistry_pdg_construction", 0, "Compute program dependence graphs (PDG) for a function …\nA memoizing constructor of PDGs.\nCallbacks to influence graph construction and their …\nComputes a global program dependence graph (PDG) starting …\nTry to interpret this function as an async function.\nReaders and writers for the intermediate artifacts we …\nThe representation of the PDG.\nDoes this function have a structure as created by the …\nIdentifies the mutated places in a MIR instruction via …\nContext for a call to <code>Future::poll</code>, when called on a …\nStores ids that are needed to construct projections around …\nDescribe in which way a function is <code>async</code>.\nIf the generator came from an <code>async fn</code>, then this is that …\nEquivalent to <code>f(&amp;iter.collect::&lt;Vec&lt;_&gt;&gt;())</code>.\nEquivalent to <code>f(&amp;iter.collect::&lt;Vec&lt;_&gt;&gt;())</code>.\nEquivalent to <code>f(&amp;iter.collect::&lt;Vec&lt;_&gt;&gt;())</code>.\nEquivalent to <code>f(&amp;iter.collect::&lt;Vec&lt;_&gt;&gt;())</code>.\nWhere was the <code>async fn</code> called, or where was the async …\nTry to interpret this function as an async function.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nA place which carries the runtime value representing the …\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nDoes this instance refer to an <code>async fn</code> or <code>async {}</code>.\nDoes this function have a structure as created by the …\nAllows loading bodies from previosly written artifacts.\nA mir <code>Body</code> and all the additional borrow checking facts …\nA visitor to collect all bodies in the crate and write …\nThe subset of borrowcheck facts that the points-to …\nSome data in a Body is not cross-crate compatible. Usually …\nEquivalent to <code>f(&amp;iter.collect::&lt;Vec&lt;_&gt;&gt;())</code>.\nEquivalent to <code>f(&amp;iter.collect::&lt;Vec&lt;_&gt;&gt;())</code>.\nEquivalent to <code>f(&amp;iter.collect::&lt;Vec&lt;_&gt;&gt;())</code>.\nEquivalent to <code>f(&amp;iter.collect::&lt;Vec&lt;_&gt;&gt;())</code>.\nA complete visit over the local crate items, collecting …\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nServe the body from the cache or read it from the disk.\nCreate the name of the file in which to store intermediate …\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nTry to load a <code>CachedBody</code> for this id.\nGet the path where artifacts from this crate would be …\nRetrieve a body and the necessary facts for a local item.\nUser-provided changes to the default PDG construction …\nInformation about the function being called.\nRecurse into the function as normal.\nReplace with a call to this other function and arguments.\nSkip the function, and perform a modular approxmation of …\nWhether or not to skip recursing into a function call …\nIf the callee is an async closure created by an <code>async fn</code>, …\nThe call-stack up to the current call site.\nThe potentially-monomorphized resolution of the callee.\nEquivalent to <code>f(&amp;iter.collect::&lt;Vec&lt;_&gt;&gt;())</code>.\nEquivalent to <code>f(&amp;iter.collect::&lt;Vec&lt;_&gt;&gt;())</code>.\nEquivalent to <code>f(&amp;iter.collect::&lt;Vec&lt;_&gt;&gt;())</code>.\nEquivalent to <code>f(&amp;iter.collect::&lt;Vec&lt;_&gt;&gt;())</code>.\nEquivalent to <code>f(&amp;iter.collect::&lt;Vec&lt;_&gt;&gt;())</code>.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nWould the PDG for this function be served from the cache.\nIndicate whether or not to skip recursing into the given …\nAn async generator, only has one argument which is the …\nDescribes how the formal parameters of a given function …\n1 to 1 mapping\nFirst argument is the closed-over environment, second …\nThe result of calculating a translation from a child place …\nThis struct represents all the information necessary to …\nReturn the base version of the parent place with no child …\nEquivalent to <code>f(&amp;iter.collect::&lt;Vec&lt;_&gt;&gt;())</code>.\nEquivalent to <code>f(&amp;iter.collect::&lt;Vec&lt;_&gt;&gt;())</code>.\nEquivalent to <code>f(&amp;iter.collect::&lt;Vec&lt;_&gt;&gt;())</code>.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns a calculated translation that needs to be finished.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nComplete the translation and return a precise parent place.\n<code>destination</code> must be the place to which the return is …\nGoverns whether the translation produces precise results …\nReturns a fully translated parent place. If …\nA memoizing constructor of PDGs.\nStores PDG’s we have already computed and which we know …\nHow we are indexing into <code>PdgCache</code>\nAccess to the underlying body cache.\nTry to retrieve or load a body for this id.\nEquivalent to <code>f(&amp;iter.collect::&lt;Vec&lt;_&gt;&gt;())</code>.\nEquivalent to <code>f(&amp;iter.collect::&lt;Vec&lt;_&gt;&gt;())</code>.\nConstruct a  graph for this instance of return it from the …\nConstruct a final PDG for this function. Same as …\nConstruct the intermediate PDG for this function. …\nReturns the argument unchanged.\nReturns the argument unchanged.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nHas a PDG been constructed for this instance before?\nInitialize the constructor.\nInitialize the constructor.\nUsed for testing.\nRegister a callback to determine how to deal with function …\nDump the MIR of any function that is visited.\nWhatever can’t survive the crossing we need to live …\nSomething that implements <code>TyDecoder</code>.\nA structure that implements <code>TyEncoder</code> for us.\nEquivalent to <code>f(&amp;iter.collect::&lt;Vec&lt;_&gt;&gt;())</code>.\nEquivalent to <code>f(&amp;iter.collect::&lt;Vec&lt;_&gt;&gt;())</code>.\nConvenience function that decodes a value from a file.\nConvenience function that encodes some value to a file.\nReturns the argument unchanged.\nReturns the argument unchanged.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCreate a new encoder that will write to the provided file.\nDecode what is in this buffer.\nWhich path in a <code>RealFileName</code> do we care about?\nThis mutation is a non-function assign\nX is control-dependent on Y if the value of Y influences …\nX is data-dependent on Y if the value of Y is an input to …\nAn edge in the program dependence graph.\nA kind of edge in the program dependence graph.\nThe top-level PDG.\nA node in the program dependency graph.\nA mutable argument was modified by a function call\nA function returned, assigning to it’s return destination\nAdditional information about the source of data.\nAdditional information about this mutation.\nThe point in the execution of the program.\nThe location of the operation.\nEquivalent to <code>f(&amp;iter.collect::&lt;Vec&lt;_&gt;&gt;())</code>.\nEquivalent to <code>f(&amp;iter.collect::&lt;Vec&lt;_&gt;&gt;())</code>.\nEquivalent to <code>f(&amp;iter.collect::&lt;Vec&lt;_&gt;&gt;())</code>.\nEquivalent to <code>f(&amp;iter.collect::&lt;Vec&lt;_&gt;&gt;())</code>.\nEquivalent to <code>f(&amp;iter.collect::&lt;Vec&lt;_&gt;&gt;())</code>.\nEquivalent to <code>f(&amp;iter.collect::&lt;Vec&lt;_&gt;&gt;())</code>.\nEquivalent to <code>f(&amp;iter.collect::&lt;Vec&lt;_&gt;&gt;())</code>.\nConstructs a control edge.\nConstructs a data edge.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nGenerates a graphviz visualization of the PDG and saves it …\nThe petgraph representation of the PDG.\nreturns whether we were able to successfully handle this …\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nReturns true if the enum is SourceUse::Argument otherwise …\nReturns true if the enum is TargetUse::Assign otherwise …\nReturns true if the enum is TargetUse::MutArg otherwise …\nReturns true if the enum is SourceUse::Operand otherwise …\nReturns true if the enum is TargetUse::Return otherwise …\nDoes the PDG track subplaces of this place?\nEither data or control.\nConstructs a new <code>DepNode</code>.\nConstructs a new <code>DepGraph</code>.\nReturns the set of destination places that the parent can …\nReturns the set of source places that the parent can …\nA place in memory in a particular body.\nReturns a pretty string representation of the place, if …\nPretty representation of the place. This is cached as an …\nWe handle terminators during graph construction generally …\nA poll to an async function, like <code>f.await</code>.\nA standard function call like <code>f(x)</code>.\nA call to a function variable, like …\nReturns the aliases of <code>place</code>. See <code>PlaceInfo::aliases</code> for …\nUpdates the last-mutated location for <code>dst</code> to the given …\nSpecial case behavior for calls to functions used in …\nDetermine the type of call-site.\nEquivalent to <code>f(&amp;iter.collect::&lt;Vec&lt;_&gt;&gt;())</code>.\nEquivalent to <code>f(&amp;iter.collect::&lt;Vec&lt;_&gt;&gt;())</code>.\nEquivalent to <code>f(&amp;iter.collect::&lt;Vec&lt;_&gt;&gt;())</code>.\nEquivalent to <code>f(&amp;iter.collect::&lt;Vec&lt;_&gt;&gt;())</code>.\nGiven the arguments to a <code>Future::poll</code> call, walk back …\nReturns all pairs of <code>(src, edge)`` such that the given </code>…\nReturns all nodes <code>src</code> such that <code>src</code> is:\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nAttempt to inline a call to a function.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCreates [<code>GraphConstructor</code>] for a function resolved as …\nResolve a function <code>Operand</code> to a specific <code>DefId</code> and generic …\nChecks whether the function call, described by the …\nThe call takes place via a shim that implements <code>FnOnce</code> for …\nA place is definitely mutated, e.g. <code>x = y</code> definitely …\nMIR visitor that invokes a callback for every <code>Mutation</code> in …\nInformation about a particular mutation.\nIndicator of certainty about whether a place is being …\nA place is possibly mutated, e.g. <code>f(&amp;mut x)</code> possibly …\nA classification on when this visitor is executed. This is …\nEquivalent to <code>f(&amp;iter.collect::&lt;Vec&lt;_&gt;&gt;())</code>.\nEquivalent to <code>f(&amp;iter.collect::&lt;Vec&lt;_&gt;&gt;())</code>.\nEquivalent to <code>f(&amp;iter.collect::&lt;Vec&lt;_&gt;&gt;())</code>.\nEquivalent to <code>f(&amp;iter.collect::&lt;Vec&lt;_&gt;&gt;())</code>.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nThe set of inputs to the mutating operation.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nThe place that is being mutated.\nSimplified reason why this mutation occurred.\nConstructs a new visitor.\nSet when this visitor is executing. See Time for more …\nThe certainty of whether the mutation is happening.\nEquivalent to <code>f(&amp;iter.collect::&lt;Vec&lt;_&gt;&gt;())</code>.\nReturns the argument unchanged.\nCalls <code>U::from(self)</code>.\nAn async check that does not crash if called on closures.\nReturns whether this method is expected to have a body we …\nThe “canonical” way we monomorphize\nResolve the <code>def_id</code> item to an instance.\nAttempt to interpret this type as a statically …")