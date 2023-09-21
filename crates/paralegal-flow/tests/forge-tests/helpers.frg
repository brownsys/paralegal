#lang forge

open "analysis_result.frg"

pred flows_to[cs: Ctrl, o: Object, f : CallArgument] {
    some c: cs |
    some a : Src | {
        o = a or o in Type and a->o in c.types
        a -> f in ^(c.flow + arg_call_site)
    }
}

pred flows_to_ctrl[cs: Ctrl, o: Object, f : CallArgument] {
    some c: cs |
    some a : Src | {
        o = a or o in Type and a->o in c.types
        a -> f in ^(c.flow + c.ctrl_flow + arg_call_site)
    }
}

fun labeled_objects[obs: Object, ls: Label] : set Object {
    labels.ls & obs
}

// Returns all objects labelled either directly or indirectly
// through types.
fun labeled_objects_with_types[cs: Ctrl, obs: Object, ls: Label] : set Object {
    labeled_objects[obs, ls] + (cs.types).(labeled_objects[obs, ls])
}


fun arguments[f : CallSite] : set CallArgument {
    arg_call_site.f
}

fun safe_sources[cs: Ctrl] : set Object {
	labeled_objects_with_types[cs, Object, safe_source] // Either directly labeled with safe_source 
	+ {
		// Or it is safe_source_with_bless and has been flowed to by bless_safe_source
		elem : labeled_objects_with_types[cs, Object, safe_source_with_bless] | {
			some bless : labeled_objects_with_types[cs, Object, bless_safe_source] | {
				flows_to_ctrl[cs, bless, elem]
			}
		}
	}
}

// verifies that for an type o, it flows into first before flowing into next
pred always_happens_before[cs: Ctrl, o: Object, first: (CallArgument + CallSite), next: (CallArgument + CallSite)] {
    not (
        some c: cs | 
        some a: Object | {
            o = a or o in Type and a->o in c.types
            a -> next in ^(c.flow + arg_call_site - 
                (first->CallSite + CallArgument->first))
        }
    )
}

pred check_always_happens[c: Ctrl] {
    all o : labeled_objects[Type, sensitive], a : labeled_objects[CallArgument, sink] | 
        flows_to_ctrl[c, o, a] implies ( 
            some chks : labeled_objects[Object, checks] {
				chks -> a.arg_call_site in (c.flow + c.ctrl_flow)
				and flows_to_ctrl[c, o, chks]
			}
        )
}

pred only_send_to_allowed_sources[c: Ctrl] {
    all o : Object | 
        all scope : labeled_objects_with_types[c, Object, scopes] |
            flows_to_ctrl[c, o, scope]
            implies {
                (some o & safe_sources[c]) // either it is safe itself
                or always_happens_before[c, o, labeled_objects_with_types[c, Object, safe_source + safe_source_with_bless + bless_safe_source], scope] // obj must go through something in safe before scope
                or (some safe : safe_sources[c] |
                    flows_to_ctrl[c, safe, o]) // safe must have flowed to obj at some point
            }
}
