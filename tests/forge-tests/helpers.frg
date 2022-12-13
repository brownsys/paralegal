#lang forge

open "analysis_result.frg"

pred flows_to[cs: Ctrl, o: Object, f : (CallArgument + CallSite)] {
    some c: cs |
    some a : Object | {
        o = a or o in Type and a->o in c.types
        some (c.flow.a + a.(c.flow)) // a exists in cs
        and (a -> f in ^(c.flow + arg_call_site))
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

fun recipients[f: CallSite, ctrl: Ctrl] : set Src {
    ctrl.flow.(labeled_objects[arguments[f], scopes])
}

pred authorized[principal: Src, c: Ctrl] {
    some principal & c.types.(labeled_objects[Type, auth_witness])
}

fun arguments[f : CallSite] : set CallArgument {
    arg_call_site.f
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

pred only_send_to_allowed_sources[c: Ctrl] {
    all o : Object | 
        all scope : labeled_objects_with_types[c, Object, scopes] |
            flows_to[c, o, scope]
            implies {
                (some o & labeled_objects_with_types[c, Object, safe_source]) // either it is safe itself
                or always_happens_before[c, o, labeled_objects_with_types[c, Object, safe_source], scope] // obj must go through something in safe before scope
                or (some safe : labeled_objects_with_types[c, Object, safe_source] |
                    flows_to[c, safe, o]) // safe must have flowed to obj at some point
            }
}
