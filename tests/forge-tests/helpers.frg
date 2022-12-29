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

fun arguments[f : CallSite] : set CallArgument {
    arg_call_site.f
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
