#lang forge

/* This file is auto-generated by dfpp version 0.0.1. */

abstract sig Label {}
abstract sig Object {
    labels: set Label
}
sig Function extends Object {}
abstract sig Src extends Object {}
sig FormalParameter extends Src {
    fp_fun_rel: set Function,
    fp_ann: set Function->Label
}
abstract sig Sink extends Object {}
one sig Return extends Sink {}
sig CallArgument extends Sink {
    arg_call_site: one CallSite
}
sig Type extends Object {
    otype: set Type
}
sig CallSite extends Src {
    function: one Function
}
sig Ctrl extends Function {
    flow: set Src->Sink,
    ctrl_flow: set Src->CallSite,
    types: set Src->Type
}

one sig exception extends Label {}
one sig sink extends Label {}
one sig input extends Label {}


inst Flows {
    Label = `sink+`input+`exception
    input = `input
    exception = `exception
    sink = `sink
    CallSite = `cs_sink1_197f1c_8458c6+`cs_sink2_d0c5a8_36d2f9
    FormalParameter = `fp1_controller_fe8a7b+`fp0_controller_fe8a7b+`fp0_sink1_197f1c+`fp0_sink2_d0c5a8
    Src = FormalParameter+CallSite
    Return = `Return
    CallArgument = `arg0_cs_sink1_197f1c_8458c6+`arg0_cs_sink2_d0c5a8_36d2f9
    Sink = Return+CallArgument
    Type = `Foo_409cfa
    Ctrl = `controller_fe8a7b
    Function = `sink1_197f1c+`sink2_d0c5a8 + Ctrl
    Object = Function+Sink+Src+Type
    
    flow = 
        (`controller_fe8a7b)->(
            (`fp1_controller_fe8a7b)->(`arg0_cs_sink2_d0c5a8_36d2f9) +
            (`fp0_controller_fe8a7b)->(`arg0_cs_sink1_197f1c_8458c6))
    ctrl_flow = 
        (`controller_fe8a7b)->(
            none->none)
    types = 
        (`controller_fe8a7b)->(
            (`fp0_controller_fe8a7b)->(`input) +
            (`fp1_controller_fe8a7b)->(`input))
    labels = (
        (`arg0_cs_sink1_197f1c_8458c6 + `sink1_197f1c + `fp0_sink1_197f1c)->(`sink) +
        (`arg0_cs_sink2_d0c5a8_36d2f9 + `sink2_d0c5a8 + `fp0_sink2_d0c5a8)->(`sink) +
        (`Foo_409cfa)->(`input) +
        none->none
    )
    arg_call_site = (
        (`arg0_cs_sink2_d0c5a8_36d2f9)->(`cs_sink2_d0c5a8_36d2f9) +
        (`arg0_cs_sink1_197f1c_8458c6)->(`cs_sink1_197f1c_8458c6)
    )
    function = (
        (`cs_sink2_d0c5a8_36d2f9)->(`sink2_d0c5a8) +
        (`cs_sink1_197f1c_8458c6)->(`sink1_197f1c)
    )
    otype = (
        none->none
    )
    fp_fun_rel = (
        (`fp1_controller_fe8a7b)->(`controller_fe8a7b) +
        (`fp0_controller_fe8a7b)->(`controller_fe8a7b) +
        (`fp0_sink2_d0c5a8)->(`sink2_d0c5a8) +
        (`fp0_sink1_197f1c)->(`sink1_197f1c)
    )
    fp_ann = (
        (`fp0_sink1_197f1c)->(`sink1_197f1c->sink) +
        (`fp0_sink2_d0c5a8)->(`sink2_d0c5a8->sink)
    )
}