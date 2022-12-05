#lang forge

open "helpers.frg"
open "../analysis_result.frg"

test expect {
    only_send_to_allowed: {
        only_send_to_allowed_sources[`process_if]
    } for Flows is theorem
}

// TODO: Automatically generate this file.
