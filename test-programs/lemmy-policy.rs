policy!(community_prop, ctx {
    let mut db_write_nodes = marked_nodes(marker!(db_write));
    let mut community_struct_nodes = marked_nodes(marker!(community));
    let mut delete_check_nodes = marked_nodes(marker!(community_delete_check));
    let mut ban_check_nodes = marked_nodes(marker!(community_ban_check));

    // if some community_struct
    community_struct_nodes.all(|community_struct| {
        // flows to some write
        let community_writes : Vec<Node> = ctx
            .influencees(community_struct, EdgeType::Data)
            .filter(|n| db_write_nodes.contains(n))
            .collect();
        // then
        community_writes.all(|write| {
            let has_delete_check = delete_check_nodes.any(|delete_check| {
                // community struct flows to delete check and
                ctx.flows_to(community_struct, delete_check, EdgeType::Data) &&
                // delete check has ctrl flow influence on the write
                ctx.has_ctrl_influence(delete_check, write)
            });

            assert_error!(ctx, has_delete_check, "Unauthorized community write: no delete check");

            let has_ban_check = ban_check_nodes.any(|ban_check| {
                // community struct flows to ban check and
                ctx.flows_to(community_struct, ban_check, EdgeType::Data) &&
                // ban check has ctrl flow influence on the write
                ctx.has_ctrl_influence(ban_check, write)
            });

            assert_error!(ctx, has_ban_check, "Unauthorized community write: no ban check");
        })
    })
    Ok(())
});

policy!(instance_prop, ctx {
    let mut writes = marked_nodes(marker!(db_write));
    let mut reads = marked_nodes(marker!(db_read));
    let mut delete_checks = marked_nodes(marker!(instance_delete_check));
    let mut ban_checks = marked_nodes(makrer!(instance_ban_check));

    // all db writes must be authorized by a ban & delete check
    let delete_ok = writes.all(|write| {
        delete_checks.any(|dc| ctx.has_ctrl_flow_influence(dc, write)) &&
        ban_checks.any(|bc| ctx.has_ctrl_flow_influence(bc, write))
    });

    // all db reads (that are not reading the active user) must be authorized by a ban & delete check
    let ban_ok = reads.all(|read| {
        if ctx.has_marker(marker!(db_user_read), read) {
            continue;
        }
        delete_checks.any(|dc| ctx.has_ctrl_flow_influence(dc, read)) &&
        ban_checks.any(|bc| ctx.has_ctrl_flow_influence(bc, read))
    });
    
    let ok = delete_ok && ban_ok;

    assert_error!(ctx, ok, "Missing ban or delete check for instance authorization");
    if !ok {
        bail!("Found a failure");
    }

    Ok(())
});


