use std::sync::Arc;

use crate::{
    desc::Identifier,
    query::context::{Context, Label},
};

pub struct DeletionProp {
    cx: Arc<Context>,
}

impl DeletionProp {
    pub fn new(cx: Arc<Context>) -> Self {
        DeletionProp { cx }
    }

    fn flows_to_store(&self, t: &Identifier) -> bool {
        let stores = Label::intern("stores");

        for (c_id, c) in &self.cx.desc().controllers {
            let t_srcs = self.cx.srcs_with_type(c, t);
            let store_cs = self
                .cx
                .labeled_sinks(c.data_sinks(), stores)
                .collect::<Vec<_>>();

            for t_src in t_srcs {
                for store in &store_cs {
                    if self.cx.flows_to(c_id, t_src, store) {
                        return true;
                    }
                }
            }
        }

        false
    }

    fn flows_to_deletion(&self, t: &Identifier) -> bool {
        let deletes = Label::intern("deletes");

        let mut ots = self.cx.otypes(t);
        ots.push(*t);

        for (c_id, c) in &self.cx.desc().controllers {
            for ot in &ots {
                let t_srcs = self.cx.srcs_with_type(c, ot).collect::<Vec<_>>();
                let delete_cs = self
                    .cx
                    .labeled_sinks(c.data_sinks(), deletes)
                    .collect::<Vec<_>>();

                for t_src in &t_srcs {
                    for delete in &delete_cs {
                        if self.cx.flows_to(c_id, t_src, delete) {                            
                            println!("{t_src:?}\n->\n{delete:?}\nin\n{c_id:?}");
                            return true;
                        }
                    }
                }
            }
        }

        false
    }

    // Asserts that there exists one controller which calls a deletion
    // function on every value (or an equivalent type) that is ever stored.
    pub fn check(&self) {
        let sensitive = Label::intern("sensitive");
        for (t, _) in self.cx.labelled(sensitive) {            
            if self.flows_to_store(t) && !self.flows_to_deletion(t) {
                println!("Found an error for type: {t:?}");
            }
        }
    }
}
