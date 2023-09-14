use std::sync::Arc;

use dfcheck::{dfgraph::Identifier, Context, Marker};

pub struct DeletionProp {
    cx: Arc<Context>,
}

impl DeletionProp {
    pub fn new(cx: Arc<Context>) -> Self {
        DeletionProp { cx }
    }

    fn flows_to_store(&self, t: Identifier) -> bool {
        let stores = Marker::new_intern("stores");

        for (c_id, c) in &self.cx.desc().controllers {
            let t_srcs = self.cx.srcs_with_type(c, t);
            let store_cs = self
                .cx
                .marked_sinks(c.data_sinks(), stores)
                .collect::<Vec<_>>();

            for t_src in t_srcs {
                for store in &store_cs {
                    if self.cx.flows_to(*c_id, t_src, store) {
                        return true;
                    }
                }
            }
        }

        false
    }

    fn flows_to_deletion(&self, t: Identifier) -> bool {
        let deletes = Marker::new_intern("deletes");

        let mut ots = self.cx.otypes(t);
        ots.push(t);

        for (c_id, c) in &self.cx.desc().controllers {
            for ot in &ots {
                let t_srcs = self.cx.srcs_with_type(c, *ot).collect::<Vec<_>>();
                let delete_cs = self
                    .cx
                    .marked_sinks(c.data_sinks(), deletes)
                    .collect::<Vec<_>>();

                for t_src in &t_srcs {
                    for delete in &delete_cs {
                        if self.cx.flows_to(*c_id, t_src, delete) {
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
        let sensitive = Marker::new_intern("sensitive");
        for (t, _) in self.cx.marked(sensitive) {
            if self.flows_to_store(*t) && !self.flows_to_deletion(*t) {
                println!("Found an error for type: {t:?}");
            }
        }
    }
}

fn main() {
    dfcheck::cli(|cx| DeletionProp::new(cx).check())
}
