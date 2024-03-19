#![feature(rustc_private)]

extern crate either;
extern crate rustc_hir;
extern crate rustc_middle;

use std::collections::HashSet;

use either::Either;
use flowistry_pdg_construction::{
    graph::{DepEdge, DepGraph},
    CallChanges, FakeEffect, FakeEffectKind, PdgParams, SkipCall,
};
use itertools::Itertools;
use rustc_hir::def_id::LocalDefId;
use rustc_middle::{
    mir::{Local, Place, ProjectionElem, Terminator, TerminatorKind},
    ty::TyCtxt,
};
use rustc_utils::{mir::borrowck_facts, source_map::find_bodies::find_bodies, PlaceExt};

fn get_main(tcx: TyCtxt<'_>) -> LocalDefId {
    find_bodies(tcx)
        .into_iter()
        .map(|(_, body_id)| tcx.hir().body_owner_def_id(body_id))
        .find(|def_id| match tcx.opt_item_name(def_id.to_def_id()) {
            Some(name) => name.as_str() == "main",
            None => false,
        })
        .expect("Missing main")
}

fn pdg(
    input: impl Into<String>,
    configure: impl for<'tcx> FnOnce(TyCtxt<'tcx>, PdgParams<'tcx>) -> PdgParams<'tcx> + Send,
    tests: impl for<'tcx> FnOnce(TyCtxt<'tcx>, DepGraph<'tcx>) + Send,
) {
    let _ = simple_logger::init_with_env();
    rustc_utils::test_utils::compile(input, move |tcx| {
        let def_id = get_main(tcx);
        let params = configure(tcx, PdgParams::new(tcx, def_id));
        let pdg = flowistry_pdg_construction::compute_pdg(params);
        tests(tcx, pdg)
    })
}

#[allow(unused)]
fn viz(g: &DepGraph<'_>) {
    g.generate_graphviz(format!(
        "{}/../../target/graph.pdf",
        env!("CARGO_MANIFEST_DIR")
    ))
    .unwrap();
}

fn connects<'tcx>(
    tcx: TyCtxt<'tcx>,
    g: &DepGraph<'tcx>,
    src: &str,
    dst: &str,
    edge: Option<&str>,
) -> bool {
    let node_map = g
        .graph
        .node_indices()
        .filter_map(|node_index| {
            let node = &g.graph[node_index];
            Some((node.place_pretty()?, node_index))
        })
        .into_grouping_map()
        .collect::<HashSet<_>>();

    let lookup_node = |mut k: &str| {
        k = k.trim_matches(|c| c == '(' || c == ')');
        node_map
            .get(k)
            .unwrap_or_else(|| {
                panic!(
                    "Could not find node `{k}`. Options were: {:?}",
                    node_map.keys().collect::<Vec<_>>()
                )
            })
            .clone()
    };
    let srcs = lookup_node(src);
    let dsts = lookup_node(dst);

    let edge_map = g
        .graph
        .edge_indices()
        .filter_map(|edge| {
            let DepEdge { at, .. } = g.graph[edge];
            let body_with_facts =
                borrowck_facts::get_body_with_borrowck_facts(tcx, at.leaf().function);
            let Either::Right(Terminator {
                kind: TerminatorKind::Call { func, .. },
                ..
            }) = body_with_facts
                .body
                .stmt_at(at.leaf().location.as_location()?)
            else {
                return None;
            };
            let (def_id, _) = func.const_fn_def()?;
            let name = tcx.opt_item_name(def_id)?.to_string();
            let (src, dst) = g.graph.edge_endpoints(edge).unwrap();
            Some((name, (src, dst)))
        })
        .into_grouping_map()
        .collect::<HashSet<_>>();

    let edges = edge.map(|edge| {
        edge_map
            .get(edge)
            .unwrap_or_else(|| {
                panic!(
                    "Could not find edge `{edge}`. Options were: {:?}",
                    edge_map.keys().collect::<Vec<_>>()
                )
            })
            .clone()
    });

    srcs.iter().any(|src| {
        dsts.iter().any(|dst| {
            let paths =
                petgraph::algo::all_simple_paths::<Vec<_>, _>(&g.graph, *src, *dst, 0, None)
                    .collect::<Vec<_>>();
            !paths.is_empty()
                && match edges.as_ref() {
                    Some(edges) => paths.iter().any(|path| {
                        path.iter()
                            .tuple_windows()
                            .any(|(n1, n2)| edges.contains(&(*n1, *n2)))
                    }),
                    None => true,
                }
        })
    })
}

macro_rules! pdg_constraint {
  (($src:tt -> $dst:expr), $($arg:expr),*) => {{
    let src = stringify!($src);
    let dst = stringify!($dst);
    assert!(connects($($arg),*, src, dst, None), "{src} -> {dst}")
  }};
  (($src:tt -/> $dst:expr), $($arg:expr),*) => {{
    let src = stringify!($src);
    let dst = stringify!($dst);
    assert!(!connects($($arg),*, src, dst, None), "{src} -/> {dst}")
  }};
  (($src:tt - $op:tt > $dst:expr), $($arg:expr),*) => {{
    let src = stringify!($src);
    let dst = stringify!($dst);
    let op = stringify!($op);
    assert!(connects($($arg),*, src, dst, Some(op)), "{src} -{{{op}}}> {dst}")
  }};
  (($src:tt - $op:tt /> $dst:expr), $($arg:expr),*) => {{
    let src = stringify!($src);
    let dst = stringify!($dst);
    let op = stringify!($op);
    assert!(!connects($($arg),*, src, dst, Some(op)), "{src} -{{{op}}}/> {dst}")
  }}
}

macro_rules! pdg_test {
  ($name:ident, { $($i:item)* }, $($cs:tt),*) => {
    pdg_test!($name, { $($i)* }, |_, params| params, $($cs),*);
  };
  ($name:ident, { $($i:item)* }, $e:expr, $($cs:tt),*) => {
    #[test]
    fn $name() {
      let input = stringify!($($i)*);
      pdg(input, $e, |tcx, g| {
        if std::env::var("VIZ").is_ok() {
            g.generate_graphviz(format!("../../target/{}.pdf", stringify!($name))).unwrap();
        }
        $(pdg_constraint!($cs, tcx, &g));*
      })
    }
  };
}

pdg_test! {
  dep_simple,
  {
    fn main() {
      let mut x = 1;
      let y = if x > 0 {
        2
      } else {
        3
      };
      let z = y;
    }
  },
  (x -> y),
  (y -/> x),
  (y -> z),
  (z -/> y),
  (z -/> x)
}

pdg_test! {
  dep_alias_simple,
  {
    fn main() {
      let mut x = 1;
      let y = &mut x;
      *y += 1;
      let z = x;
    }
  },
  (x -> z),
  (y -> z)
}

pdg_test! {
  dep_alias_dynamic,
  {
    fn main() {
      let mut a = 1;
      let mut b = 2;
      let c = 3;
      let r = if c == 0 {
        &mut a
      } else {
        &mut b
      };
      *r += 1;
      let d = a;
    }
  },
  (c -> d)
}

pdg_test! {
  dep_fields,
  {
    fn main() {
      let mut x = (1, 2);
      x.0 += 1;
      let y = x.0;
      let z = x.1;
      x = (3, 4);
      let w = x.0;
    }
  },
  ((x.0) -> y),
  ((x.1) -> z),
  ((x.0) -/> z),
  ((x.1) -/> y)
}

pdg_test! {
  strong_update,
  {
    fn main() {
      let x = 1;
      let y = 2;
      let mut z = x;
      z = y;
      let w = z;
    }
  },
  (y -> w),
  (x -/> w)
}

pdg_test! {
  inline_simple,
  {
    fn foo(x: i32) -> i32 {
      let y = x + 1;
      y
    }
    fn main() {
      let a = 1;
      let c = foo(a);
      let b = c;
    }
  },
  (a -> x),
  (x -> y),
  (a -> y),
  (y -> b),
  (a -> b)
}

pdg_test! {
  inline_refs,
  {
    fn foo(x: &mut i32, y: i32, z: i32) {
      *x += y;
    }
    fn main() {
      let mut a = 1;
      let b = 2;
      let c = 3;
      foo(&mut a, b, c);
      let d = a;
    }
  },
  (a -> d),
  (b -> d),
  (c -/> d)
}

pdg_test! {
  inline_fields,
  {
    fn foo(x: &mut (i32, i32), y: i32) {
      x.0 += y;
    }
    fn main() {
      let mut a = (0, 1);
      let b = 2;
      foo(&mut a, b);
      let c = a.0;
      let d = a.1;
    }
  },
  (b -> c),
  (b -/> d)
}

pdg_test! {
  external_funcs,
  {
    fn main() {
      let mut v = vec![1, 2, 3];
      let x = 4;
      v.push(x);
      let y = 0;
      let n = v.get(y);
    }
  },
  (x - push > v),
  (x - push > n),
  (y -/> v)
}

pdg_test! {
  function_cloning,
  {
    fn id(t: i32) -> i32 { t }

    fn main() {
      let x = 1;
      let y = 2;

      let a = id(x);
      let b = id(y);
    }
  },
  (x -> a),
  (x -/> b)
}

// TODO: fix the d -/> f arrow
// field-sensitivity issue where closure args aren't being splatted
pdg_test! {
  closure_simple,
  {
    fn main() {
      let a = 0;
      let b = 1;
      let c = 2;
      let d = 3;
      let f = (|x, y| {
        let e = a;
        b + x
      })(c, d);
    }
  },
  (a -/> f),
  // (d -/> f),
  (b -> f),
  (c -> f)
}

pdg_test! {
  trait_inline,
  {
    trait Foo {
      fn foo(x: i32, y: i32) -> i32;
    }

    struct Bar;
    impl Foo for Bar {
      fn foo(x: i32, y: i32) -> i32 { x }
    }

    fn call_foo<T: Foo>(a: i32, b: i32) -> i32 {
      T::foo(a, b)
    }

    fn main() {
      let i = 1;
      let j = 2;
      let k = call_foo::<Bar>(i, j);
    }
  },
  (i -> k),
  (j -/> k)
}

pdg_test! {
  cfa_simple,
  {
    fn call(f: impl Fn() -> i32)  -> i32 { f() }
    fn main() {
      let a = 0;
      let b = 1;
      let d = call(|| {
        let c = a;
        b
      });
    }
  },
  // (a -/> d),
  (b -> d)
}

pdg_test! {
  async_simple,
  {
    async fn main() {
      let a = 1;
      let b = a;
      let c = a;
    }
  },
  (a -> b),
  (a -> c),
  (b -/> c)
}

pdg_test! {
  async_inline,
  {
    async fn foo(x: i32, y: i32) -> i32 {
      x
    }

    async fn main() {
      let a = 1;
      let b = 2;
      let c = foo(a, b).await;
    }
  },
  (a -> c),
  (b -/> c)
}

pdg_test! {
  recursive,
  {
    fn f(x: i32) -> i32 {
      if x == 0 { 0 }
      else { g(x) }
    }
    fn g(y: i32) -> i32 {
      f(y - 1)
    }
    fn main() {
      let a = 1;
      let b = f(a);
    }
  },
  (a -> b)
}

pdg_test! {
  never_type,
  {
    fn main() -> ! {
      let mut x = 1;
      let y = x;
      loop {
        x += y;
      }
    }
  },
  (x -> y)
}

pdg_test! {
  loops,
  {
    fn main() {
      let mut x = 0;
      while x < 10 {
        let y = 1;
        x += y;
      }
      let z = x;
    }
  },
  (y -> z)
}

pdg_test! {
  vec,
  {
    fn main() {
      let mut v = Vec::new();
      v.push(0);
      let x = v.len();
    }
  },
  (v -> x)
}

pdg_test! {
    websubmit_email,
    {
        fn my_send(
            sender: String,
            recipients: Vec<String>,
            subject: String,
            text: String,
        ) {}

        fn main() {
            let sender = String::new();
            let recipients = Vec::new();
            let subject = String::new();
            let text = String::new();
            my_send(sender, recipients, subject, text)
        }
    },
    |_, params| {
        params.with_call_change_callback(move |_| {
            CallChanges::default().with_skip(SkipCall::Skip)
        })
    },
    (recipients -/> sender)
}

pdg_test! {
  call_filter,
  {
    fn no_inline(a: &mut i32, b: i32) {}

    fn nested_layer_one(c: &mut i32, d: i32) {
      nested_layer_two(c, d);
    }

    fn nested_layer_two(e: &mut i32, f: i32) {}

    fn main() {
      let mut x = 0;
      let y = 1;
      no_inline(&mut x, y);

      let mut w = 0;
      let z = 1;
      nested_layer_one(&mut w, z);
    }
  },
  |tcx, params| params.with_call_change_callback(move |info| {
      let name = tcx.opt_item_name(info.callee.def_id());
      let skip = if !matches!(name.as_ref().map(|sym| sym.as_str()), Some("no_inline"))
          && info.call_string.len() < 2
      {
          SkipCall::NoSkip
      } else {
          SkipCall::Skip
      };
      CallChanges::default().with_skip(skip)
  }),
  (y -> x),
  (z -> w)
}

pdg_test! {
  false_call_edges_unmodified,
  {
    fn fake(a: &mut i32, b: &i32) {}

    fn main() {
      let mut x = 0;
      let y = 0;
      fake(&mut x, &y);
      let z = x;
    }
  },
  (x -fake/> z)
}

pdg_test! {
  false_call_edges_modified,
  {
    fn fake(a: &mut i32, b: &i32) {}

    fn main() {
      let mut x = 0;
      let y = 0;
      fake(&mut x, &y);
      let z = x;
    }
  },
  |tcx, params| params.with_call_change_callback(
    move |info| {
        let name = tcx.opt_item_name(info.callee.def_id());
        if matches!(name.as_ref().map(|sym| sym.as_str()), Some("fake")) {
            let fake_write = FakeEffect {
                place: Place::make(Local::from_usize(1), &[ProjectionElem::Deref], tcx),
                kind: FakeEffectKind::Write,
            };
            let fake_read = FakeEffect {
                place: Place::make(Local::from_usize(2), &[ProjectionElem::Deref], tcx),
                kind: FakeEffectKind::Read,
            };
            let fake_effects = vec![fake_write, fake_read];
            CallChanges::default().with_fake_effects(fake_effects)
        } else {
            CallChanges::default()
        }
    },
  ),
  (x -fake> z),
  (y -fake> *b)
}