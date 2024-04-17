// impl Eval { fn as_ref(&self) -> &str; }
#[derive(strum::AsRefStr)]
enum Eval {
    Not(Box<Eval>),
    Src { code: &'static str, result: bool },
    All(Vec<IterItem>),
    Or { left: Box<Eval>, right: Box<Eval> },
}

struct IterItem {
    item_rendering: String,
    body_eval: Eval,
}

impl Eval {
    fn success(&self) -> bool {
        match self {
            Self::Src { result, .. } => *result,
            Self::All(children) => children.iter().all(|c| c.body_eval.success()),
            Self::Not(inner) => !inner.success(),
            Self::Or { left, right } => left.success() || right.success(),
        }
    }

    fn children_where(&self, expectation: bool) -> Vec<(String, &Eval)> {
        let mut succeeding = vec![];
        match self {
            Self::All(children) => succeeding.extend(
                children
                    .iter() // : Iterator<Item = &IterItem>
                    .filter(|c| c.body_eval.success() != expectation)
                    .map(|c| (format!("i = {}", &c.item_rendering), &c.body_eval)),
            ),
            Self::Not(inner) if inner.success() == expectation => {
                succeeding.push(("not".to_owned(), inner.as_ref()))
            }
            Self::Or { left, right } => succeeding.extend(
                [
                    ("left hand side".to_owned(), left.as_ref()),
                    ("right hand side".to_owned(), right.as_ref()),
                ]
                .into_iter()
                .filter(|c| expectation != c.1.success()),
            ),
            _ => (),
        }
        succeeding
    }

    fn all<D: std::fmt::Debug>(iterator: Vec<D>, mut body: impl FnMut(D) -> Eval) -> Eval {
        Self::All(
            iterator
                .into_iter()
                .map(|item| IterItem {
                    item_rendering: format!("{item:?}"),
                    body_eval: body(item),
                })
                .collect(),
        )
    }

    fn or(left: Eval, right: Eval) -> Eval {
        Self::Or {
            left: Box::new(left),
            right: Box::new(right),
        }
    }

    fn emit(&self, prefix: &str, expectation: bool) {
        if self.success() != expectation {
            println!("{prefix}'{}' operator failed", self.as_ref());
            if let Self::All(inner) = self {
                if inner.is_empty() {
                    println!("{prefix}empty children");
                }
            }
            for (message, inner) in self.children_where(expectation) {
                println!("{prefix}Inner failure from {message}");
                inner.emit(
                    &format!("  {prefix}"),
                    match self {
                        Self::Not { .. } => !expectation,
                        _ => expectation,
                    },
                )
            }
        }
    }
    fn as_ref(&self) -> &str {
        match self {
            Self::Not { .. } => "not",
            Self::Or { .. } => "or",
            Self::All { .. } => "all",
            Self::Src { code, .. } => code,
        }
    }
}


macro_rules! src {
    ($($code:tt)*) => {
        Eval::Src {
            result: $($code)*,
            code: stringify!($($code)*),
        }
    }
}

fn main() {
    let my_policy_result = Eval::all(vec!["hello", "there"], |s: &str| {
        Eval::all(vec![1, 2, 3], |i: u32| {
            Eval::or(src!(s.flows_to(&i)), src!(i.flows_to(s)))
        })
    });

    my_policy_result.emit("", true);
    
}