use paralegal_flow::test_utils::InlineTestBuilder;

#[test]
fn clone_nesting() {
    InlineTestBuilder::new(stringify!(
        #[derive(Clone)]
        enum Opt<T> {
            Empty,
            Filled(T),
        }

        #[derive(Clone)]
        struct AStruct {
            f: usize,
            g: usize,
        }

        #[derive(Clone)]
        enum AnEnum {
            Var1(usize),
            Var2(String),
        }

        fn main() {
            let v0 = Opt::Filled(AStruct { f: 0, g: 0 }).clone();
            let v2 = Opt::Filled(AnEnum::Var1(0)).clone();
        }
    ))
    .check(|ctr| {})
}

#[test]
fn clone_test_2() {
    InlineTestBuilder::new(stringify!(
        #[derive(Clone)]
        pub(crate) enum IdOrNestedObject<Kind> {
            Id(Url),
            NestedObject(Kind),
        }

        #[derive(Clone)]
        struct Url(String);

        #[derive(Clone)]
        pub struct Vote {
            pub(crate) to: Vec<Url>,
        }

        #[derive(Clone)]
        pub struct AnnounceActivity {
            pub(crate) object: IdOrNestedObject<AnnouncableActivities>,
        }
        #[derive(Clone)]
        pub struct Tombstone {
            pub(crate) id: Url,
        }

        #[derive(Clone)]
        pub struct Delete {
            pub(crate) object: IdOrNestedObject<Tombstone>,
        }

        #[derive(Clone)]
        pub enum AnnouncableActivities {
            Vote(Vote),
            Delete(Delete),
        }

        fn main() {
            let v = AnnouncableActivities::Vote(Vote { to: vec![] }).clone();
        }
    ))
    .check(|_g| {})
}
