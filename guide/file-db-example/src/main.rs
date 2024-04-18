pub struct QueryBuilder {
    /* ... */
}
impl QueryBuilder { // TODO
    fn add(&mut self, query: Query) { /* ... */ }
    #[paralegal::marker(executes, arguments = [0])]
    fn execute(&mut self) { /* ... */ }
}

enum Query {
    Delete(DeleteQuery),
    // Other variants here
}
#[derive(Debug)]
#[paralegal::marker(make_delete_query)]
struct DeleteQuery {
    id: Id,
    table_name: &'static str,
}
pub struct User {
    id : Id,
    /* ... */

}
#[paralegal::marker(user_data)]
pub struct Post {
    id : Id,
    /* ... */
}
#[paralegal::marker(user_data)]
pub struct Comment { 
    id: Id,
    /* ... */ 
}


#[derive(Copy)]
pub struct Id {
    id : String,
}
struct Authored {
    posts: Vec<Post>,
    comments: Vec<Comment>,
}
impl User {
    #[paralegal::analyze]
    fn delete_user(&self, builder: &mut QueryBuilder) {
        let authored: Authored = self.authored();
        builder.add(Query::Delete(DeleteQuery{id: self.id, table_name : "users"}));
        builder.execute();
        for post in &authored.posts { // TODO
            builder.add(Query::Delete(DeleteQuery{id : post.id, table_name: "posts"}));
        }
        // builder.execute();
        for comment in &authored.comments {
            builder.add(Query::Delete(DeleteQuery{id : comment.id, table_name : "comments"}));
        }
        // builder.execute();
    }
    fn authored(&self) -> Authored { /* ... */
        return Authored {
            posts : vec![],
            comments : vec![],
        };
    }
}

// controller.name
// defid -> 