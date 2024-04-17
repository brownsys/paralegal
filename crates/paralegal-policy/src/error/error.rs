pub enum Expr<T> {
    Policy(PolicyResult<T>), // Could be an all_flows inside for example
    SourceCode(String), // Everything thats big thats not in PolicyResult
    // Do we need something separate or smaller building blocks that could be normal DS?
    // Will we need to break open the Source Code Chunks? We should assume this is 
    // unbreakable source code chunks else we use PolicyResult
    // fix: make eval things different from error things. 
}
pub enum Eval<T> {
    SourceCode(Source<T>),
    Ops(EvalResult<T>),
}
impl Eval {
    fn failed(&self) 
}
pub struct Source<T> {
    result: T,
    error: Expr<T>,// has to be of form Expr::SourceCode(String)
}
pub enum Operator {
    And,
    Or,
    Not,
    Any,
    All,
    Bool,
}
pub struct EvalResult<T> {
    result: bool,// can just compute
    error: Expr<T>,
    operator: Operator
}
pub enum PolicyResult<T> {
    And(AndResult<T>),
    Or(OrResult<T>),
    Not(NotResult<T>),
    All(AllIterResult<T>),
    Any(AnyIterResult<T>),
    // None(NoneResult), // Like no flows-> none of these -> can be collapsible into a not any
}
pub enum AndResult<T> {
    Success(Box<Expr<T>>, Box<Expr<T>>), // What things can we compute the and over? Just bools
    LeftFailed(Box<Expr<T>>, Box<Expr<T>>),
    RightFailed(Box<Expr<T>>, Box<Expr<T>>),
    BothFailed(Box<Expr<T>>, Box<Expr<T>>),
}
pub struct AndEval<T> {
   result : bool,
   error: AndResult<T>,
}
pub fn AndE(lhs : Expr<T>, rhs : Expr<T>) -> EvalResult<T> {
    let left = boolE(lhs);
    let right = boolE(rhs);
    if left.result && right.result {
        return EvalResult {
            result : true,
            error : And( AndResult( Success( Box::new(left.error), Box::new(right.error))))
        }
    } else if left.result && !right.result {
        return EvalResult {
            result : false,
            error : And( AndResult( RightFailed( Box::new(left.error), Box::new(right.error))))
        }
    } else if right.result && !left.result {
        return EvalResult {
            result : false,
            error : And( AndResult( LeftFailed( Box::new(left.error), Box::new(right.error))))
        }
    } else {
        return EvalResult {
            result : false,
            error : And( AndResult( BothFailed( Box::new(left.error), Box::new(right.error))))
        }
    }
}
pub fn OrE(lhs : Expr<T>, rhs : Expr<T>) -> EvalResult<T> {
    let left = boolE(lhs);
    let right = boolE(rhs);
    if left.result && right.result {
        return EvalResult {
            result : true,
            error : Or( OrResult( BothTrue( Box::new(left.error), Box::new(right.error))))
        }
    } else if left.result && !right.result {
        return EvalResult {
            result : true,
            error : Or( OrResult( LeftTrue( Box::new(left.error), Box::new(right.error))))
        }
    } else if right.result && !left.result {
        return EvalResult {
            result : true,
            error : Or( OrResult( RightTrue( Box::new(left.error), Box::new(right.error))))
        }
    } else {
        return EvalResult {
            result : false,
            error : Or( OrResult( BothFailed( Box::new(left.error), Box::new(right.error))))
        }
    }
}
pub fn boolE(expr : Expr<T>) -> EvalResult<T> {
    match expr {
        Expr::SourceCode(src) => {
            if src.result {
                return EvalResult {result : true, error: src.error};
            } else {
                return EvalResult {result : false, error: src.error};
            }
        }
        Expr::Eval(eval_result) => {
            if eval.result {
                return EvalResult {result : true, error: src.error};
            } else {
                return EvalResult {result : false, error: src.error};
            }
        }
        Expr::Policy(_) => {
            println!("Can't have a policy result as an input to And");
        }
    }
}
// TODO: Expr needs to be chunks of policy code  that might be huge. It might have embedded PolicyResults
pub enum OrResult<T> {
    BothTrue(Box<Expr<T>>, Box<Expr<T>>),
    LeftTrue(Box<Expr<T>>, Box<Expr<T>>),
    RightTrue(Box<Expr<T>>, Box<Expr<T>>),
    BothFailed(Box<Expr<T>>, Box<Expr<T>>),
}
pub enum NotResult<T> {
    Success(Box<Expr<T>>), // not(x) = true
    Failure(Box<Expr<T>>)
}
pub fn NotE(expr:Expr<T>) -> EvalResult<T> {
    let res = boolE(expr);
    if res.result {
        return EvalResult{
            result : !res.result,
            error : NotResult( Failure(Box::new(res.error))),
        }
    } else {
        return EvalResult{
            result : !res.result,
            error : NotResult( Success(Box::new(res.error))),
        }
    }
}
pub enum AllResult{
    Success, // What should these store vs AllIterResult
    ChildFailed, // Maybe start by storing what child failed
    EmptySuccess,
}

pub struct AllIterResult<T> {
    result : AllResult, // success or failure
    args: Vec<T>, // Args can be different types. Is that an issue? 
    // Maybe bring them all into string using serilization
    // children: Vec<Expr>, // Different Exprs but tbf you should store the 
    // iterator values and local variables relevant to the snippet.
    failed_children: Vec<Box<Expr<T>>>,
    passing_children: Vec<Box<Expr<T>>>,
}
pub fn AllE(list: Vec<T>, body : Fn()) {
    // how to get list items in scope? Make it all a function that takes in
    let mut all_res = AllIterResult {
        result: True,
        args: list.clone(), // Cloning list to retain ownership
        failed_children: Vec::new(),
        passing_children: Vec::new(),
    };
    for i in list {
        let iter_res = body(i);
        all_res.result = all_res.result && iter_res.result;
        if iter_res.result {
            all_res.passing_children.push(Box::new(iter_res.error));
        } else {
            all_res.failed_children.push(Box::new(iter_res.error));
        }
    }
    return EvalResult {
        result :all_res.result, //redundant
        error : all_res
    }

    for i in list {
        i.flows_to(b); src!()
    }

}

pub fn AnyE(list: Vec<T>, body : Fn()) -> EvalResult<T> {
    // how to get list items in scope? Make it all a function that takes in
    let mut any_res = AnyIterResult {
        result: None,
        args: list.clone(), // Cloning list to retain ownership
        failed_children: Vec::new(),
        passing_children: Vec::new(),
    };
    let res = false;
    for i in list {
        let iter_res = body(i);
        if iter_res.result {
            res = true;
            any_res.passing_children.push(Box::new(iter_res.error));
        } else {
            any_res.failed_children.push(Box::new(iter_res.error));
        }
    }
    if res {
        any_res.result = AnyResult(Success);
    } else if len(list) == 0 {
        any_res.result = AnyResult(EmptyFailure);
    } else {
        any_res.result = AnyResult(ChildFailed);
    }
    return EvalResult {
        result : res,
        error : any_res
    }
}

AllE([1, 2, 3, 4, 5], |listitem: T| -> EvalResult<T> {And(listitem, true)});
/***
 * Example of AllIter Result:
 * result: ChildFailed
 * args: [serialized arguments into the iterator -> List to iterate through only]
 * children: [
 * First child executed an any within it. Now Expr is PolicyResult with AnyResult
 * ] else [
 * Some source code being evaluated within.
 * ]
 */

pub enum AnyResult{
    Success, // What should these store vs AllIterResult
    ChildFailed, // Maybe start by storing what child failed
    EmptyFailure,
}

 pub struct AnyIterResult<T> {
    result : AnyResult, // success or failure
    args: Vec<T>, // Args can be different types. Is that an issue? 
    // Maybe bring them all into string using serilization
    // children: Vec<Expr<T>>, // Different Exprs but tbf you should store the 
    // iterator values and local variables relevant to the snippet.
    // no need to differentiate failed and passing children because none passed
    // and only one needs to pass.
    failed_children: Vec<Box<Expr<T>>>,
    passing_children: Vec<Box<Expr<T>>>,
}





pub fn any_flow_errors<T>(res : AnyIterResult<T>, not: bool) {
    match res.result{
        AnyResult::Success => {
            if not {
                // this is causing failure
                println!("One of the elements of this list succeeded when they shouldn't have");
                for child in res.passing_children {
                    evaluate_errors(*child, not);
                }
            } else {
                return; // Any result was expected to succeed and succeeded
            }
        }
        AnyResult::ChildFailed => {
            if !not {
                println!("All of the children of the any iterator failed");
                // println!("One example of children is {} ", res.failed_children[0]); 
                // TODO: we don't want the expr, we want the resolution of the expr
                for child in res.failed_children {
                    // Generate message for each child that should have passed
                    evaluate_errors(*child, not); // pass down the not value without changing
                    // TODO: we assume that we are aware of all the not-ing through our iterator design
                }
            }
            // or expected to fail and failed.
        }
        AnyResult::EmptyFailure => {
            if !not {
                println!("Evaluated any over an empty list. Did you expect this list to be populated?");
                println!("This also makes any code within this any iterator unreachable!");
            }
        }
    }
}

pub fn not_errors<T>(res : NotResult<T>, not: bool) {
    match res {
        NotResult::Success(expr) => {
            // Then expr must have evaluated to false
            println!("The following expr evaluated to false as expected!")
        }
        NotResult::Failure(expr) => {
            // expr must be erroneously true.
            println!("The following expr evaluated to true as expected")
        }
    }
}

pub fn or_errors<T>(res : OrResult<T>) {
    match res {
        OrResult::Success(exprl, exprr) => {
            // Then expr must have evaluated to false
            println!("The Or operator succeeded - at least one of the exprs is true");
            evaluate_errors(*exprl, false);
            evaluate_errors(*exprr, false); // TODO: when to reset the nots and when to pass em down?
        }
        OrResult::Failure(exprl, exprr) => {
            // expr must be erroneously true.
            println!("The Or operator failed which means both the left and the right side failed");
            println!("Left Operation of the Or");
            evaluate_errors(*exprl, false);
            println!("Right Operation of the Or"); // TODO: do some indexing or toggle list
            evaluate_errors(*exprr, false);
        }
    }
}

// pub fn or_eval_and_collect<T>(res : OrResult<T>) {
//    let l = collect_errors(res.left);
//    let r = collect_errors(res.right);
//    match 
// }

// pub fn collect_errors<T>(expr : Expr<T>)

pub fn and_errors<T>(res : AndResult<T>) {
    match res {
        AndResult::Success(exprl, exprr) => {
            // Then expr must have evaluated to false
            println!("The And operator succeeded - both of the exprs are true");
            evaluate_errors(*exprl, false);
            evaluate_errors(*exprr, false);
        }
        AndResult::Failure(exprl, exprr) => {
            // expr must be erroneously true.
            println!("The And operator failed which means one of the left and the right side failed");
            println!("Left Operation of the And");
            evaluate_errors(*exprl, false);
            println!("Right Operation of the And"); // TODO: do some indexing or toggle list
            evaluate_errors(*exprr, false);
        }
    }
}

pub fn all_errors<T>(res : AllIterResult<T>) {
    match res.result {
        AllResult::Success => {
                // this is causing failure
            println!("All iter : All of the children succeeded");
            for child in res.passing_children {
                evaluate_errors(*child, false);
            }
        }
        AllResult::ChildFailed => {
            println!("All iter : Some of the children of the all iterator failed");
            // println!("One example of children is {} ", res.failed_children[0]); 
            // TODO: we don't want the expr, we want the resolution of the expr
            for child in res.failed_children {
                // Generate message for each child that should have passed
                evaluate_errors(*child, false); // pass down the not value without changing
                // TODO: we assume that we are aware of all the not-ing through our iterator design
            }
            // or expected to fail and failed.
        }
        AllResult::EmptySuccess => {
            println!("All iter : Evaluated any over an empty list so this all iterator passes but it is vacuous. Did you expect this list to be populated?");
            println!("This also makes any code within this any iterator unreachable!");
        }
    }
}

pub fn evaluate_errors<T>(expr : Expr<T>, not: bool) {
    match expr {
        Expr::Policy(policy_result) => {
            match policy_result {
                PolicyResult::Any(any_res) => {
                    any_flow_errors(any_res, not);
                }
                PolicyResult::Not(not_res) => {
                    not_errors(not_res, not);// should we invert not? Its whether the kids are notted right?
                }
                PolicyResult::Or(or_res) => {
                    or_errors(or_res);
                }
                PolicyResult::And(and_res) => {
                    and_errors(and_res);
                }
                PolicyResult::All(all_res) => {
                    all_errors(all_res);
                }
            }
        }
        Expr::SourceCode(src) => {
            // Found native source code
            // println!(src);
            return;
        }
    }
}

fn main() {
    
    let mini: Expr<String> = Expr::Policy(
        PolicyResult::Any(
            AnyIterResult {
                result : AnyResult::EmptyFailure,
                args: vec![],
                failed_children: vec![],
                passing_children: vec![],
            }));
        evaluate_errors(mini, false);
    
    // Specifically there are no Comment types fetched into this controller which is why it was erroring. No sources
    // Lets expand this
    let mini2: Expr<String> = Expr::Policy(
        PolicyResult::Any(
            AnyIterResult {
                result : AnyResult::EmptyFailure,
                args: vec![],
                failed_children: vec![],
                passing_children: vec![],
            }));
            
    let controller1: Expr<String> = Expr::Policy(
        PolicyResult::All(
            AllIterResult {
                result : AllResult::ChildFailed,
                args : vec![], // Still not sure what this should be
                failed_children: vec![Box::new(mini2)], // let's assume this was the only type marked sensitive
                passing_children: vec![],
            }));
            evaluate_errors(controller1, false);
}

//  #[cfg(test)]
// mod tests {
//     #[test]
//     fn plume_test() {
//         let result = 2 + 2;
//         assert_eq!(result, 4);
//     }
// }
// Can't yet test because it's all stdoutput. could start returning things to test but visual is good for now.

// pub fn and_eval(l : bool, r : bool) {
//     // Need sth like bool_eval(l)-> collect errors -> r -> collect_errors
//     if (l && r) {
//         Expr::Policy(
//             PolicyResult::And(
//                 Success(
//                     Box::new(Expr::SourceCode(l)), 
//                     Box::new(Expr::SourceCode(r)))
//             )
//         )
//     } else {
//         PolicyResult::And(
//             Failure(
//             Box::new(Expr::SourceCode(l)), 
//             Box::new(Expr::SourceCode(r)))
//         )
//     }
// }

// pub fn not_eval(notev : bool) {
//     // first evaluate left then right
//     if (!notev) {
//         Expr::Policy(
//             PolicyResult::And(
//                 Success(
//                     Box::new(Expr::SourceCode(not_ev)))
//             )
//         )
//     } else {
//         Expr::Policy(
//             PolicyResult::And(
//                 Failure(
//                 Box::new(Expr::SourceCode(l)), 
//                 Box::new(Expr::SourceCode(r)))
//             )
//         )
//     }
// }




// Define a struct to hold error messages
struct ErrorMessage {
    message: String,
    children: Vec<ErrorMessage>,
}

// Recursive function to collect error messages
fn collect_errors(expr: &Expr<T>) -> ErrorMessage {
    match expr {
        Expr::Policy(policy_result) => {
            match policy_result {
                PolicyResult::Or(or_res) => {
                    let left_error = collect_errors(&or_res.left);
                    let right_error = collect_errors(&or_res.right);
                    ErrorMessage {
                        message: format!("One of the following conditions failed:"),
                        children: vec![left_error, right_error],
                    }
                }
                // Handle other cases similarly
            }
        }
        Expr::SourceCode(src) => {
            ErrorMessage {
                message: format!("Source code evaluation failed: {}", src),
                children: vec![],
            }
        }
    }
}

// Function to format error messages
fn format_error_message(error: &ErrorMessage, indent: usize) -> String {
    let mut formatted_message = format!("{}{}\n", "  ".repeat(indent), error.message);
    for child in &error.children {
        formatted_message += &format_error_message(child, indent + 1);
    }
    formatted_message
}

// Usage example
fn main() {
    let expr: Expr<T> = ...; // Define your expression
    let error = collect_errors(&expr);
    let formatted_error_message = format_error_message(&error, 0);
    println!("{}", formatted_error_message);
}


pub enum Evaluators {
    Not(NotEval),
    And(AndEval),
    Or(OrEval),
}

pub struct NotEval {
    expr : bool
}
pub enum NotResult<T> {
    Success(Box<Expr<T>>),
    Failure(Box<Expr<T>>)
}
pub fn not_evaluator(not_expr : NotEval) {
    if not_expr.expr { // TODO: This could be a boolean or a NotResult
        return NotResult::Success(Box::new)
    }
    // alt:

}   
pub fn collect_errors() {
    
}


// impl BitAnd<Expr> for Expr {
//     type Output = Expr; -> can be andresult but can be not'ed or or-ed later

//     fn bitand(self, rhs: Self) -> Self::Output {
//         if self && rhs {
//             AndResult::BothTrue
//         } else if !self {
//             AndResult::LhsFalse // implies
//         } else {
//             AndResult::RhsFalse
//         }
//     }
// }

// Alt: implement a .and() and .or() on Expr directly

// Now you can write src!(true) -> SourceCode{result: true, code : "true"}
macro_rules! src {
    ($($code:tt)*) => {
        Expr::SourceCode {
            result: $($code)*,
            code: stringify!($($code)*),
        }
    }
}

pub fn main() {
    src!(a.flows_to(b));
}
