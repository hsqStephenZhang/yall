mod ast;
mod lexer;

use lexer::Token;
use logos::Logos;

mod parser {
    include!(concat!(env!("OUT_DIR"), "/datalog.yapg.rs"));
}

fn main() {
    let e1 = r#"
parent(tom, bob).
parent(tom, liz).
parent(bob, ann).
parent(bob, pat).
parent(pat, jim).
"#;

    let e2 = r#"
ancestor(X, Y) :- parent(X, Y).
ancestor(X, Y) :- parent(X, Z), ancestor(Z, Y).
"#;

    let e3 = r#"
edge(1, 2).
edge(2, 3).
path(X, Y) :- edge(X, Y).
path(X, Y) :- edge(X, Z), path(Z, Y).
"#;

    let e4 = r#"
different(X, Y) :- X != Y.
same(X, Y) :- X = Y.
"#;

    let e5 = r#"
Result :- add(1, 2).
"#;

    let e6 = r#"
parent(tom, bob)~
"#;

    let e7 = r#"
(io).
"#;

    let e8 = r#"
edge("a", "b").
edge("b", "c").
edge("c", "d").
reachable(X, Y) :- edge(X, Y).
reachable(X, Y) :- edge(X, Z), reachable(Z, Y).
reachable("a", X)?
"#;

    let examples: Vec<&str> = vec![e1, e2, e3, e4, e5, e6, e7, e8];

    for (i, input) in examples.iter().enumerate() {
        println!("\n=== Example {} ===", i + 1);
        println!("Input:\n{}", input.trim());

        let lexer = Token::lexer(input);
        let tokenstream = lexer.into_iter().map(|tk| tk.unwrap()).collect::<Vec<_>>();
        match parser::ProgramParser::new(()).parse(tokenstream.into_iter().peekable()) {
            Some(program) => {
                println!("\n✓ Parsed successfully!");
                println!("{:#?}", program);
            }
            None => {
                println!("\n✗ Parse error");
            }
        }
    }
}
