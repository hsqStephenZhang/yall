use logos::Logos;

use crate::ast::Token;

mod parser {
    include!(concat!(env!("OUT_DIR"), "/lambda.yapg.rs"));
}

mod ast;

fn main() {
    let examples = vec!["λ x . x", "(f x)", "x:Int", "\\ x . x"];

    for (i, input) in examples.iter().enumerate() {
        println!("\n=== Example {} ===", i + 1);
        println!("Input:\n{}", input.trim());

        let lexer = Token::lexer(input);
        let tokens: Vec<_> = lexer.collect();

        let parser = parser::ExpressionParser::new(());
        match parser.parse(tokens.into_iter().map(|r| r.unwrap()).peekable()) {
            Some(ast) => {
                println!("AST:\n{:?}", ast);
            }
            None => {
                println!("Error during parsing");
            }
        }
    }
}
