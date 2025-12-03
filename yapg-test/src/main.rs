use crate::ast::SemanticAction;

mod ast;

pub mod calculator {
    include!(concat!(env!("OUT_DIR"), "/calculator.yapg.rs"));
}

fn main() {
    let _ = tracing_subscriber::fmt()
        .with_max_level(tracing::Level::TRACE)
        .with_test_writer()
        .try_init();

    let actioner = SemanticAction;
    let parser = calculator::ExprParser::new(actioner);
    let input = "a + b";
    let tokens: Vec<ast::Token> = input.split_whitespace().map(|s| ast::Token::from(s)).collect();
    let res = parser.parse(tokens.into_iter().peekable());
    println!("Parse result: {:?}", res);
}
