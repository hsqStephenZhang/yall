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

    let actioner = SemanticAction {
        context: std::collections::HashMap::from([
            ("a".into(), 1),
            ("b".into(), 2),
            ("c".into(), 3),
            ("d".into(), 4),
        ]),
    };
    let parser = calculator::ExprParser::new(actioner);
    let input = "a * ( b * ( c + d ) )";
    let tokens: Vec<ast::Token> = input.split_whitespace().map(|s| ast::Token::from(s)).collect();
    let res = parser.parse(tokens.into_iter().peekable());
    println!("Parse result: {:?}", res);
}
