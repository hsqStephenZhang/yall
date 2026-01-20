mod ast;
mod lexer;

pub mod parser {
    include!(concat!(env!("OUT_DIR"), "/json.yapg.rs"));
}

fn main() {
    let _ = tracing_subscriber::fmt()
        .with_max_level(tracing::Level::TRACE)
        .with_test_writer()
        .try_init();

    let parser = parser::ValueParser::new(());
    let input = "{ \"k1\" : \"v1\" , \"k2\" : [ true , false , null ] }";
    let tokens: Vec<lexer::Token> = input.split_whitespace().map(lexer::Token::from).collect();
    let res = parser.parse(tokens.into_iter().peekable());
    println!("Parse result: {:?}", res);
}
