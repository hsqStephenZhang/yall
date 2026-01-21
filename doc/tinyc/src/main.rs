// This file is the entry point of the application. It initializes the parser and lexer, reads input files, and processes the parsed output.

mod ast;

mod parser {
    include!(concat!(env!("OUT_DIR"), "/tinyc.yapg.rs"));
}

use logos::Logos;

use crate::ast::Token;

fn main() {
    let args = std::env::args().collect::<Vec<_>>();
    if args.len() < 2 {
        eprintln!("Usage: {} <source-file>", args[0]);
        std::process::exit(1);
    }
    let filename = &args[1];
    let code = std::fs::read_to_string(filename).expect("Failed to read source file");
    run(&code);
}

pub fn run(code: &str) {
    let lexer = Token::lexer(code);
    let tokens: Vec<_> = lexer.collect();

    let parser = parser::ProgramParser::new(());
    match parser.parse(tokens.into_iter().map(|r| r.unwrap()).peekable()) {
        Some(ast) => {
            println!("AST:\n{}", ast);
        }
        None => {
            println!("Error during parsing");
        }
    }
}

#[test]
fn test() {
    let code = r#"
a = 0;
b = 1;
i = 0;
while (i < 10) {
    c = a + b;
    a = b;
    b = c;
    i = i + 1;
}
    "#;

    run(code);
}
