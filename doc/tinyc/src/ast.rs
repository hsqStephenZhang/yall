use logos::Logos;

// This file defines the Abstract Syntax Tree (AST) structures used by the parser.
// It includes definitions for program, statements, expressions, and other components of the grammar.

#[derive(Logos, Debug, Clone, PartialEq)]
#[logos(skip r"[ \t\n\r]+")]
pub enum Token {
    #[token("if")]
    If,

    #[token("else")]
    Else,

    #[token("while")]
    While,

    #[token("do")]
    Do,

    #[token("(")]
    LParen,

    #[token(")")]
    RParen,

    #[token("{")]
    LBrace,

    #[token("}")]
    RBrace,

    #[token(";")]
    Semi,

    #[token("=")]
    Eq,

    #[token("<")]
    Lt,

    #[token("+")]
    Plus,

    #[token("-")]
    Minus,

    #[regex(r"[a-z]+", |lex| lex.slice().to_string())]
    String(String),

    #[regex(r"[0-9]+", |lex| lex.slice().parse().ok())]
    Int(i32),
}

impl Token {
    pub fn into_string(self) -> String {
        match self {
            Token::String(s) => s,
            _ => panic!("Expected String token"),
        }
    }

    pub fn into_int(self) -> i32 {
        match self {
            Token::Int(n) => n,
            _ => panic!("Expected Int token"),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Program {
    pub statements: Vec<Statement>,
}

impl std::fmt::Display for Program {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for stmt in &self.statements {
            writeln!(f, "{:?}", stmt)?;
        }
        Ok(())
    }
}

#[allow(unused)]
#[derive(Debug, Clone, PartialEq)]
pub enum Statement {
    If(Expr, Box<Statement>),
    IfElse(Expr, Box<Statement>, Box<Statement>),
    While(Expr, Box<Statement>),
    DoWhile(Box<Statement>, Expr),
    Block(Vec<Statement>),
    Expr(Expr),
    Empty,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Expr {
    Test(Test),
    Assign(String, Box<Expr>),
}

#[derive(Debug, Clone, PartialEq)]
pub enum Test {
    Sum(Sum),
    Lt(Sum, Sum),
}

#[derive(Debug, Clone, PartialEq)]
pub enum Sum {
    Term(Term),
    Add(Box<Sum>, Term),
    Sub(Box<Sum>, Term),
}

#[derive(Debug, Clone, PartialEq)]
pub enum Term {
    Id(String),
    Integer(i32),
    ParenExpr(Box<Expr>),
}