#![allow(unused)]

use std::collections::HashMap;

use yapg::grammar::TerminalKind;

// these are pre-defined AST nodes
#[derive(Debug)]
pub enum Expr {
    Identifier(Identifier),
    Op(Box<Expr>, Opcode, Box<Expr>),
    Evaluted(i32),
}

impl Expr {
    pub fn into_i32(self) -> i32 {
        match self {
            Expr::Evaluted(v) => v,
            _ => panic!("expected Evaluted Expr"),
        }
    }
}

#[derive(Debug)]
pub enum Factor {
    Term,
    FactorOp(Term, Opcode, Term),
}

#[derive(Debug)]
pub enum Term {
    Num(Box<Expr>),
    Expr(Box<Expr>),
}

#[derive(Debug)]
pub enum Opcode {
    Mul,
    Add,
}

#[derive(Debug)]
pub struct Identifier(pub String);

impl From<Token> for Identifier {
    fn from(token: Token) -> Self {
        match token {
            Token::Identifier(s) => Identifier(s),
            _ => panic!("expected Identifier token"),
        }
    }
}

#[derive(Debug, Clone, Eq)]
pub enum Token {
    LParen,
    RParen,
    Plus,
    Star,
    Identifier(String),
}

impl PartialEq for Token {
    fn eq(&self, other: &Self) -> bool {
        self.id() == other.id()
    }
}

impl std::hash::Hash for Token {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.id().hash(state);
    }
}

// for generate tokenstream from str
impl From<&str> for Token {
    fn from(s: &str) -> Self {
        match s {
            "(" => Token::LParen,
            ")" => Token::RParen,
            "+" => Token::Plus,
            "*" => Token::Star,
            id => Token::Identifier(id.to_string()),
        }
    }
}

pub struct SemanticAction;

impl SemanticAction {
    pub fn rule1(&mut self, stack_top: (Box<Expr>, Opcode, Box<Expr>)) -> Box<Expr> {
        let (arg1, arg2, arg3) = stack_top;
        println!("Building Expr Op Node: {:?} {:?} {:?}", arg1, arg2, arg3);
        Box::new(Expr::Op(arg1, arg2, arg3))
    }

    pub fn rule2(&mut self, term: Box<Expr>) -> Box<Expr> {
        println!("Building Expr from Term Node: {:?}", term);
        term
    }
}