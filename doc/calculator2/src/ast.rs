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

pub struct SemanticAction {
    pub context: HashMap<String, i32>,
}

impl SemanticAction {
    pub fn eval_bin(&mut self, stack_top: (Box<Expr>, Opcode, Box<Expr>)) -> Box<Expr> {
        let (arg1, arg2, arg3) = stack_top;
        let lhs = arg1.into_i32();
        let rhs = arg3.into_i32();
        match arg2 {
            Opcode::Add => Box::new(Expr::Evaluted(lhs + rhs)),
            Opcode::Mul => Box::new(Expr::Evaluted(lhs * rhs)),
        }
    }

    pub fn eval_var(&mut self, token: Token) -> Box<Expr> {
        match token {
            Token::Identifier(name) => {
                let value = *self.context.get(&name).unwrap_or(&0);
                Box::new(Expr::Evaluted(value))
            }
            _ => panic!("expected Identifier token"),
        }
    }
}
