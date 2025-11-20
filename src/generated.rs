use crate::{
    grammar::{TerminalKind, parse_lines},
    pda::{DFA, PDA, TokenStream},
};

// these are pre-defined AST nodes
#[derive(Debug)]
pub enum Expr {
    Identifier(Identifier),
    Op(Box<Expr>, Opcode, Box<Expr>),
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
    Div,
    Add,
    Sub,
}

#[derive(Debug)]
pub struct Identifier(String);

impl From<Token> for Identifier {
    fn from(token: Token) -> Self {
        match token {
            Token::Identifier(s) => Identifier(s),
            _ => panic!("expected Identifier token"),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum Token {
    LParen,
    RParen,
    Plus,
    Minus,
    Star,
    Devide,
    Identifier(String),
}

impl<'a> From<&'a str> for Token {
    fn from(s: &str) -> Self {
        match s {
            "(" => Token::LParen,
            ")" => Token::RParen,
            "+" => Token::Plus,
            "-" => Token::Minus,
            "*" => Token::Star,
            "/" => Token::Devide,
            id => Token::Identifier(id.to_string()),
        }
    }
}

impl TerminalKind for Token {
    fn id(&self) -> &str {
        match self {
            Token::LParen => "(",
            Token::RParen => ")",
            Token::Plus => "+",
            Token::Minus => "-",
            Token::Star => "*",
            Token::Devide => "/",
            Token::Identifier(_) => "identifier",
        }
    }
}

#[derive(Debug)]
pub enum Value {
    ExprOp(Opcode),
    Factor(Box<Expr>),
    FactorOp(Opcode),
    Term(Box<Expr>),
    Expr(Box<Expr>),
    Token(Token),
}

impl From<Token> for Value {
    fn from(token: Token) -> Self {
        Value::Token(token)
    }
}

impl Value {
    pub fn into_exprop(self) -> Opcode {
        match self {
            Value::ExprOp(v) => v,
            _ => panic!("expected ExprOp node"),
        }
    }
    pub fn into_factor(self) -> Box<Expr> {
        match self {
            Value::Factor(v) => v,
            _ => panic!("expected Factor node"),
        }
    }
    pub fn into_factorop(self) -> Opcode {
        match self {
            Value::FactorOp(v) => v,
            _ => panic!("expected FactorOp node"),
        }
    }
    pub fn into_term(self) -> Box<Expr> {
        match self {
            Value::Term(v) => v,
            _ => panic!("expected Term node"),
        }
    }
    pub fn into_expr(self) -> Box<Expr> {
        match self {
            Value::Expr(v) => v,
            _ => panic!("expected Expr node"),
        }
    }
    pub fn into_token(self) -> Token {
        match self {
            Value::Token(v) => v,
            _ => panic!("expected Token node"),
        }
    }
}
pub fn rule_1(stack: &mut Vec<Value>) -> Value {
    let arg3 = stack.pop().unwrap().into_factor();
    let arg2 = stack.pop().unwrap().into_exprop();
    let arg1 = stack.pop().unwrap().into_expr();
    let result = { Box::new(Expr::Op(arg1, arg2, arg3)) };
    Value::Expr(result)
}
pub fn rule_2(stack: &mut Vec<Value>) -> Value {
    let arg1 = stack.pop().unwrap().into_factor();
    let result = { arg1 };
    Value::Expr(result)
}
pub fn rule_3(stack: &mut Vec<Value>) -> Value {
    let arg1 = stack.pop().unwrap().into_token();
    let result = { Opcode::Add };
    Value::ExprOp(result)
}
pub fn rule_4(stack: &mut Vec<Value>) -> Value {
    let arg1 = stack.pop().unwrap().into_token();
    let result = { Opcode::Sub };
    Value::ExprOp(result)
}
pub fn rule_5(stack: &mut Vec<Value>) -> Value {
    let arg3 = stack.pop().unwrap().into_term();
    let arg2 = stack.pop().unwrap().into_factorop();
    let arg1 = stack.pop().unwrap().into_factor();
    let result = { Box::new(Expr::Op(arg1, arg2, arg3)) };
    Value::Factor(result)
}
pub fn rule_6(stack: &mut Vec<Value>) -> Value {
    let arg1 = stack.pop().unwrap().into_term();
    let result = { arg1 };
    Value::Factor(result)
}
pub fn rule_7(stack: &mut Vec<Value>) -> Value {
    let arg1 = stack.pop().unwrap().into_token();
    let result = { Opcode::Mul };
    Value::FactorOp(result)
}
pub fn rule_8(stack: &mut Vec<Value>) -> Value {
    let arg1 = stack.pop().unwrap().into_token();
    let result = { Opcode::Div };
    Value::FactorOp(result)
}
pub fn rule_9(stack: &mut Vec<Value>) -> Value {
    let arg1 = stack.pop().unwrap().into_token();
    let result = { Box::new(Expr::Identifier(arg1.into())) };
    Value::Term(result)
}
pub fn rule_10(stack: &mut Vec<Value>) -> Value {
    let arg3 = stack.pop().unwrap().into_token();
    let arg2 = stack.pop().unwrap().into_expr();
    let arg1 = stack.pop().unwrap().into_token();
    let result = { arg2 };
    Value::Term(result)
}
type ActionFn = fn(&mut Vec<Value>) -> Value;
const RULE_TABLE: &[ActionFn] = &[
    rule_1, rule_2, rule_3, rule_4, rule_5, rule_6, rule_7, rule_8, rule_9, rule_10,
];

static INIT: std::sync::Once = std::sync::Once::new();
fn setup() {
    INIT.call_once(|| {
        let _ = tracing_subscriber::fmt()
            .with_max_level(tracing::Level::TRACE)
            .with_test_writer()
            .try_init();
    });
}

#[test]
fn test_expr() {
    setup();
    let grammar = parse_lines::<_, Token>(
        "Expr",
        vec![
            "Expr -> Expr ExprOp Factor",
            "Expr -> Factor",
            "ExprOp -> +",
            "Factor -> Factor FactorOp Term",
            "Factor -> Term",
            "FactorOp -> *",
            "Term -> Identifier",
            "Term -> ( Expr )",
        ],
    );

    let dfa = DFA::build(&grammar);
    let mut pda = PDA::new(dfa, grammar, RULE_TABLE);
    let ts = TokenStream::new(vec![
        Token::Identifier("x".to_string()),
        Token::Plus,
        Token::Identifier("y".to_string()),
        Token::Star,
        Token::LParen,
        Token::Identifier("z".to_string()),
        Token::Plus,
        Token::Identifier("w".to_string()),
        Token::RParen,
    ]);

    let res = pda.process(ts);
    println!("Result: {}", res);
}
