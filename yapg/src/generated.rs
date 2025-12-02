#![allow(unused)]

use crate::grammar::TerminalKind;
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
enum Token {
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

impl TerminalKind for Token {
    fn id(&self) -> &str {
        match self {
            Token::LParen => "(",
            Token::RParen => ")",
            Token::Plus => "+",
            Token::Star => "*",
            Token::Identifier(_) => "identifier",
        }
    }
}

impl From<Token> for Value {
    fn from(token: Token) -> Self {
        Value::Token(token)
    }
}

pub struct SemanticAction;

impl SemanticAction {
    fn rule1(&mut self, stack_top: (Box<Expr>, Opcode, Box<Expr>)) -> Box<Expr> {
        let (arg1, arg2, arg3) = stack_top;
        println!("Building Expr Op Node: {:?} {:?} {:?}", arg1, arg2, arg3);
        Box::new(Expr::Op(arg1, arg2, arg3))
    }
}

#[derive(Debug)]
enum Value {
    ExprOp(Opcode),
    FactorOp(Opcode),
    Expr(Box<Expr>),
    Factor(Box<Expr>),
    Term(Box<Expr>),
    Token(Token),
}
impl Value {
    fn into_exprop(self) -> Opcode {
        match self {
            Value::ExprOp(v) => v,
            _ => panic!("expected ExprOp node"),
        }
    }
    fn into_factorop(self) -> Opcode {
        match self {
            Value::FactorOp(v) => v,
            _ => panic!("expected FactorOp node"),
        }
    }
    fn into_expr(self) -> Box<Expr> {
        match self {
            Value::Expr(v) => v,
            _ => panic!("expected Expr node"),
        }
    }
    fn into_factor(self) -> Box<Expr> {
        match self {
            Value::Factor(v) => v,
            _ => panic!("expected Factor node"),
        }
    }
    fn into_term(self) -> Box<Expr> {
        match self {
            Value::Term(v) => v,
            _ => panic!("expected Term node"),
        }
    }
    fn into_token(self) -> Token {
        match self {
            Value::Token(v) => v,
            _ => panic!("expected Token node"),
        }
    }
}
#[allow(clippy::ptr_arg)]
fn rule_0(action: &mut SemanticAction, stack: &mut Vec<Value>) -> Value {
    unreachable!("rule 0's action should never be called")
}
fn rule_1(action: &mut SemanticAction, stack: &mut Vec<Value>) -> Value {
    let arg3 = stack.pop().unwrap().into_factor();
    let arg2 = stack.pop().unwrap().into_exprop();
    let arg1 = stack.pop().unwrap().into_expr();
    let args = (arg1, arg2, arg3);
    let result = SemanticAction::rule1(action, args);
    Value::Expr(result)
}
fn rule_2(action: &mut SemanticAction, stack: &mut Vec<Value>) -> Value {
    let arg1 = stack.pop().unwrap().into_factor();
    let result = { arg1 };
    Value::Expr(result)
}
fn rule_3(action: &mut SemanticAction, stack: &mut Vec<Value>) -> Value {
    let arg1 = stack.pop().unwrap().into_token();
    let result = { Opcode::Add };
    Value::ExprOp(result)
}
fn rule_4(action: &mut SemanticAction, stack: &mut Vec<Value>) -> Value {
    let arg3 = stack.pop().unwrap().into_term();
    let arg2 = stack.pop().unwrap().into_factorop();
    let arg1 = stack.pop().unwrap().into_factor();
    let result = { Box::new(Expr::Op(arg1, arg2, arg3)) };
    Value::Factor(result)
}
fn rule_5(action: &mut SemanticAction, stack: &mut Vec<Value>) -> Value {
    let arg1 = stack.pop().unwrap().into_term();
    let result = { arg1 };
    Value::Factor(result)
}
fn rule_6(action: &mut SemanticAction, stack: &mut Vec<Value>) -> Value {
    let arg1 = stack.pop().unwrap().into_token();
    let result = { Opcode::Mul };
    Value::FactorOp(result)
}
fn rule_7(action: &mut SemanticAction, stack: &mut Vec<Value>) -> Value {
    let arg1 = stack.pop().unwrap().into_token();
    let result = { Box::new(Expr::Identifier(arg1.into())) };
    Value::Term(result)
}
fn rule_8(action: &mut SemanticAction, stack: &mut Vec<Value>) -> Value {
    let arg3 = stack.pop().unwrap().into_token();
    let arg2 = stack.pop().unwrap().into_expr();
    let arg1 = stack.pop().unwrap().into_token();
    let result = { arg2 };
    Value::Term(result)
}
type ActionFn = fn(&mut SemanticAction, &mut Vec<Value>) -> Value;
const RULE_TABLE: &[ActionFn] =
    &[rule_0, rule_1, rule_2, rule_3, rule_4, rule_5, rule_6, rule_7, rule_8];

#[test]
fn test_expr() {
    use crate::nfa_dfa::DFA;
    use crate::pda::*;
    use crate::tests::*;
    static INIT: std::sync::Once = std::sync::Once::new();
    INIT.call_once(|| {
        let _ = tracing_subscriber::fmt()
            .with_max_level(tracing::Level::TRACE)
            .with_test_writer()
            .try_init();
    });

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

    for (idx, rule) in grammar.rules.iter().enumerate() {
        println!("Rule ID {}: {:?}", idx, rule);
    }

    let dfa = DFA::build(&grammar);
    let code = dfa.generate_rust_code(&grammar).to_string();
    let actioner = SemanticAction;
    let mut pda = PDA::new(dfa, grammar, actioner, RULE_TABLE);
    let ts = vec![
        Token::Identifier("x".to_string()),
        Token::Plus,
        Token::Identifier("y".to_string()),
        Token::Star,
        Token::LParen,
        Token::Identifier("z".to_string()),
        Token::Plus,
        Token::Identifier("w".to_string()),
        Token::RParen,
    ];

    let res = pda.process(ts.into_iter().peekable());
    let top = pda.final_value();
    println!("Result: {}", res);
    println!("AST: {:?}", top.into_expr());

    println!("Generated DFA Code:\n{}", code);
}
