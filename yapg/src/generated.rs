#![allow(unused)]

use tracing::trace;

use crate::grammar::{Symbol, TerminalKind};
use crate::nfa_dfa::PrintableDFAState;
use crate::parser::{ParseContext, PdaImpl};
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

const FINAL_STATES_SET: phf::Set<usize> = phf::phf_set! { 3usize , 6usize , 2usize , 4usize , 13usize , 1usize , 11usize , 8usize , 12usize };
const STATES_NUM: usize = 14usize;
const START_STATE: usize = 0usize;
const END_STATE: usize = 2usize;
static TRANSITION0: phf::Map<&'static str, usize> = phf::phf_map! { "Factor" => 1usize , "Term" => 3usize , "identifier" => 4usize , "(" => 5usize , "Expr" => 2usize };
static TRANSITION1: phf::Map<&'static str, usize> =
    phf::phf_map! { "FactorOp" => 7usize , "*" => 6usize };
static TRANSITION2: phf::Map<&'static str, usize> =
    phf::phf_map! { "+" => 8usize , "ExprOp" => 9usize };
static TRANSITION3: phf::Map<&'static str, usize> = phf::phf_map! {};
static TRANSITION4: phf::Map<&'static str, usize> = phf::phf_map! {};
static TRANSITION5: phf::Map<&'static str, usize> = phf::phf_map! { "identifier" => 4usize , "Term" => 3usize , "(" => 5usize , "Factor" => 1usize , "Expr" => 10usize };
static TRANSITION6: phf::Map<&'static str, usize> = phf::phf_map! {};
static TRANSITION7: phf::Map<&'static str, usize> =
    phf::phf_map! { "(" => 5usize , "Term" => 11usize , "identifier" => 4usize };
static TRANSITION8: phf::Map<&'static str, usize> = phf::phf_map! {};
static TRANSITION9: phf::Map<&'static str, usize> = phf::phf_map! { "Factor" => 12usize , "(" => 5usize , "Term" => 3usize , "identifier" => 4usize };
static TRANSITION10: phf::Map<&'static str, usize> =
    phf::phf_map! { "ExprOp" => 9usize , "+" => 8usize , ")" => 13usize };
static TRANSITION11: phf::Map<&'static str, usize> = phf::phf_map! {};
static TRANSITION12: phf::Map<&'static str, usize> =
    phf::phf_map! { "*" => 6usize , "FactorOp" => 7usize };
static TRANSITION13: phf::Map<&'static str, usize> = phf::phf_map! {};
static TRANSITIONS: &[&phf::Map<&'static str, usize>] = &[
    &TRANSITION0,
    &TRANSITION1,
    &TRANSITION2,
    &TRANSITION3,
    &TRANSITION4,
    &TRANSITION5,
    &TRANSITION6,
    &TRANSITION7,
    &TRANSITION8,
    &TRANSITION9,
    &TRANSITION10,
    &TRANSITION11,
    &TRANSITION12,
    &TRANSITION13,
];
const REDUCE_RULE: &[Option<usize>] = &[
    None,
    Some(2usize),
    Some(0usize),
    Some(5usize),
    Some(7usize),
    None,
    Some(6usize),
    None,
    Some(3usize),
    None,
    None,
    Some(4usize),
    Some(1usize),
    Some(8usize),
];
const RULES: &[(&str, &[&str])] = &[
    ("S'", &["Expr"]),
    ("Expr", &["Expr", "ExprOp", "Factor"]),
    ("Expr", &["Factor"]),
    ("ExprOp", &["+"]),
    ("Factor", &["Factor", "FactorOp", "Term"]),
    ("Factor", &["Term"]),
    ("FactorOp", &["*"]),
    ("Term", &["identifier"]),
    ("Term", &["(", "Expr", ")"]),
];
static CONFLICT_RESOLVER: phf::Map<usize, phf::Set<&'static str>> = phf::phf_map! { 1usize => phf :: phf_set ! { "+" , ")" } , 2usize => phf :: phf_set ! { } , 12usize => phf :: phf_set ! { "+" , ")" } };

pub struct ExprParser<Actioner> {
    actioner: Actioner,
}

impl ExprParser<SemanticAction> {
    pub fn new(actioner: SemanticAction) -> Self {
        Self { actioner }
    }

    pub fn parse_inner<I: Iterator<Item = Token>>(
        self,
        token_stream: std::iter::Peekable<I>,
    ) -> Option<Box<Expr>> {
        let actions = RULE_TABLE;
        let ctx = ParseContext {
            start_state: START_STATE,
            end_state: END_STATE,
            final_states: FINAL_STATES_SET,
            transitions: TRANSITIONS,
            reduce_rule: REDUCE_RULE,
            rules: RULES,
            conflict_resolver: &CONFLICT_RESOLVER,
        };
        let mut pda: PdaImpl<'_, Value, SemanticAction> =
            PdaImpl::new(START_STATE, self.actioner, actions);
        if pda.process(token_stream, &ctx) { Some(pda.final_value().into_expr()) } else { None }
    }
}

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

    let parser = ExprParser::new(SemanticAction {});
    let res = parser.parse_inner(ts.into_iter().peekable()).unwrap();
    println!("Result: {:?}", res);
}
