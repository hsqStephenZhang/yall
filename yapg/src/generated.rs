#[allow(warnings)]
#[allow(unused)]
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
pub enum Token {
    LParen,
    RParen,
    Plus,
    Star,
    Identifier(String),
}

// for `parse_lines` convenience
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

pub struct SemanticAction;

impl SemanticAction {
    pub fn rule1(&mut self, stack_top: (Box<Expr>, Opcode, Box<Expr>)) -> Box<Expr> {
        let (arg1, arg2, arg3) = stack_top;
        println!("Building Expr Op Node: {:?} {:?} {:?}", arg1, arg2, arg3);
        Box::new(Expr::Op(arg1, arg2, arg3))
    }
}

/// generated

impl crate::grammar::TerminalKind for Token {
    fn id(&self) -> &str {
        match self {
            Token::Plus => "+",
            Token::Star => "*",
            Token::LParen => "(",
            Token::RParen => ")",
            Token::Identifier(..) => "identifier",
        }
    }
}
impl From<Token> for Value {
    fn from(token: Token) -> Self {
        Value::Token(token)
    }
}
#[derive(Debug)]
enum Value {
    Term(Box<Expr>),
    Expr(Box<Expr>),
    FactorOp(Opcode),
    ExprOp(Opcode),
    Factor(Box<Expr>),
    Token(Token),
}
impl Value {
    fn into_term(self) -> Box<Expr> {
        match self {
            Value::Term(v) => v,
            _ => panic!("expected Term node"),
        }
    }
    fn into_expr(self) -> Box<Expr> {
        match self {
            Value::Expr(v) => v,
            _ => panic!("expected Expr node"),
        }
    }
    fn into_factorop(self) -> Opcode {
        match self {
            Value::FactorOp(v) => v,
            _ => panic!("expected FactorOp node"),
        }
    }
    fn into_exprop(self) -> Opcode {
        match self {
            Value::ExprOp(v) => v,
            _ => panic!("expected ExprOp node"),
        }
    }
    fn into_factor(self) -> Box<Expr> {
        match self {
            Value::Factor(v) => v,
            _ => panic!("expected Factor node"),
        }
    }
    fn into_token(self) -> Token {
        match self {
            Value::Token(v) => v,
            _ => panic!("expected Token node"),
        }
    }
}
#[allow(unused)]
#[allow(clippy::ptr_arg)]
fn rule_0(action: &mut SemanticAction, stack: &mut Vec<Value>) -> Value {
    unreachable!("rule 0's action should never be called")
}
#[allow(unused)]
fn rule_1(action: &mut SemanticAction, stack: &mut Vec<Value>) -> Value {
    let arg3 = stack.pop().unwrap().into_factor();
    let arg2 = stack.pop().unwrap().into_exprop();
    let arg1 = stack.pop().unwrap().into_expr();
    let args = (arg1, arg2, arg3);
    let result = SemanticAction::rule1(action, args);
    Value::Expr(result)
}
#[allow(unused)]
fn rule_2(action: &mut SemanticAction, stack: &mut Vec<Value>) -> Value {
    let arg1 = stack.pop().unwrap().into_factor();
    let result = { arg1 };
    Value::Expr(result)
}
#[allow(unused)]
fn rule_3(action: &mut SemanticAction, stack: &mut Vec<Value>) -> Value {
    let arg1 = stack.pop().unwrap().into_token();
    let result = { Opcode::Add };
    Value::ExprOp(result)
}
#[allow(unused)]
fn rule_4(action: &mut SemanticAction, stack: &mut Vec<Value>) -> Value {
    let arg3 = stack.pop().unwrap().into_term();
    let arg2 = stack.pop().unwrap().into_factorop();
    let arg1 = stack.pop().unwrap().into_factor();
    let result = { Box::new(Expr::Op(arg1, arg2, arg3)) };
    Value::Factor(result)
}
#[allow(unused)]
fn rule_5(action: &mut SemanticAction, stack: &mut Vec<Value>) -> Value {
    let arg1 = stack.pop().unwrap().into_term();
    let result = { arg1 };
    Value::Factor(result)
}
#[allow(unused)]
fn rule_6(action: &mut SemanticAction, stack: &mut Vec<Value>) -> Value {
    let arg1 = stack.pop().unwrap().into_token();
    let result = { Opcode::Mul };
    Value::FactorOp(result)
}
#[allow(unused)]
fn rule_7(action: &mut SemanticAction, stack: &mut Vec<Value>) -> Value {
    let arg1 = stack.pop().unwrap().into_token();
    let result = { Box::new(Expr::Identifier(arg1.into())) };
    Value::Term(result)
}
#[allow(unused)]
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
fn __is_final_state(state_id: usize) -> bool {
    match state_id {
        3usize | 7usize | 12usize | 11usize | 9usize | 4usize | 13usize | 5usize | 2usize => true,
        _ => false,
    }
}
const START_STATE: usize = 0usize;
const END_STATE: usize = 4usize;
fn __transition12(id: &str) -> Option<usize> {
    match id {
        "FactorOp" => Some(10usize),
        "*" => Some(9usize),
        _ => None,
    }
}
fn __transition0(id: &str) -> Option<usize> {
    match id {
        "(" => Some(1usize),
        "Expr" => Some(4usize),
        "Factor" => Some(5usize),
        "identifier" => Some(2usize),
        "Term" => Some(3usize),
        _ => None,
    }
}
fn __transition6(id: &str) -> Option<usize> {
    match id {
        "+" => Some(7usize),
        "ExprOp" => Some(8usize),
        ")" => Some(11usize),
        _ => None,
    }
}
fn __transition1(id: &str) -> Option<usize> {
    match id {
        "identifier" => Some(2usize),
        "(" => Some(1usize),
        "Factor" => Some(5usize),
        "Term" => Some(3usize),
        "Expr" => Some(6usize),
        _ => None,
    }
}
fn __transition8(id: &str) -> Option<usize> {
    match id {
        "identifier" => Some(2usize),
        "(" => Some(1usize),
        "Term" => Some(3usize),
        "Factor" => Some(12usize),
        _ => None,
    }
}
fn __transition10(id: &str) -> Option<usize> {
    match id {
        "identifier" => Some(2usize),
        "(" => Some(1usize),
        "Term" => Some(13usize),
        _ => None,
    }
}
fn __transition5(id: &str) -> Option<usize> {
    match id {
        "FactorOp" => Some(10usize),
        "*" => Some(9usize),
        _ => None,
    }
}
fn __transition4(id: &str) -> Option<usize> {
    match id {
        "ExprOp" => Some(8usize),
        "+" => Some(7usize),
        _ => None,
    }
}
fn __transitions(cur: usize, id: &str) -> Option<usize> {
    match cur {
        12usize => __transition12(id),
        0usize => __transition0(id),
        6usize => __transition6(id),
        1usize => __transition1(id),
        8usize => __transition8(id),
        10usize => __transition10(id),
        5usize => __transition5(id),
        4usize => __transition4(id),
        _ => None,
    }
}
const REDUCE_RULE: &[Option<usize>] = &[
    None,
    None,
    Some(7usize),
    Some(5usize),
    Some(0usize),
    Some(2usize),
    None,
    Some(3usize),
    None,
    Some(6usize),
    None,
    Some(8usize),
    Some(1usize),
    Some(4usize),
];
const RULES: &[(&str, &[&str])] = &[
    ("Expr'", &["Expr"]),
    ("Expr", &["Expr", "ExprOp", "Factor"]),
    ("Expr", &["Factor"]),
    ("ExprOp", &["+"]),
    ("Factor", &["Factor", "FactorOp", "Term"]),
    ("Factor", &["Term"]),
    ("FactorOp", &["*"]),
    ("Term", &["identifier"]),
    ("Term", &["(", "Expr", ")"]),
];
fn __conflict_resolver(state: usize, token: &str) -> bool {
    match state {
        12usize => match token {
            "+" | ")" => true,
            _ => false,
        },
        5usize => match token {
            "+" | ")" => true,
            _ => false,
        },
        _ => true,
    }
}
pub struct ExprParser<Actioner> {
    actioner: Actioner,
}
impl ExprParser<SemanticAction> {
    pub fn new(actioner: SemanticAction) -> Self {
        Self { actioner }
    }
    pub fn parse<I: Iterator<Item = Token>>(
        self,
        token_stream: std::iter::Peekable<I>,
    ) -> Option<Box<Expr>> {
        let actions = RULE_TABLE;
        let ctx = crate::parser::ParseContext {
            start_state: START_STATE,
            end_state: END_STATE,
            is_final_state: __is_final_state,
            transitions: __transitions,
            reduce_rule: REDUCE_RULE,
            rules: RULES,
            conflict_resolver: __conflict_resolver,
        };
        let mut pda: crate::parser::PdaImpl<'_, Value, SemanticAction> =
            crate::parser::PdaImpl::new(START_STATE, self.actioner, actions);
        if pda.process(token_stream, &ctx) { Some(pda.final_value().into_expr()) } else { None }
    }
}

#[test]
fn test_expr() {
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
    let res = parser.parse(ts.into_iter().peekable()).unwrap();
    println!("Result: {:?}", res);
}
