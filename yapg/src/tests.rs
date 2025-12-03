use std::collections::HashSet;
use std::hash::Hash;

use crate::generator::*;
use crate::grammar::*;

pub fn parse_lines<S, T>(start_sym: &str, raw_rules: Vec<S>) -> Grammar<T>
where
    S: AsRef<str>,
    T: for<'a> From<&'a str> + Hash + Eq + std::fmt::Debug + Clone + TerminalKind,
{
    let start_sym = NonTerminal::new(start_sym);
    let pseudo_start_sym = NonTerminal::new("S'");

    let nonterms = raw_rules
        .iter()
        .map(|s| {
            let line = s.as_ref();
            let mut parts = line.split("->");
            parts.next().unwrap().trim()
        })
        .collect::<HashSet<_>>();

    let mut rules = vec![Rule {
        left: pseudo_start_sym.clone(),
        right: vec![Symbol::NonTerm(start_sym.clone())],
    }];

    rules.extend(raw_rules.iter().map(|line| {
        let line = line.as_ref();
        let mut parts = line.split("->");
        let left = parts.next().unwrap().trim();
        let right = parts.next().unwrap().trim();

        let left_nt = NonTerminal::new(left);
        let right_syms = if right == "ε" {
            vec![]
        } else {
            right
                .split_whitespace()
                .map(|s| {
                    if nonterms.contains(s) {
                        Symbol::NonTerm(NonTerminal::new(s))
                    } else {
                        Symbol::Term(T::from(s))
                    }
                })
                .collect()
        };

        Rule { left: left_nt, right: right_syms }
    }));

    Grammar::new(pseudo_start_sym, start_sym, rules)
}

#[test]
fn test_hardcode_expr_parser_generator() {
    let defs = vec![
        //  pub Expr: Box<Expr> = {
        //     Expr ExprOp Factor => `rule1`,   // expr -> expr + factor, expr -> expr - factor
        //     Factor                           // expr -> factor
        //  };
        GenRuleGroup {
            name: "Expr".to_string(),
            return_type: "Box<Expr>".to_string(),
            rules: vec![
                // Rule 1: Expr ExprOp Factor => `rule1`
                GenRule {
                    production: vec![
                        "Expr".to_string(),
                        "ExprOp".to_string(),
                        "Factor".to_string(),
                    ],
                    action: ActionKind::Sema("rule1".to_string()),
                },
                // Rule 2: Factor
                GenRule {
                    production: vec!["Factor".to_string()],
                    action: "arg1".to_string().into(),
                },
            ],
        },
        // ExprOp: Opcode = {
        //     Token::Plus => Opcode::Add,      // expr_op -> +
        // };
        GenRuleGroup {
            name: "ExprOp".to_string(),
            return_type: "Opcode".to_string(),
            rules: vec![
                // "+" => Opcode::Add
                GenRule {
                    production: vec!["Token::Plus".to_string()],
                    action: "Opcode::Add".to_string().into(),
                },
            ],
        },
        // Factor: Box<Expr> = {
        //     Factor FactorOp Term => Box::new(Expr::Op(<>)),  // factor -> factor * term, factor -> factor / term
        //     Term,                                            // factor -> term
        // };
        GenRuleGroup {
            name: "Factor".to_string(),
            return_type: "Box<Expr>".to_string(),
            rules: vec![
                // Factor FactorOp Term => Box::new(Expr::Op(<>))
                GenRule {
                    production: vec![
                        "Factor".to_string(),
                        "FactorOp".to_string(),
                        "Term".to_string(),
                    ],
                    action: "Box::new(Expr::Op(arg1, arg2, arg3))".to_string().into(),
                },
                // Term
                GenRule { production: vec!["Term".to_string()], action: "arg1".to_string().into() },
            ],
        },
        // FactorOp: Opcode = {
        //     Token::Star => Opcode::Mul,       // factor_op -> *
        // };
        GenRuleGroup {
            name: "FactorOp".to_string(),
            return_type: "Opcode".to_string(),
            rules: vec![
                // "*" => Opcode::Mul
                GenRule {
                    production: vec!["Token::Star".to_string()],
                    action: "Opcode::Mul".to_string().into(),
                },
            ],
        },
        // Term: Box<Expr> = {
        //     Token::Identifier => Box::new(Expr::Identifier(<>)),   // term -> identifier
        //     Token::LParen Expr Token::RParen => Expr               // term -> ( expr )
        // };
        GenRuleGroup {
            name: "Term".to_string(),
            return_type: "Box<Expr>".to_string(),
            rules: vec![
                GenRule {
                    production: vec!["Num".to_string()],
                    action: "Box::new(Expr::Identifier(arg1.into()))".to_string().into(),
                },
                GenRule {
                    production: vec!["(".to_string(), "Expr".to_string(), ")".to_string()],
                    action: "arg2".to_string().into(),
                },
            ],
        },
    ];

    const PRE_DEFINED: &'static str = r#"
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

// should be generated from grammar
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

// should be generated from grammar
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

// should be generated from grammar
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

"#;

    let usage = r#"

#[test]
fn test_expr() {
    use crate::pda::*;
    use crate::tests::*;
    use crate::nfa_dfa::DFA;
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
}
"#;

    let generator = Generator::new(GenGrammar::new(
        defs.clone(),
        "Token".to_string(),
        vec![],
        Some("SemanticAction".to_string()),
        None,
    ));
    let generated_code = PRE_DEFINED.to_string() + "\n" + &generator.generate().to_string() + usage;
    std::fs::write("src/generated.rs", generated_code).unwrap();
}
