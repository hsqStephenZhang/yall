use crate::generator::*;

#[test]
fn t1() {
    let defs = vec![
        //  pub Expr: Box<Expr> = {
        //     Expr ExprOp Factor => Box::new(Expr::Op(<>)), // expr -> expr + factor, expr -> expr - factor
        //     Factor                                        // expr -> factor
        //  };
        NonTerminalRules {
            name: "Expr".to_string(),
            return_type: "Box<Expr>".to_string(),
            rules: vec![
                // Rule 1: Expr ExprOp Factor => Box::new(Expr::Op(<>))
                Rule {
                    production: vec![
                        "Expr".to_string(),
                        "ExprOp".to_string(),
                        "Factor".to_string(),
                    ],
                    action: "Box::new(Expr::Op(arg1, arg2, arg3))".to_string(),
                },
                // Rule 2: Factor
                Rule {
                    production: vec!["Factor".to_string()],
                    action: "arg1".to_string(),
                },
            ],
        },
        // ExprOp: Opcode = {
        //     Token::Plus => Opcode::Add,      // expr_op -> +
        //     Token::Minus => Opcode::Sub,     // expr_op -> -
        // };
        NonTerminalRules {
            name: "ExprOp".to_string(),
            return_type: "Opcode".to_string(),
            rules: vec![
                // "+" => Opcode::Add
                Rule {
                    production: vec!["Token::Plus".to_string()],
                    action: "Opcode::Add".to_string(),
                },
            ],
        },
        // Factor: Box<Expr> = {
        //     Factor FactorOp Term => Box::new(Expr::Op(<>)),  // factor -> factor * term, factor -> factor / term
        //     Term,                                            // factor -> term
        // };
        NonTerminalRules {
            name: "Factor".to_string(),
            return_type: "Box<Expr>".to_string(),
            rules: vec![
                // Factor FactorOp Term => Box::new(Expr::Op(<>))
                Rule {
                    production: vec![
                        "Factor".to_string(),
                        "FactorOp".to_string(),
                        "Term".to_string(),
                    ],
                    action: "Box::new(Expr::Op(arg1, arg2, arg3))".to_string(),
                },
                // Term
                Rule {
                    production: vec!["Term".to_string()],
                    action: "arg1".to_string(),
                },
            ],
        },
        // FactorOp: Opcode = {
        //     Token::Star => Opcode::Mul,       // factor_op -> *
        //     Token::Device => Opcode::Div,     // factor_op -> /
        // };
        NonTerminalRules {
            name: "FactorOp".to_string(),
            return_type: "Opcode".to_string(),
            rules: vec![
                // "*" => Opcode::Mul
                Rule {
                    production: vec!["Token::Star".to_string()],
                    action: "Opcode::Mul".to_string(),
                },
            ],
        },
        // Term: Box<Expr> = {
        //     Token::Identifier => Box::new(Expr::Identifier(<>)),   // term -> identifier
        //     Token::LParen Expr Token::RParen => Expr               // term -> ( expr )
        // };
        NonTerminalRules {
            name: "Term".to_string(),
            return_type: "Box<Expr>".to_string(),
            rules: vec![
                Rule {
                    production: vec!["Num".to_string()],
                    action: "Box::new(Expr::Identifier(arg1.into()))".to_string(),
                },
                Rule {
                    production: vec!["(".to_string(), "Expr".to_string(), ")".to_string()],
                    action: "arg2".to_string(),
                },
            ],
        },
    ];

    const PRE_DEFINED: &'static str = r#"
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
pub struct Identifier(String);

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
impl<'a> From<&'a str> for Token {
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

"#;

    let generator = Generator::new(&defs);
    let generated_code = PRE_DEFINED.to_string() + "\n" + &generator.generate(&defs).to_string();
    std::fs::write("src/generated.rs", generated_code).unwrap();
}
