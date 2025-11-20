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
                    id: 1,
                    production: vec![
                        "Expr".to_string(),
                        "ExprOp".to_string(),
                        "Factor".to_string(),
                    ],
                    action: "Box::new(Expr::Op(arg1, arg2, arg3))".to_string(),
                },
                // Rule 2: Factor
                Rule {
                    id: 2,
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
                // Rule 3: "+" => Opcode::Add
                Rule {
                    id: 3,
                    production: vec!["Token::Plus".to_string()],
                    action: "Opcode::Add".to_string(),
                },
                // Rule 4: "-" => Opcode::Sub
                Rule {
                    id: 4,
                    production: vec!["Token::Minus".to_string()],
                    action: "Opcode::Sub".to_string(),
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
                // Rule 5: Factor FactorOp Term => Box::new(Expr::Op(<>))
                Rule {
                    id: 5,
                    production: vec![
                        "Factor".to_string(),
                        "FactorOp".to_string(),
                        "Term".to_string(),
                    ],
                    action: "Box::new(Expr::Op(arg1, arg2, arg3))".to_string(),
                },
                // Rule 6: Term
                Rule {
                    id: 6,
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
                // Rule 7: "*" => Opcode::Mul
                Rule {
                    id: 7,
                    production: vec!["Token::Star".to_string()],
                    action: "Opcode::Mul".to_string(),
                },
                // Rule 8: "/" => Opcode::Div
                Rule {
                    id: 8,
                    production: vec!["Token::Devide".to_string()],
                    action: "Opcode::Div".to_string(),
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
                    id: 9,
                    production: vec!["Num".to_string()],
                    action: "Box::new(Expr::Identifier(arg1.into()))".to_string(),
                },
                Rule {
                    id: 10,
                    production: vec!["(".to_string(), "Expr".to_string(), ")".to_string()],
                    action: "arg2".to_string(),
                },
            ],
        },
    ];

    const PRE_DEFINED: &'static str = r#"
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
