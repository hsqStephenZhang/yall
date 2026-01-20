mod parser {
    include!(concat!(env!("OUT_DIR"), "/expr.yapg.rs"));
}

mod ast {
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

    #[derive(Debug, Clone)]
    pub enum Token {
        LParen,
        RParen,
        Plus,
        Star,
        Identifier(String),
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
}

#[test]
fn test_expr_parser() {
    let actioner = ast::SemanticAction {
        context: std::collections::HashMap::from([
            ("a".into(), 1),
            ("b".into(), 2),
            ("c".into(), 3),
            ("d".into(), 4),
        ]),
    };
    let parser = parser::ExprParser::new(actioner);
    let input = "a * ( b * ( c + d ) )";
    let tokens: Vec<ast::Token> = input.split_whitespace().map(|s| ast::Token::from(s)).collect();
    let res = parser.parse(tokens.into_iter().peekable());
    assert_eq!(res.unwrap().into_i32(), 14);
}
