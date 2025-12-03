use logos::{Lexer, Logos};

use crate::generator::{GenGrammar, GenRule, GenRuleGroup, TokenKindDef};

#[derive(Logos, Debug, PartialEq, Clone)]
#[logos(skip r"[ \t\n\f]+")]
#[logos(skip r"//.*")]
pub enum Token {
    #[token("=")]
    Equal,

    #[token("{")]
    LBrace,

    #[token("}")]
    RBrace,

    #[token("(")]
    LParen,

    #[token(")")]
    RParen,

    #[token("..")]
    DoubleDot,

    #[token(",")]
    Comma,

    #[token(";")]
    Semi,

    #[token("::")]
    ColonColon,

    #[token("tokenkind")]
    KwTokenKind,

    #[regex(r#""(?:[^"\\]|\\.)*""#, |lex| {
        let s = lex.slice();
        s[1..s.len()-1].to_string() 
    })]
    StringLiteral(String),

    #[token("extern", extract_extern_block)]
    ExternBlock(String),

    #[token("SemanticAction", extract_semantic_action)]
    SemanticAction(String),

    #[token(":", extract_type_def)]
    TypeDefinition(String),

    #[token("=>", extract_action_code)]
    ArrowWithAction(String),

    #[regex("[a-zA-Z_][a-zA-Z0-9_]*", |lex| lex.slice().to_string())]
    Ident(String),
}

impl Token {
    fn as_extern_block(self) -> Option<String> {
        if let Token::ExternBlock(code) = self { Some(code.clone()) } else { None }
    }

    fn as_semantic_action(self) -> Option<String> {
        if let Token::SemanticAction(action) = self { Some(action.clone()) } else { None }
    }
}

fn extract_balanced(lex: &mut Lexer<Token>, delimiters: &[char]) -> String {
    let remainder = lex.remainder();
    let mut len = 0;

    let mut count_paren = 0; // ()
    let mut count_brack = 0; // []
    let mut count_brace = 0; // {}
    let mut count_angle = 0; // <>

    for c in remainder.chars() {
        if count_paren == 0 && count_brack == 0 && count_brace == 0 && count_angle == 0 {
            if delimiters.contains(&c) {
                break;
            }
        }

        match c {
            '(' => count_paren += 1,
            ')' => {
                if count_paren > 0 {
                    count_paren -= 1
                }
            }
            '[' => count_brack += 1,
            ']' => {
                if count_brack > 0 {
                    count_brack -= 1
                }
            }
            '{' => count_brace += 1,
            '}' => {
                if count_brace > 0 {
                    count_brace -= 1
                }
            }
            '<' => count_angle += 1,
            '>' => {
                if count_angle > 0 {
                    count_angle -= 1
                }
            }
            _ => {}
        }
        len += c.len_utf8();
    }

    lex.bump(len);
    remainder[..len].trim().to_string()
}

fn extract_type_def(lex: &mut Lexer<Token>) -> String {
    extract_balanced(lex, &['='])
}

fn extract_action_code(lex: &mut Lexer<Token>) -> String {
    extract_balanced(lex, &[',', '}'])
}

fn extract_extern_block(lex: &mut Lexer<Token>) -> String {
    let remainder = lex.remainder();
    let start_offset = remainder.find('{').expect("Expected '{' after extern");
    lex.bump(start_offset + 1);
    extract_balanced(lex, &['}'])
}

fn extract_semantic_action(lex: &mut Lexer<Token>) -> String {
    let s = extract_balanced(lex, &[';']);
    assert!(s.starts_with("="));
    s.trim()[1..].trim().to_string()
}

pub struct Parser<'source> {
    lexer: logos::Lexer<'source, Token>,
    peeked: Option<Token>,
}

impl<'source> Parser<'source> {
    pub fn new(source: &'source str) -> Self {
        Self { lexer: Token::lexer(source), peeked: None }
    }

    fn peek(&mut self) -> Option<&Token> {
        if self.peeked.is_none() {
            self.peeked = self.lexer.next().map(|res| res.expect("Lexer error"));
            println!("Peeked token: {:?}", self.peeked);
        }
        self.peeked.as_ref()
    }

    fn advance(&mut self) -> Option<Token> {
        if let Some(token) = self.peeked.take() {
            return Some(token);
        }
        self.lexer.next().map(|res| res.expect("Lexer error"))
    }

    fn expect(&mut self, expected: Token) {
        match self.advance() {
            Some(t) if t == expected => {}
            Some(t) => panic!("Expected {:?}, found {:?}", expected, t),
            None => panic!("Expected {:?}, found EOF", expected),
        }
    }

    pub fn parse_grammar(&mut self) -> GenGrammar {
        let mut rule_groups = Vec::new();
        let mut token_kinds = Vec::new();
        let mut token_ty = String::new();
        let mut semantic_action_type = None;
        let mut extern_code = None;

        while let Some(token) = self.peek() {
            if let Token::Semi = token {
                self.advance();
                continue;
            }

            match token {
                Token::Ident(_) => {
                    rule_groups.push(self.parse_non_terminal());
                }
                Token::ExternBlock(_) => {
                    extern_code = self.advance().unwrap().as_extern_block();
                    self.expect(Token::RBrace);
                    self.expect(Token::Semi);
                }
                Token::SemanticAction(_) => {
                    semantic_action_type = self.advance().unwrap().as_semantic_action();
                    self.expect(Token::Semi);
                }
                Token::KwTokenKind => {
                    (token_ty, token_kinds) = self.parse_token_kinds();
                }
                _ => panic!("Unexpected token at top level: {:?}", token),
            }
        }
        GenGrammar::new(rule_groups, token_ty, token_kinds, semantic_action_type, extern_code)
    }

    // Name : Type = { Rules }
    fn parse_non_terminal(&mut self) -> GenRuleGroup {
        // 1. Name
        let name = match self.advance() {
            Some(Token::Ident(n)) => n,
            t => panic!("Expected NonTerminal Name, found {:?}", t),
        };

        // 2. Type
        let return_type = match self.advance() {
            Some(Token::TypeDefinition(t)) => t,
            t => panic!("Expected Type Definition (: Type =), found {:?}", t),
        };

        // 3. =
        self.expect(Token::Equal);

        // 4. {
        self.expect(Token::LBrace);

        // 5. Rules
        let mut rules = Vec::new();
        while let Some(token) = self.peek() {
            if *token == Token::RBrace {
                break;
            }
            rules.push(self.parse_rule());

            if let Some(Token::Comma) = self.peek() {
                self.advance();
            }
        }

        // 6. }
        self.expect(Token::RBrace);

        GenRuleGroup { name, return_type, rules }
    }

    // Part1 Part2 ... => Action
    fn parse_rule(&mut self) -> GenRule {
        let mut production = Vec::new();

        loop {
            if let Some(Token::ArrowWithAction(_)) = self.peek() {
                break;
            }
            if let Some(Token::RBrace) | Some(Token::Comma) = self.peek() {
                panic!("Expected '=>' in rule definition");
            }

            match self.advance() {
                Some(Token::Ident(s)) => {
                    let mut item = s;
                    if let Some(Token::ColonColon) = self.peek() {
                        self.advance(); // ::
                        item.push_str("::");
                        if let Some(Token::Ident(part2)) = self.advance() {
                            item.push_str(&part2);
                        } else {
                            panic!("Expected Identifier after ::");
                        }
                    }
                    production.push(item);
                }
                t => panic!("Unexpected token in production: {:?}", t),
            }
        }

        let action = match self.advance() {
            Some(Token::ArrowWithAction(code)) => code,
            t => panic!("Expected Action Code (=> ...), found {:?}", t),
        };

        if action.starts_with('`') && action.ends_with('`') {
            let method = action.trim_matches('`').to_string();
            GenRule { production, action: crate::generator::ActionKind::Sema(method) }
        } else {
            GenRule { production, action: crate::generator::ActionKind::Code(action) }
        }
    }

    /// parse section defining token kinds
    /// tokenkind Token {
    ///     Plus = "+",
    ///     Star = "*",
    ///     LParen = "(",
    ///     RParen = ")",
    ///     Identifier(..) = "identifier",
    /// };
    fn parse_token_kinds(&mut self) -> (String, Vec<TokenKindDef>) {
        self.expect(Token::KwTokenKind);

        let token_type = match self.advance() {
            Some(Token::Ident(n)) => n,
            t => panic!("Expected TokenKind Name, found {:?}", t),
        };

        self.expect(Token::LBrace);

        let mut defs = Vec::new();

        while let Some(token) = self.peek() {
            if *token == Token::RBrace {
                break;
            }

            let name = match self.advance() {
                Some(Token::Ident(n)) => n,
                t => panic!("Expected Token Name, found {:?}", t),
            };
            let is_unit = if let Some(Token::LParen) = self.peek() {
                self.advance();
                self.expect(Token::DoubleDot);
                self.expect(Token::RParen);
                false
            } else {
                true
            };

            self.expect(Token::Equal);

            let kind = match self.advance() {
                Some(Token::StringLiteral(s)) => s,
                t => panic!("Expected String Literal, found {:?}", t),
            };

            defs.push(TokenKindDef { name, kind, is_unit });
            
            self.expect(Token::Comma);
        }

        self.expect(Token::RBrace);
        self.expect(Token::Semi);

        (token_type, defs)
    }
}

#[test]
fn test() {
    let input = r#"

        // use rust code
        extern {
            use crate::ast::{Expr, Opcode};
        };

        // unique kind for each token
        tokenkind Token {
            Plus = "+",  // corresponds to Token::Plus
            Star = "*",
            LParen = "(",
            RParen = ")",
            Identifier(..) = "identifier",
        };

        // define SemanticAction
        SemanticAction = SemanticAction;

        Expr: Box<Expr> = {
            Expr ExprOp Factor => `rule1`,
            Factor             => arg1
        };

        ExprOp: Opcode = {
            Token::Plus  => Opcode::Add,
            Token::Minus => Opcode::Sub,
        };

        Factor: Box<Expr> = {
            Factor FactorOp Term => Box::new(Expr::Op(arg1, arg2, arg3)),
            Term                 => arg1,
        };
        
        Term: Box<Expr> = {
            Num => Box::new(Expr::Identifier(arg1.into())),
            Token::LParen Expr Token::RParen => arg2
        };
    "#;

    // let lexer = Token::lexer(input);
    // for token in lexer {
    //     println!("Token: {:?}", token);
    // }

    println!("Starting Parser...");
    let mut parser = Parser::new(input);

    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| parser.parse_grammar()));

    match result {
        Ok(grammar) => {
            println!("imported code:\n{}", grammar.extern_code.unwrap_or_default());
            println!("Semantic Action Type: {:?}", grammar.semantic_action_type);
            println!("Token Type : {}", grammar.token_ty);
            for token_kind in grammar.token_kinds {
                let unit_display = if token_kind.is_unit { "" } else { "(..)" };
                println!("TokenKind: {}{} = {:?}", token_kind.name, unit_display, token_kind.kind);
            }
            
            for def in grammar.rule_groups {
                println!("NonTerminal: {}", def.name);
                println!("  Type: {}", def.return_type);
                println!("  Rules:");
                for rule in def.rules {
                    println!("    {:?} => {}", rule.production, rule.action);
                }
                println!("-------------------------------");
            }
        }
        Err(_) => println!("Parsing Failed."),
    }
}
