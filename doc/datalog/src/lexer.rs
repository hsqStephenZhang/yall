use logos::Logos;

#[derive(Logos, Debug, Clone, PartialEq)]
#[logos(skip r"[ \t\n\r]+")]
#[logos(skip r"#[^\n\r]*")]
pub enum Token {
    // Operators and punctuation
    #[token(".")]
    Dot,

    #[token("~")]
    Tilde,

    #[token("?")]
    Question,

    #[token(":-")]
    ColonDash,

    #[token(",")]
    Comma,

    #[token("(")]
    LParen,

    #[token(")")]
    RParen,

    #[token("=")]
    Eq,

    #[token("!=")]
    NotEq,

    // Keywords
    #[token("true")]
    True,

    #[token("false")]
    False,

    // Literals
    #[regex(r"[A-Z][a-zA-Z_]*", |lex| lex.slice().to_string())]
    Variable(String),

    #[regex(r"[a-z][a-zA-Z0-9_-]*", |lex| lex.slice().to_string())]
    Identifier(String),

    #[regex(r#""[^"]*""#, |lex| {
        let s = lex.slice();
        s[1..s.len()-1].to_string()
    })]
    String(String),

    #[regex(r"[0-9]+", |lex| lex.slice().parse().ok())]
    Integer(i64),
}

impl Token {
    pub fn into_variable(self) -> String {
        match self {
            Token::Variable(s) => s,
            _ => panic!("Expected Variable token"),
        }
    }

    pub fn into_identifier(self) -> String {
        match self {
            Token::Identifier(s) => s,
            _ => panic!("Expected Identifier token"),
        }
    }

    pub fn into_string(self) -> String {
        match self {
            Token::String(s) => s,
            _ => panic!("Expected String token"),
        }
    }

    pub fn into_integer(self) -> i64 {
        match self {
            Token::Integer(i) => i,
            _ => panic!("Expected Integer token"),
        }
    }
}
