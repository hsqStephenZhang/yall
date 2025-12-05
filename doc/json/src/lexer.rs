// tokenkind Token {
//     LBrace = "{",
//     RBrace = "}",
//     LBracket = "[",
//     RBracket = "]",
//     Colon = ":",
//     Comma = ",",
//     StringLit(String) = "string",
//     Number(f64) = "number",
//     True = "true",
//     False = "false",
//     Null = "null",
// };
#[derive(Debug, Clone)]
pub(crate) enum Token {
    LBrace,
    RBrace,
    LBracket,
    RBracket,
    Colon,
    Comma,
    StringLit(String),
    Number(String),
    True,
    False,
    Null,
}

impl Token {
    pub fn into_stringlit(self) -> String {
        match self {
            Token::StringLit(s) => s,
            _ => panic!("expected StringLit token"),
        }
    }

    pub fn into_number(self) -> String {
        match self {
            Token::Number(s) => s,
            _ => panic!("expected Number token"),
        }
    }
}

impl From<&str> for Token {
    fn from(s: &str) -> Self {
        match s {
            "{" => Token::LBrace,
            "}" => Token::RBrace,
            "[" => Token::LBracket,
            "]" => Token::RBracket,
            ":" => Token::Colon,
            "," => Token::Comma,
            "true" => Token::True,
            "false" => Token::False,
            "null" => Token::Null,
            _ if s.starts_with('"') && s.ends_with('"') => {
                Token::StringLit(s[1..s.len() - 1].to_string())
            }
            _ => Token::Number(s.to_string()),
        }
    }
}