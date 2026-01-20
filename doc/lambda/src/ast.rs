use logos::Logos;

#[derive(Logos, Debug, Clone, PartialEq)]
#[logos(skip r"[ \t\n\f]+")]
pub enum Token {
    #[token("λ")]
    Lambda,

    #[token("\\")]
    Backslash,

    #[token(":")]
    Colon,

    #[token(".")]
    Dot,

    #[token("(")]
    LParen,

    #[token(")")]
    RParen,

    #[regex(r"[a-zA-Z0-9_-]+", |lex| lex.slice().to_string())]
    Id(String),
}

impl Token {
    pub fn into_id(self) -> String {
        match self {
            Token::Id(s) => s,
            _ => panic!("Expected Id token"),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Variable(pub String, pub Option<String>);

#[derive(Debug, Clone, PartialEq)]
pub enum Expression {
    Var(Variable),
    Abs(Box<Expression>),
    App(Box<Expression>, Box<Expression>),
}

impl Expression {
    /// Build nested abstractions from a list of variables and an optional body
    pub fn build_abs(lambda_count: usize, vars: Vec<Variable>, body: Option<Expression>) -> Expression {
        let mut expr = body.unwrap_or_else(|| {
            // If no body is provided, create a variable expression from the last variable
            // or a placeholder
            if let Some(last_var) = vars.last() {
                Expression::Var(last_var.clone())
            } else {
                // Empty abstraction, use a placeholder variable
                Expression::Var(Variable("_".to_string(), None))
            }
        });

        // Build abstractions from right to left
        for _ in vars.iter().rev() {
            expr = Expression::Abs(Box::new(expr));
        }

        // Add additional lambda layers if lambda_count > vars.len()
        let additional_lambdas = lambda_count.saturating_sub(vars.len());
        for _ in 0..additional_lambdas {
            expr = Expression::Abs(Box::new(expr));
        }

        expr
    }
}

#[macro_export]
macro_rules! app {
    ($e1:expr, $e2:expr) => {
        Expression::App(Box::new($e1), Box::new($e2))
    };
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_lambda_tokens() {
        let input = "λ x . x";
        let mut lex = Token::lexer(input);
        
        assert_eq!(lex.next(), Some(Ok(Token::Lambda)));
        assert_eq!(lex.next(), Some(Ok(Token::Id("x".to_string()))));
        assert_eq!(lex.next(), Some(Ok(Token::Dot)));
        assert_eq!(lex.next(), Some(Ok(Token::Id("x".to_string()))));
        assert_eq!(lex.next(), None);
    }

    #[test]
    fn test_application() {
        let input = "(f x)";
        let mut lex = Token::lexer(input);
        
        assert_eq!(lex.next(), Some(Ok(Token::LParen)));
        assert_eq!(lex.next(), Some(Ok(Token::Id("f".to_string()))));
        assert_eq!(lex.next(), Some(Ok(Token::Id("x".to_string()))));
        assert_eq!(lex.next(), Some(Ok(Token::RParen)));
        assert_eq!(lex.next(), None);
    }

    #[test]
    fn test_typed_variable() {
        let input = "x:Int";
        let mut lex = Token::lexer(input);
        
        assert_eq!(lex.next(), Some(Ok(Token::Id("x".to_string()))));
        assert_eq!(lex.next(), Some(Ok(Token::Colon)));
        assert_eq!(lex.next(), Some(Ok(Token::Id("Int".to_string()))));
        assert_eq!(lex.next(), None);
    }

    #[test]
    fn test_backslash_lambda() {
        let input = "\\ x . x";
        let mut lex = Token::lexer(input);
        
        assert_eq!(lex.next(), Some(Ok(Token::Backslash)));
        assert_eq!(lex.next(), Some(Ok(Token::Id("x".to_string()))));
        assert_eq!(lex.next(), Some(Ok(Token::Dot)));
        assert_eq!(lex.next(), Some(Ok(Token::Id("x".to_string()))));
        assert_eq!(lex.next(), None);
    }
}