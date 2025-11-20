use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use std::collections::HashMap;
use std::collections::HashSet;

#[derive(Debug, Clone)]
pub struct NonTerminalRules {
    pub name: String,
    pub return_type: String,
    pub rules: Vec<Rule>,
}

#[derive(Debug, Clone)]
pub struct Rule {
    pub id: usize,
    pub production: Vec<String>,
    pub action: String,
}

pub struct Generator {
    symbol_type_map: HashMap<String, String>,
}

impl Generator {
    pub fn new(defs: &[NonTerminalRules]) -> Self {
        let mut symbol_type_map = HashMap::new();

        for nt in defs {
            symbol_type_map.insert(nt.name.clone(), nt.return_type.clone());
        }

        Self { symbol_type_map }
    }

    pub fn generate(&self, defs: &[NonTerminalRules]) -> TokenStream {
        let value_enum = self.gen_value_enum();
        let action_fns = self.gen_action_fns(defs);
        let table = self.gen_table(defs);

        quote! {
            #value_enum
            #action_fns
            #table
        }
    }

    fn gen_value_enum(&self) -> TokenStream {
        let mut variants = Vec::new();
        let mut methods = Vec::new();

        let mut seen_variants = HashSet::new();

        let mut gen_variant = |variant_name_str: String, rust_type_str: &str| {
            if seen_variants.contains(&variant_name_str) {
                return;
            }
            seen_variants.insert(variant_name_str.clone());

            let variant_ident = format_ident!("{}", variant_name_str);
            let rust_type: syn::Type = syn::parse_str(rust_type_str).unwrap();

            variants.push(quote! {
                #variant_ident(#rust_type)
            });

            let method_name = format_ident!("into_{}", variant_name_str.to_lowercase());
            let error_msg = format!("expected {} node", variant_name_str);

            methods.push(quote! {
                pub fn #method_name(self) -> #rust_type {
                    match self {
                        Value::#variant_ident(v) => v,
                        _ => panic!(#error_msg),
                    }
                }
            });
        };

        for (variant_name_str, rust_type_str) in &self.symbol_type_map {
            gen_variant(variant_name_str.clone(), rust_type_str.as_str());
        }
        gen_variant("Token".into(), "Token");

        quote! {
            #[derive(Debug)]
            pub enum Value {
                #(#variants),*
            }

            impl Value {
                #(#methods)*
            }
        }
    }

    fn gen_action_fns(&self, defs: &[NonTerminalRules]) -> TokenStream {
        let mut funcs = Vec::new();

        for nt in defs {
            // let result_variant_str = self.type_variant_map.get(&nt.return_type).unwrap();
            // let result_variant = format_ident!("{}", result_variant_str);
            let result_variant = format_ident!("{}", nt.name);

            for rule in &nt.rules {
                let fn_name = format_ident!("rule_{}", rule.id);

                let mut pops = Vec::new();

                // Expr -> Expr(1) Op(2) Factor(3)
                // stack: [..., arg1, arg2, arg3]

                for (i, symbol) in rule.production.iter().enumerate().rev() {
                    let arg_name = format_ident!("arg{}", i + 1); // arg1, arg2...

                    let target_variant = if self.symbol_type_map.contains_key(symbol) {
                        &symbol
                    } else {
                        "Token"
                    };
                    let conversion_method = format_ident!("into_{}", target_variant.to_lowercase());

                    pops.push(quote! {
                        let #arg_name = stack.pop().unwrap().#conversion_method();
                    });
                }

                let user_action: TokenStream =
                    syn::parse_str(&rule.action).expect("Invalid action code");

                funcs.push(quote! {
                    pub fn #fn_name(stack: &mut Vec<Value>) -> Value {
                        #(#pops)*
                        let result = { #user_action };
                        Value::#result_variant(result)
                    }
                });
            }
        }

        quote! {
            #(#funcs)*
        }
    }

    fn gen_table(&self, defs: &[NonTerminalRules]) -> TokenStream {
        let mut rows = Vec::new();

        for nt in defs {
            for rule in &nt.rules {
                let id = rule.id;
                let fn_name = format_ident!("rule_{}", id);
                rows.push(quote! {
                    #fn_name
                });
            }
        }

        quote! {
            type ActionFn = fn(&mut Vec<Value>) -> Value;
            const RULE_TABLE: &[ActionFn] = &[
                #(#rows),*
            ];
        }
    }
}

/// generation strategy:
/// 1. collect all non-terminals and their return types
/// 2. create a `enum Value` that can represent all possible return types and str token
/// 3. for each rule, generate a function that pops arguments from a stack and pushes the result
/// 4. create a table that maps rule id to action function

#[allow(warnings)]
mod playground {
    /**
     *
     * copied from lalrpop grammar example
    *
    pub Expr: Box<Expr> = { // (1)
       Expr ExprOp Factor => Box::new(Expr::Op(<>)), // (2)
       Factor,
    };

    ExprOp: Opcode = { // (3)
        Token::Plus => Opcode::Add,
        Token::Minus => Opcode::Sub,
    };

    Factor: Box<Expr> = {
        Factor FactorOp Term => Box::new(Expr::Op(<>)),
        Term,
    };

    FactorOp: Opcode = {
        Token::Star => Opcode::Mul,
        Token::Device => Opcode::Div,
    };

    Term: Box<Expr> = {
        Id => Box::new(Expr::Identifier(<>)), // (4)
        Token::LParen Expr Token::RParen => Expr
    };

    Id: Identifier = {
        Token::Identifier(s) => Identifier(s)
    };

    */

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

    #[derive(Debug, PartialEq, Eq)]
    enum Token {
        LParen,
        RParen,
        Plus,
        Minus,
        Star,
        Devide,
        Identifier(String),
    }

    /// the following code should be generated from the grammar
    #[derive(Debug)]
    pub enum Value {
        Expr(Box<Expr>),
        ExprOp(Opcode),
        Factor(Box<Expr>),
        FactorOp(Opcode),
        Term(Box<Expr>),
        Identifier(Identifier),
        Token(Token),
    }

    trait NamedToken {
        fn name(&self) -> &str;
    }

    impl NamedToken for Token {
        fn name(&self) -> &str {
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

    impl Value {
        pub fn into_expr(self) -> Box<Expr> {
            match self {
                Value::Expr(e) => e,
                _ => panic!("expected Expr node"),
            }
        }

        pub fn into_expr_op(self) -> Opcode {
            match self {
                Value::ExprOp(op) => op,
                _ => panic!("expected ExprOp node"),
            }
        }

        pub fn into_factor(self) -> Box<Expr> {
            match self {
                Value::Factor(e) => e,
                _ => panic!("expected Factor node"),
            }
        }

        pub fn into_factor_op(self) -> Opcode {
            match self {
                Value::FactorOp(op) => op,
                _ => panic!("expected FactorOp node"),
            }
        }

        pub fn into_term(self) -> Box<Expr> {
            match self {
                Value::Term(e) => e,
                _ => panic!("expected Term node"),
            }
        }

        pub fn into_identifier(self) -> Identifier {
            match self {
                Value::Identifier(n) => n,
                _ => panic!("expected I32 node"),
            }
        }

        pub fn into_token(self) -> Token {
            match self {
                Value::Token(s) => s,
                _ => panic!("expected Token node"),
            }
        }
    }

    type ActionFn = fn(&mut Vec<Value>) -> Value;

    // pub Expr: Box<Expr> = {
    //    Expr ExprOp Factor => Box::new(Expr::Op(<>)),
    //    Factor,
    // };

    pub fn expr_rule1(stack: &mut Vec<Value>) -> Value {
        let arg3 = stack.pop().unwrap().into_expr();
        let arg2 = stack.pop().unwrap().into_expr_op();
        let arg1 = stack.pop().unwrap().into_expr();
        Value::Expr(Box::new(Expr::Op(arg1, arg2, arg3)))
    }

    pub fn expr_rule2(stack: &mut Vec<Value>) -> Value {
        let arg1 = stack.pop().unwrap().into_factor();
        Value::Expr(arg1)
    }

    // ExprOp: Opcode = {
    //     Token::Plus => Opcode::Add,
    //     Token::Sub => Opcode::Sub,
    // };

    pub fn expr_op_rule1(stack: &mut Vec<Value>) -> Value {
        let arg1 = stack.pop().unwrap().into_token();
        assert_eq!(arg1, Token::Plus);
        let op = Opcode::Add;
        Value::ExprOp(op)
    }

    pub fn expr_op_rule2(stack: &mut Vec<Value>) -> Value {
        let arg1 = stack.pop().unwrap().into_token();
        assert_eq!(arg1, Token::Minus);
        let op = Opcode::Sub;
        Value::ExprOp(op)
    }

    // Factor: Box<Expr> = {
    //     Factor FactorOp Term => Box::new(Expr::Op(<>)),
    //     Term,
    // };

    pub fn factor_rule1(stack: &mut Vec<Value>) -> Value {
        let arg3 = stack.pop().unwrap().into_term();
        let arg2 = stack.pop().unwrap().into_factor_op();
        let arg1 = stack.pop().unwrap().into_factor();
        Value::Expr(Box::new(Expr::Op(arg1, arg2, arg3)))
    }

    pub fn factor_rule2(stack: &mut Vec<Value>) -> Value {
        let arg1 = stack.pop().unwrap().into_term();
        Value::Expr(arg1)
    }

    // FactorOp: Opcode = {
    //     Token::Star => Opcode::Mul,
    //     Token::Devide => Opcode::Div,
    // };

    pub fn factor_op_rule1(stack: &mut Vec<Value>) -> Value {
        let arg1 = stack.pop().unwrap().into_token();
        debug_assert_eq!(arg1, Token::Star);
        let op = Opcode::Mul;
        Value::FactorOp(op)
    }

    pub fn factor_op_rule2(stack: &mut Vec<Value>) -> Value {
        let arg1 = stack.pop().unwrap().into_token();
        debug_assert_eq!(arg1, Token::Devide);
        let op = Opcode::Div;
        Value::FactorOp(op)
    }

    // Term: Box<Expr> = {
    //     Num => Box::new(Expr::Number(<>)),
    //     "(" Expr ")" => <>
    // };

    pub fn term_rule1(stack: &mut Vec<Value>) -> Value {
        let arg1 = stack.pop().unwrap().into_identifier();
        Value::Expr(Box::new(Expr::Identifier(arg1)))
    }

    pub fn term_rule2(stack: &mut Vec<Value>) -> Value {
        let arg3 = stack.pop().unwrap().into_token();
        debug_assert_eq!(arg3, Token::LParen);
        let arg2 = stack.pop().unwrap().into_expr();
        let arg1 = stack.pop().unwrap().into_token();
        debug_assert_eq!(arg1, Token::RParen);
        Value::Expr(arg2)
    }

    // Id: Identifier = {
    //     Token::Identifier(something) => Identifier(something)
    // };
    pub fn identifier_rule1(stack: &mut Vec<Value>) -> Value {
        use std::str::FromStr;
        let arg1 = stack.pop().unwrap().into_token();
        let Token::Identifier(something) = arg1 else {
            panic!()
        };
        Value::Identifier(Identifier(something))
    }

    // we could make it a match statement for better performance(by avoiding table lookup)
    const tbl: &[(usize, ActionFn)] = &[
        (1, expr_rule1),
        (2, expr_rule2),
        (3, expr_op_rule1),
        (4, expr_op_rule2),
        (5, factor_rule1),
        (6, factor_rule2),
        (7, factor_op_rule1),
        (8, factor_op_rule2),
        (9, term_rule1),
        (10, term_rule2),
        (11, identifier_rule1),
    ];
}
