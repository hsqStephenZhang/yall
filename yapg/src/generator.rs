use std::cell::OnceCell;
use std::collections::{HashMap, HashSet};

use proc_macro2::TokenStream;
use quote::{format_ident, quote};

use crate::grammar_parser::Parser;

/// a group of rules for a non-terminal
/// like
/// ```yall grammar
/// pub Expr: Box<Expr> = {
///     Expr -> Expr ExprOp Factor { ... }
///     Factor
/// };
/// ```
#[derive(Debug, Clone)]
pub struct GenRuleGroup {
    pub name: String,
    pub return_type: String,
    pub rules: Vec<GenRule>,
}

#[derive(Debug, Clone)]
pub enum ActionKind {
    Code(String),
    Sema(String),
}

impl From<String> for ActionKind {
    fn from(action: String) -> Self {
        ActionKind::Code(action)
    }
}

impl std::fmt::Display for ActionKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ActionKind::Code(code) => write!(f, "{}", code),
            ActionKind::Sema(method) => write!(f, "`{}`", method),
        }
    }
}

#[derive(Debug, Clone)]
pub struct GenRule {
    pub production: Vec<String>,
    pub action: ActionKind,
}

#[derive(Debug, Clone)]
pub struct TokenKindDef {
    pub name: String,
    pub kind: String,
    // default is true
    pub is_unit: bool,
}

#[derive(Debug, Clone)]
pub struct GenGrammar {
    pub rule_groups: Vec<GenRuleGroup>,
    pub token_ty: String,
    pub token_kinds: Vec<TokenKindDef>,
    pub semantic_action_type: Option<String>,
    pub extern_code: Option<String>,

    non_terminals: OnceCell<HashSet<String>>,
}

impl GenGrammar {
    pub fn new(
        rule_groups: Vec<GenRuleGroup>,
        token_ty: String,
        token_kinds: Vec<TokenKindDef>,
        semantic_action_type: Option<String>,
        extern_code: Option<String>,
    ) -> Self {
        Self {
            rule_groups,
            token_ty,
            token_kinds,
            semantic_action_type,
            extern_code,
            non_terminals: OnceCell::new(),
        }
    }

    // verify the integrity of the grammar
    pub fn verify(&self) -> bool {
        if self.semantic_action_type.is_none() {
            for group in &self.rule_groups {
                for rule in &group.rules {
                    if let ActionKind::Sema(_) = rule.action {
                        return false;
                    }
                }
            }
        }
        true
    }

    pub fn non_terminals(&self) -> &HashSet<String> {
        self.non_terminals.get_or_init(|| {
            let mut nts = HashSet::new();
            for group in &self.rule_groups {
                nts.insert(group.name.clone());
            }
            nts
        })
    }

    pub fn to_grammar(&self) -> crate::grammar::Grammar<crate::grammar::Terminal> {
        let start_sym = self.rule_groups[0].name.clone();
        let pseduo_start_sym = format!("{}'", &start_sym);
        let mut rules: Vec<crate::grammar::Rule<crate::grammar::Terminal>> =
            Vec::with_capacity(self.rule_groups.iter().map(|g| g.rules.len()).sum::<usize>() + 1);
        rules.push(crate::grammar::Rule {
            left: pseduo_start_sym.clone().into(),
            right: vec![crate::grammar::Symbol::NonTerm(start_sym.clone().into())],
        });

        assert!(
            !self.rule_groups.iter().any(|g| g.name == pseduo_start_sym),
            "The grammar contains a non-terminal named {}, which conflicts with the pseudo start symbol",
            pseduo_start_sym
        );
        let non_terminals = self.non_terminals();
        let token_variant_to_kind = self
            .token_kinds
            .iter()
            .map(|tk| (tk.name.clone(), tk.kind.clone()))
            .collect::<HashMap<_, _>>();
        rules.extend(self.rule_groups.iter().flat_map(|group| {
            group.rules.iter().map(|rule| crate::grammar::Rule {
                left: group.name.clone().into(),
                right: rule
                    .production
                    .iter()
                    .map(|s| {
                        if non_terminals.contains(s) {
                            crate::grammar::Symbol::NonTerm(s.into())
                        } else {
                            assert!(
                                s.starts_with(self.token_ty.as_str()),
                                "The grammar uses token kind '{}' which is not defined",
                                s
                            );
                            let s = s.trim_start_matches(self.token_ty.as_str());
                            let s = s.trim_start_matches("::");
                            assert!(
                                token_variant_to_kind.contains_key(s),
                                "The grammar uses token kind '{}' which is not defined",
                                s
                            );
                            crate::grammar::Symbol::Term(crate::grammar::Terminal(
                                token_variant_to_kind.get(s).unwrap().clone(),
                            ))
                        }
                    })
                    .collect::<Vec<_>>(),
            })
        }));
        crate::grammar::Grammar::new(pseduo_start_sym.into(), start_sym.into(), rules)
    }
}

/// generation strategy:
/// 1. collect all non-terminals and their return types
/// 2. create a `enum Value` that can represent all possible return types and str token
/// 3. for each rule, generate a function that pops arguments from a stack and pushes the result
/// 4. create a table that maps rule id to action function
pub struct Generator {
    grammar: GenGrammar,
    symbol_type_map: HashMap<String, String>,
}

impl Generator {
    pub fn new(grammar: GenGrammar) -> Self {
        assert!(
            grammar.verify(),
            "Grammar uses semantic actions but no SemanticAction type is defined"
        );
        let mut symbol_type_map = HashMap::new();
        for def in &grammar.rule_groups {
            symbol_type_map.insert(def.name.clone(), def.return_type.clone());
        }
        Self { grammar, symbol_type_map }
    }

    pub fn generate(self) -> TokenStream {
        let extern_code = self.grammar.extern_code.as_ref().map(String::as_str).unwrap_or("");
        let extern_code: syn::File = syn::parse_str(extern_code).expect("Invalid extern code");
        let token_terminal_kind_impl = self.gen_terminal_kind_impl();
        let value_enum = self.gen_value_enum();
        let action_fns = self.gen_action_fns();
        let action_table = self.gen_table();
        let parser = self.gen_parser();

        let grammar = self.grammar.to_grammar();
        let dfa = crate::nfa_dfa::DFA::build(&grammar);
        let tables = dfa.generate_rust_code(&grammar);

        quote! {
            #[allow(warnings)]
            #[allow(unused)]
            #extern_code
            #token_terminal_kind_impl
            #value_enum
            #action_fns
            #action_table
            #tables
            #parser
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
                fn #method_name(self) -> #rust_type {
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
            enum Value {
                #(#variants),*
            }

            impl Value {
                #(#methods)*
            }
        }
    }

    /// ```ignore
    // for rule "Expr -> Expr ExprOp Factor", we should generate:
    // ```rust
    /// fn rule_1_action(action: &mut SemanticAction, stack: &mut Vec<Value>) -> Value {
    ///     let arg3 = stack.pop().unwrap().into_factor();
    ///     let arg2 = stack.pop().unwrap().into_exprop();
    ///     let arg1 = stack.pop().unwrap().into_expr();
    ///     let args = (arg1, arg2, arg3);
    ///     let result = SemanticAction::rule1(action, args);
    ///     Value::Expr(result)
    /// }
    /// ```
    fn gen_action_fns(&self) -> TokenStream {
        let defs = &self.grammar.rule_groups;
        let mut funcs = Vec::new();

        let fn0_name = format_ident!("rule_{}", 0usize);
        funcs.push(quote! {
            #[allow(unused)]
            #[allow(clippy::ptr_arg)]
            fn #fn0_name(action: &mut SemanticAction, stack: &mut Vec<Value>) -> Value {
                unreachable!("rule 0's action should never be called")
            }
        });
        let mut rule_id = 1;

        for nt in defs {
            // let result_variant_str = self.type_variant_map.get(&nt.return_type).unwrap();
            // let result_variant = format_ident!("{}", result_variant_str);
            let result_variant = format_ident!("{}", nt.name);

            for rule in &nt.rules {
                let fn_name = format_ident!("rule_{}", rule_id as usize);
                rule_id += 1;

                let mut pops = Vec::new();

                // Expr -> Expr(1) Op(2) Factor(3)
                // stack: [..., arg1, arg2, arg3]

                for (i, symbol) in rule.production.iter().enumerate().rev() {
                    let arg_name = format_ident!("arg{}", i + 1); // arg1, arg2...

                    let target_variant =
                        if self.symbol_type_map.contains_key(symbol) { symbol } else { "Token" };
                    let conversion_method = format_ident!("into_{}", target_variant.to_lowercase());

                    pops.push(quote! {
                        let #arg_name = stack.pop().unwrap().#conversion_method();
                    });
                }

                match &rule.action {
                    ActionKind::Code(code) => {
                        let user_action: TokenStream =
                            syn::parse_str(&code).expect("Invalid action code");
                        funcs.push(quote! {
                            #[allow(unused)]
                            fn #fn_name(action: &mut SemanticAction, stack: &mut Vec<Value>) -> Value {
                                #(#pops)*
                                let result = { #user_action };
                                Value::#result_variant(result)
                            }
                        });
                    }
                    ActionKind::Sema(method) => {
                        let arg_idents: Vec<proc_macro2::Ident> = (1..=rule.production.len())
                            .map(|i| format_ident!("arg{}", i))
                            .collect();
                        let args = if arg_idents.len() == 1 {
                            let only_arg = &arg_idents[0];
                            quote! { #only_arg }
                        } else {
                            quote! { ( #(#arg_idents),* ) }
                        };
                        let method = format_ident!("{}", method);

                        funcs.push(quote! {
                            #[allow(unused)]
                            fn #fn_name(action: &mut SemanticAction, stack: &mut Vec<Value>) -> Value {
                                #(#pops)*
                                let args = #args;
                                let result = SemanticAction::#method(action, args);
                                Value::#result_variant(result)
                            }
                        });
                    }
                }
            }
        }

        quote! {
            #(#funcs)*
        }
    }

    fn gen_table(&self) -> TokenStream {
        let defs = &self.grammar.rule_groups;
        let mut rows = Vec::new();
        let fn_name = format_ident!("rule_{}", 0usize);
        rows.push(quote! {
            #fn_name
        });
        let mut rule_id = 1;

        for nt in defs {
            for _ in &nt.rules {
                let id = rule_id;
                let fn_name = format_ident!("rule_{}", id as usize);
                rule_id += 1;
                rows.push(quote! {
                    #fn_name
                });
            }
        }

        quote! {
            type ActionFn = fn(&mut SemanticAction, &mut Vec<Value>) -> Value;
            const RULE_TABLE: &[ActionFn] = &[
                #(#rows),*
            ];
        }
    }

    fn gen_parser(&self) -> TokenStream {
        let parser_name = format_ident!("{}Parser", "Expr");
        let sema_ty = match self.grammar.semantic_action_type.as_ref() {
            None => "()",
            Some(ty) => ty.as_str(),
        };
        let sema_ty: syn::Type =
            syn::parse_str(sema_ty).expect(&format!("Invalid SemanticAction type {}", sema_ty));

        let parser = quote! {
            pub struct #parser_name<Actioner> {
                actioner: Actioner,
            }

            impl #parser_name<#sema_ty> {
                pub fn new(actioner: #sema_ty) -> Self {
                    Self { actioner }
                }

                pub fn parse<I: Iterator<Item = Token>>(
                    self,
                    token_stream: std::iter::Peekable<I>,
                ) -> Option<Box<Expr>> {
                    let actions = RULE_TABLE;
                    let ctx = yapg::parser::ParseContext {
                        start_state: START_STATE,
                        end_state: END_STATE,
                        is_final_state: __is_final_state,
                        transitions: __transitions,
                        reduce_rule: REDUCE_RULE,
                        rules: RULES,
                        lookahead: __lookahead,
                    };
                    let mut pda: yapg::parser::PdaImpl<'_, Value, #sema_ty> =
                        yapg::parser::PdaImpl::new(START_STATE, self.actioner, actions);
                    if pda.process(token_stream, &ctx) { Some(pda.final_value().into_expr()) } else { None }
                }
            }
        };

        parser
    }

    /// generate TerminalKind impl for the token enum
    /// ```ignore
    /// impl TerminalKind for Token {
    ///     fn id(&self) -> &str {
    ///         match self {
    ///             Token::LParen => "(",
    ///             Token::RParen => ")",
    ///             Token::Plus => "+",
    ///             Token::Star => "*",
    ///             Token::Identifier(..) => "identifier",
    ///         }
    ///     }
    /// }
    /// ```
    fn gen_terminal_kind_impl(&self) -> TokenStream {
        let token_ty: syn::Type = syn::parse_str(self.grammar.token_ty.as_str()).unwrap();
        let items = self.grammar.token_kinds.iter().map(|tk| {
            let variant = format_ident!("{}", tk.name);
            let suffix = if tk.is_unit {
                quote! {}
            } else {
                quote! { (..) }
            };
            let kind = tk.kind.as_str();
            quote! {
                #token_ty::#variant #suffix => #kind,
            }
        });
        quote! {
            impl yapg::grammar::TerminalKind for #token_ty {
                fn id(&self) -> &str {
                    match self {
                        #(#items)*
                    }
                }
            }

            impl From<#token_ty> for Value {
                fn from(token: Token) -> Self {
                    Value::Token(token)
                }
            }
        }
    }
}

pub struct Configuration {
    grammar_files: Vec<String>,
}

impl Configuration {
    pub fn new() -> Self {
        Self { grammar_files: Vec::new() }
    }

    pub fn add_grammar_file(mut self, path: impl Into<String>) -> Self {
        self.grammar_files.push(path.into());
        self
    }

    pub fn build(self) -> std::io::Result<()> {
        let out_path = std::env::var("OUT_DIR").expect("OUT_DIR not set");
        let out_path = std::path::Path::new(&out_path);
        std::fs::create_dir_all(out_path)?;

        for file in &self.grammar_files {
            tracing::trace!("Processing grammar file: {}", file);
            let content = std::fs::read_to_string(file)
                .unwrap_or_else(|e| panic!("Failed to read grammar file {}: {}", file, e));
            let grammar = Parser::new(&content).parse_grammar();
            let generator = Generator::new(grammar);
            let generated_code = generator.generate();
            let filename = std::path::Path::new(file)
                .file_name()
                .expect("Grammar file path should have a file name")
                .to_str()
                .unwrap();
            let path = out_path.join(format!("{}.rs", filename));

            let _ = std::fs::write(&path, generated_code.to_string())?;

            let status = std::process::Command::new("rustfmt")
                .arg(&path)
                .status()
                .expect("Failed to run rustfmt");

            if !status.success() {
                panic!("rustfmt failed");
            }
        }
        Ok(())
    }
}
