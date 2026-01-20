use std::cell::OnceCell;
use std::collections::{HashMap, HashSet};

use heck::ToUpperCamelCase;
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
    // For handling | alternatives within a rule
    pub alternatives: Vec<Vec<GenRule>>,
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
pub enum ProductionItem {
    Symbol(String),
    // Item with a suffix operator: +, *, or ?
    ZeroOrMore(String), // item*
    OneOrMore(String),  // item+
    Optional(String),   // item?
}

impl ProductionItem {
    pub fn symbol(&self) -> &str {
        match self {
            ProductionItem::Symbol(s) => s,
            ProductionItem::ZeroOrMore(s) => s,
            ProductionItem::OneOrMore(s) => s,
            ProductionItem::Optional(s) => s,
        }
    }
}

#[derive(Debug, Clone)]
pub struct GenRule {
    pub production: Vec<ProductionItem>,
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
        let mut grammar = Self {
            rule_groups,
            token_ty,
            token_kinds,
            semantic_action_type,
            extern_code,
            non_terminals: OnceCell::new(),
        };
        grammar.expand_operators();
        grammar
    }

    /// Sanitize a symbol name to be a valid Rust identifier
    fn sanitize_name(s: &str) -> String {
        s.replace("::", "_")
            .replace("(", "")
            .replace(")", "")
            .replace(" ", "Empty")
            .replace(",", "Comma")
            .replace("[", "LBracket")
            .replace("]", "RBracket")
            .replace("+", "Plus")
            .replace("*", "Star")
    }

    /// Expand operators (+, *, ?) into auxiliary grammar rules
    fn expand_operators(&mut self) {
        let mut new_rule_groups = Vec::new();
        let mut counter = 0;

        // Build a type map before we start mutating
        let mut type_map: HashMap<String, String> = HashMap::new();
        for group in &self.rule_groups {
            type_map.insert(group.name.clone(), group.return_type.clone());
        }

        let token_ty = self.token_ty.clone();

        for group in &mut self.rule_groups {
            for rule in &mut group.rules {
                let mut new_production = Vec::new();

                for item in &rule.production {
                    match item {
                        ProductionItem::Symbol(s) => {
                            new_production.push(ProductionItem::Symbol(s.clone()));
                        }
                        ProductionItem::OneOrMore(s) => {
                            // First, expand parenthesized groups
                            let (expanded_symbol, elem_type, group_aux_rules) =
                                Self::expand_group(&token_ty, s, &mut counter, &type_map);
                            new_rule_groups.extend(group_aux_rules);

                            // Update type_map with the new symbol
                            if let Some(ref et) = elem_type {
                                type_map.insert(expanded_symbol.clone(), et.clone());
                            }

                            // Then create auxiliary non-terminal for A+
                            let sanitized = Self::sanitize_name(&expanded_symbol);
                            let aux_name = format!("{}_plus_{}", sanitized, counter);
                            counter += 1;

                            let element_type = elem_type.unwrap_or_else(|| {
                                Self::get_type_from_map(&token_ty, &expanded_symbol, &type_map)
                            });

                            // A_plus -> A | A_plus A
                            let aux_rules = vec![
                                GenRule {
                                    production: vec![ProductionItem::Symbol(
                                        expanded_symbol.clone(),
                                    )],
                                    action: ActionKind::Code("vec![arg1]".to_string()),
                                },
                                GenRule {
                                    production: vec![
                                        ProductionItem::Symbol(aux_name.clone()),
                                        ProductionItem::Symbol(expanded_symbol.clone()),
                                    ],
                                    action: ActionKind::Code(
                                        "{ let mut v = arg1; v.push(arg2); v }".to_string(),
                                    ),
                                },
                            ];

                            let aux_type = format!("Vec<{}>", element_type);
                            type_map.insert(aux_name.clone(), aux_type.clone());

                            new_rule_groups.push(GenRuleGroup {
                                name: aux_name.clone(),
                                return_type: aux_type,
                                rules: aux_rules,
                                alternatives: Vec::new(),
                            });

                            new_production.push(ProductionItem::Symbol(aux_name));
                        }
                        ProductionItem::ZeroOrMore(s) => {
                            // First, expand parenthesized groups
                            let (expanded_symbol, elem_type, group_aux_rules) =
                                Self::expand_group(&token_ty, s, &mut counter, &type_map);
                            new_rule_groups.extend(group_aux_rules);

                            // Update type_map with the new symbol
                            if let Some(ref et) = elem_type {
                                type_map.insert(expanded_symbol.clone(), et.clone());
                            }

                            // Then create auxiliary non-terminal for A*
                            let sanitized = Self::sanitize_name(&expanded_symbol);
                            let aux_name = format!("{}_star_{}", sanitized, counter);
                            counter += 1;

                            let element_type = elem_type.unwrap_or_else(|| {
                                Self::get_type_from_map(&token_ty, &expanded_symbol, &type_map)
                            });

                            // A_star -> ε | A_star A
                            let aux_rules = vec![
                                GenRule {
                                    production: vec![],
                                    action: ActionKind::Code("Vec::new()".to_string()),
                                },
                                GenRule {
                                    production: vec![
                                        ProductionItem::Symbol(aux_name.clone()),
                                        ProductionItem::Symbol(expanded_symbol.clone()),
                                    ],
                                    action: ActionKind::Code(
                                        "{ let mut v = arg1; v.push(arg2); v }".to_string(),
                                    ),
                                },
                            ];

                            let aux_type = format!("Vec<{}>", element_type);
                            type_map.insert(aux_name.clone(), aux_type.clone());

                            new_rule_groups.push(GenRuleGroup {
                                name: aux_name.clone(),
                                return_type: aux_type,
                                rules: aux_rules,
                                alternatives: Vec::new(),
                            });

                            new_production.push(ProductionItem::Symbol(aux_name));
                        }
                        ProductionItem::Optional(s) => {
                            // First, expand parenthesized groups
                            let (expanded_symbol, elem_type, group_aux_rules) =
                                Self::expand_group(&token_ty, s, &mut counter, &type_map);
                            new_rule_groups.extend(group_aux_rules);

                            // Update type_map with the new symbol
                            if let Some(ref et) = elem_type {
                                type_map.insert(expanded_symbol.clone(), et.clone());
                            }

                            // Then create auxiliary non-terminal for A?
                            let sanitized = Self::sanitize_name(&expanded_symbol);
                            let aux_name = format!("{}_opt_{}", sanitized, counter);
                            counter += 1;

                            let element_type = elem_type.unwrap_or_else(|| {
                                Self::get_type_from_map(&token_ty, &expanded_symbol, &type_map)
                            });

                            // A_opt -> ε | A
                            let aux_rules = vec![
                                GenRule {
                                    production: vec![],
                                    action: ActionKind::Code("None".to_string()),
                                },
                                GenRule {
                                    production: vec![ProductionItem::Symbol(
                                        expanded_symbol.clone(),
                                    )],
                                    action: ActionKind::Code("Some(arg1)".to_string()),
                                },
                            ];

                            let aux_type = format!("Option<{}>", element_type);
                            type_map.insert(aux_name.clone(), aux_type.clone());

                            new_rule_groups.push(GenRuleGroup {
                                name: aux_name.clone(),
                                return_type: aux_type,
                                rules: aux_rules,
                                alternatives: Vec::new(),
                            });

                            new_production.push(ProductionItem::Symbol(aux_name));
                        }
                    }
                }

                rule.production = new_production;
            }
        }

        self.rule_groups.extend(new_rule_groups);
    }

    /// Expand a parenthesized group like "(Token::Comma Item)" into an auxiliary non-terminal
    /// Returns (new_symbol_name, element_type, auxiliary_rule_groups)
    fn expand_group(
        token_ty: &str,
        s: &str,
        counter: &mut usize,
        type_map: &HashMap<String, String>,
    ) -> (String, Option<String>, Vec<GenRuleGroup>) {
        // Check if it's a parenthesized group
        if !s.starts_with('(') || !s.ends_with(')') {
            return (s.to_string(), None, vec![]);
        }

        // Extract the content inside parentheses
        let content = &s[1..s.len() - 1];

        // Split by whitespace to get individual symbols
        let symbols: Vec<&str> = content.split_whitespace().collect();

        // Create a new non-terminal for this group
        let sanitized = Self::sanitize_name(content);
        let group_name = format!("{}_group_{}", sanitized, *counter);
        *counter += 1;

        // Determine the return type (tuple of symbol types)
        let symbol_types: Vec<String> =
            symbols.iter().map(|sym| Self::get_type_from_map(token_ty, sym, type_map)).collect();

        let return_type = if symbol_types.len() == 1 {
            symbol_types[0].clone()
        } else {
            format!("({})", symbol_types.join(", "))
        };

        // Create the production: Group -> Symbol1 Symbol2 ...
        let production: Vec<ProductionItem> =
            symbols.iter().map(|s| ProductionItem::Symbol(s.to_string())).collect();

        // Create action that constructs the tuple
        let action = if symbols.len() == 1 {
            ActionKind::Code("arg1".to_string())
        } else {
            let args: Vec<String> = (1..=symbols.len()).map(|i| format!("arg{}", i)).collect();
            ActionKind::Code(format!("({})", args.join(", ")))
        };

        let group_rule = GenRule { production, action };

        let group_rule_group = GenRuleGroup {
            name: group_name.clone(),
            return_type: return_type.clone(),
            rules: vec![group_rule],
            alternatives: Vec::new(),
        };

        (group_name, Some(return_type), vec![group_rule_group])
    }
    /// Get type from the type map, or default to Token type
    fn get_type_from_map(
        token_ty: &str,
        symbol: &str,
        type_map: &HashMap<String, String>,
    ) -> String {
        if let Some(ty) = type_map.get(symbol) { ty.clone() } else { token_ty.to_string() }
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

    pub fn start_sym(&self) -> String {
        self.rule_groups[0].name.clone()
    }

    pub fn type_of(&self, symbol: &str) -> Option<&String> {
        for group in &self.rule_groups {
            if group.name == symbol {
                return Some(&group.return_type);
            }
        }
        None
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
                    .map(|item| {
                        let s = item.symbol();
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
        let extern_code = self.grammar.extern_code.as_deref().unwrap_or("");
        let extern_code: syn::File =
            syn::parse_str(extern_code).unwrap_or_else(|_| panic!("Invalid extern code"));
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
            #[allow(non_camel_case_types)]
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
        let semantic_action_ty: syn::Type = match self.grammar.semantic_action_type.as_ref() {
            None => syn::parse_str("()").unwrap(),
            Some(ty) => syn::parse_str(ty).expect("Invalid SemanticAction type"),
        };
        let defs = &self.grammar.rule_groups;
        let mut funcs = Vec::new();

        let fn0_name = format_ident!("rule_{}", 0usize);
        funcs.push(quote! {
            #[allow(unused)]
            #[allow(clippy::ptr_arg)]
            fn #fn0_name(action: &mut #semantic_action_ty, stack: &mut Vec<Value>) -> Value {
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

                for (i, item) in rule.production.iter().enumerate().rev() {
                    let arg_name = format_ident!("arg{}", i + 1); // arg1, arg2...
                    let symbol = item.symbol();

                    let target_variant =
                        if self.symbol_type_map.contains_key(symbol) { symbol } else { "Token" };
                    let conversion_method = format_ident!("into_{}", target_variant.to_lowercase());

                    pops.push(quote! {
                        let #arg_name = stack.pop().unwrap().#conversion_method();
                    });
                }

                match &rule.action {
                    ActionKind::Code(code) => {
                        let user_action: TokenStream = syn::parse_str(code)
                            .unwrap_or_else(|_| panic!("Invalid action code: {}", code));
                        funcs.push(quote! {
                            #[allow(unused)]
                            #[allow(clippy::useless_conversion)]
                            fn #fn_name(action: &mut #semantic_action_ty, stack: &mut Vec<Value>) -> Value {
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
                            #[allow(clippy::useless_conversion)]
                            fn #fn_name(action: &mut #semantic_action_ty, stack: &mut Vec<Value>) -> Value {
                                #(#pops)*
                                let args = #args;
                                let result = #semantic_action_ty::#method(action, args);
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
        let sema_ty = match self.grammar.semantic_action_type.as_ref() {
            None => "()",
            Some(ty) => ty.as_str(),
        };
        let sema_ty: syn::Type = syn::parse_str(sema_ty)
            .unwrap_or_else(|_| panic!("Invalid SemanticAction type {}", sema_ty));

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
            type ActionFn = fn(&mut #sema_ty, &mut Vec<Value>) -> Value;
            const RULE_TABLE: &[ActionFn] = &[
                #(#rows),*
            ];
        }
    }

    fn gen_parser(&self) -> TokenStream {
        let start_sym = self.grammar.start_sym();
        let start_sym_ty =
            self.grammar.type_of(&start_sym).expect("Start symbol must have a return type");

        let extract_method_name = format_ident!("into_{}", start_sym.to_lowercase());
        let parser_name = format_ident!("{}Parser", start_sym.to_upper_camel_case());
        let ty_name = syn::parse_str::<syn::Type>(start_sym_ty)
            .unwrap_or_else(|_| panic!("Invalid type for start symbol: {}", start_sym_ty));
        let sema_ty = match self.grammar.semantic_action_type.as_ref() {
            None => "()",
            Some(ty) => ty.as_str(),
        };
        let sema_ty: syn::Type = syn::parse_str(sema_ty)
            .unwrap_or_else(|_| panic!("Invalid SemanticAction type {}", sema_ty));

        let parser = quote! {
            pub(crate) struct #parser_name<Actioner> {
                actioner: Actioner,
            }

            impl #parser_name<#sema_ty> {
                pub fn new(actioner: #sema_ty) -> Self {
                    Self { actioner }
                }

                pub fn parse<I: Iterator<Item = Token>>(
                    self,
                    token_stream: std::iter::Peekable<I>,
                ) -> Option<#ty_name> {
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
                    if pda.process(token_stream, &ctx) { Some(pda.final_value().#extract_method_name()) } else { None }
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

#[derive(Default)]
pub struct Configuration {
    grammar_files: Vec<String>,
}

impl Configuration {
    pub fn new() -> Self {
        Self::default()
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

            std::fs::write(&path, generated_code.to_string())?;

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
