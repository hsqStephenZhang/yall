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
pub struct GenGrammar {
    pub rule_groups: Vec<GenRuleGroup>,
    pub semantic_action_type: Option<String>,
    pub extern_code: Option<String>,
}

impl GenGrammar {
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
        let value_enum = self.gen_value_enum();
        let action_fns = self.gen_action_fns();
        let table = self.gen_table();

        quote! {
            #extern_code
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
        std::fs::create_dir_all(&out_path).expect("Failed to create output directory");
        for file in &self.grammar_files {
            tracing::trace!("Processing grammar file: {}", file);
            let content = std::fs::read_to_string(file)
                .unwrap_or_else(|e| panic!("Failed to read grammar file {}: {}", file, e));
            let grammar = Parser::new(&content).parse_grammar();
            let generator = Generator::new(grammar);
            let generated_code = generator.generate();
            let out_path = format!("{}.rs", file.trim_end_matches(".yapg"));
            let _ = std::fs::write(&out_path, generated_code.to_string())?;
        }
        Ok(())
    }
}
