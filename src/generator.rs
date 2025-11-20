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
    pub production: Vec<String>,
    pub action: String,
}

/// generation strategy:
/// 1. collect all non-terminals and their return types
/// 2. create a `enum Value` that can represent all possible return types and str token
/// 3. for each rule, generate a function that pops arguments from a stack and pushes the result
/// 4. create a table that maps rule id to action function
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

        let fn0_name = format_ident!("rule_{}", 0usize);
        funcs.push(quote! {
            pub fn #fn0_name(stack: &mut Vec<Value>) -> Value {
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
            pub type ActionFn = fn(&mut Vec<Value>) -> Value;
            pub const RULE_TABLE: &[ActionFn] = &[
                #(#rows),*
            ];
        }
    }
}
