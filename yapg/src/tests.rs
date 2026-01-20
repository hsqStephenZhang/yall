use std::collections::HashSet;
use std::hash::Hash;

use crate::grammar::*;

pub fn parse_lines<S, T>(start_sym: &str, raw_rules: Vec<S>) -> Grammar<T>
where
    S: AsRef<str>,
    T: for<'a> From<&'a str> + Hash + Eq + std::fmt::Debug + Clone + TerminalKind,
{
    let start_sym = NonTerminal::new(start_sym);
    let pseudo_start_sym = NonTerminal::new("S'");

    let nonterms = raw_rules
        .iter()
        .map(|s| {
            let line = s.as_ref();
            let mut parts = line.split("->");
            parts.next().unwrap().trim()
        })
        .collect::<HashSet<_>>();

    let mut rules = vec![Rule {
        left: pseudo_start_sym.clone(),
        right: vec![Symbol::NonTerm(start_sym.clone())],
    }];

    rules.extend(raw_rules.iter().map(|line| {
        let line = line.as_ref();
        let mut parts = line.split("->");
        let left = parts.next().unwrap().trim();
        let right = parts.next().unwrap().trim();

        let left_nt = NonTerminal::new(left);
        let right_syms = if right == "ε" {
            vec![]
        } else {
            right
                .split_whitespace()
                .map(|s| {
                    if nonterms.contains(s) {
                        Symbol::NonTerm(NonTerminal::new(s))
                    } else {
                        Symbol::Term(T::from(s))
                    }
                })
                .collect()
        };

        Rule { left: left_nt, right: right_syms }
    }));

    Grammar::new(pseudo_start_sym, start_sym, rules)
}
