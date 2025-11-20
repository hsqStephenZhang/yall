use std::{
    cell::OnceCell,
    collections::{HashMap, HashSet, VecDeque},
    hash::Hash,
    ops::Index,
};

use tracing::debug;

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct NonTerminal(pub(crate) String);

impl NonTerminal {
    pub fn new<S: Into<String>>(s: S) -> Self {
        Self(s.into())
    }
}

impl<T: Into<String>> From<T> for NonTerminal {
    fn from(value: T) -> Self {
        Self(value.into())
    }
}

pub trait TerminalKind {
    // identifier of the terminal, must be unique within a grammar
    fn id(&self) -> &str;
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct Terminal(pub(crate) String);

impl Terminal {
    pub fn new<S: Into<String>>(s: S) -> Self {
        Self(s.into())
    }
}

impl<'a> From<&'a str> for Terminal {
    fn from(value: &'a str) -> Self {
        Self(value.into())
    }
}

impl TerminalKind for Terminal {
    fn id(&self) -> &str {
        &self.0
    }
}

impl std::fmt::Display for Terminal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "Term({})", self.0)
    }
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum Symbol<Tk> {
    Term(Tk),
    NonTerm(NonTerminal),
    Epsilon,
}

impl<Tk: TerminalKind> Symbol<Tk> {
    pub fn name(&self) -> &str {
        match self {
            Symbol::Term(s) => s.id(),
            Symbol::NonTerm(non_terminal) => &non_terminal.0,
            Symbol::Epsilon => "ε",
        }
    }
}

impl<Tk: TerminalKind> Symbol<Tk> {
    pub fn into_term(self) -> Tk {
        if let Self::Term(term) = self {
            term
        } else {
            panic!()
        }
    }
}

impl<Tk: TerminalKind> From<NonTerminal> for Symbol<Tk> {
    fn from(value: NonTerminal) -> Self {
        Self::NonTerm(value)
    }
}

impl<Tk: TerminalKind> From<Tk> for Symbol<Tk> {
    fn from(value: Tk) -> Self {
        Self::Term(value)
    }
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct Rule<Tk> {
    pub left: NonTerminal,
    pub right: Vec<Symbol<Tk>>,
}

impl<Tk: TerminalKind + std::fmt::Display> std::fmt::Display for Rule<Tk> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} -> ", self.left.0)?;
        if self.right.is_empty() {
            write!(f, "ε")
        } else {
            for sym in &self.right {
                match sym {
                    Symbol::Term(t) => write!(f, "'{}' ", t.id())?,
                    Symbol::NonTerm(nt) => write!(f, "{} ", nt.0)?,
                    Symbol::Epsilon => write!(f, "ε ")?,
                }
            }
            Ok(())
        }
    }
}

#[derive(Clone)]
pub struct Grammar<Tk: Hash + Eq> {
    pub pseudo_start_sym: NonTerminal,
    pub start_sym: NonTerminal,
    pub rules: Vec<Rule<Tk>>,

    // first set cache
    pub first_and_follow: OnceCell<FirstFollow<Tk>>,
}

pub fn parse_lines<S, T>(start_sym: &str, raw_rules: Vec<S>) -> Grammar<T>
where
    S: AsRef<str>,
    T: for<'a> From<&'a str> + Hash + Eq,
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

        Rule {
            left: left_nt,
            right: right_syms,
        }
    }));

    Grammar {
        pseudo_start_sym,
        start_sym,
        rules,
        first_and_follow: OnceCell::new(),
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FirstFollow<Tk: Eq + Hash> {
    first: HashMap<Symbol<Tk>, HashSet<Tk>>,
    follow: HashMap<Symbol<Tk>, HashSet<Tk>>,
}

impl<Tk: Hash + Eq> FirstFollow<Tk> {
    pub fn first(&self) -> &HashMap<Symbol<Tk>, HashSet<Tk>> {
        &self.first
    }

    pub fn follow(&self) -> &HashMap<Symbol<Tk>, HashSet<Tk>> {
        &self.follow
    }
}

#[cfg(test)]
pub enum CompareOption {
    First,
    Follow,
    Both,
}

impl<Tk: TerminalKind + Hash + Eq> FirstFollow<Tk> {
    #[cfg(test)]
    fn new_for_test(
        expect_first: Vec<(Symbol<Tk>, Vec<Tk>)>,
        expect_follow: Vec<(Symbol<Tk>, Vec<Tk>)>,
    ) -> FirstFollow<Tk> {
        let mut first = HashMap::new();
        for (sym, terms) in expect_first {
            first.insert(sym, terms.into_iter().collect());
        }
        let mut follow = HashMap::new();
        for (sym, terms) in expect_follow {
            follow.insert(sym, terms.into_iter().collect());
        }

        FirstFollow { first, follow }
    }

    #[cfg(test)]
    fn assert_eq(&self, cmp_opt: CompareOption, other: &Self) -> bool {
        fn assert_set_eq<Tk: TerminalKind + Hash + Eq>(
            set_name: &str,
            set1: &HashMap<Symbol<Tk>, HashSet<Tk>>,
            set2: &HashMap<Symbol<Tk>, HashSet<Tk>>,
        ) -> bool {
            if set1 != set2 {
                print!("difference in {}\n", set_name);
                println!("left:");
                for (sym, terms) in set1 {
                    let term_ids = terms.iter().map(|t| t.id()).collect::<Vec<_>>();
                    println!("  {}: {:?}", sym.name(), term_ids);
                }
                println!("right:");
                for (sym, terms) in set2 {
                    let term_ids = terms.iter().map(|t| t.id()).collect::<Vec<_>>();
                    println!("  {}: {:?}", sym.name(), term_ids);
                }
                false
            } else {
                true
            }
        }
        match cmp_opt {
            CompareOption::First => assert_set_eq("First", &self.first, &other.first),
            CompareOption::Follow => assert_set_eq("Follow", &self.follow, &other.follow),
            CompareOption::Both => {
                assert_set_eq("First", &self.first, &other.first)
                    && assert_set_eq("Follow", &self.follow, &other.follow)
            }
        }
    }
}

#[derive(Debug, Clone)]
pub struct FollowSet {}

impl<Tk: Clone + TerminalKind + Eq + Hash> Grammar<Tk> {
    pub fn rules_of(&self, non_term: &NonTerminal) -> impl Iterator<Item = (usize, &Rule<Tk>)> {
        self.rules
            .iter()
            .enumerate()
            .filter(|(_, rule)| rule.left == *non_term)
    }

    pub fn first_follow_set(&self) -> &FirstFollow<Tk> {
        self.first_and_follow
            .get_or_init(|| self.calculate_first_follow_set())
    }

    pub fn calculate_first_follow_set(&self) -> FirstFollow<Tk> {
        let mut all_syms = self
            .rules
            .iter()
            .map(|rule| {
                let mut right = rule.right.clone();
                right.push(rule.left.clone().into());
                right
            })
            .flatten()
            .collect::<HashSet<_>>();
        all_syms.remove(&Symbol::Epsilon);

        // 1. calculate the emptyable Non-terminals

        // from sym to the syms that depend on it (for the first set)
        // we don't take account of epsilon here
        let mut could_be_empty = self
            .rules
            .iter()
            .filter_map(|rule| {
                if rule.right.is_empty() {
                    Some(rule.left.clone())
                } else {
                    None
                }
            })
            .collect::<HashSet<_>>();

        let mut might_be_empty_rules = self
            .rules
            .iter()
            .enumerate()
            .filter_map(|(idx, rule)| {
                if rule.right.iter().all(|x| matches!(x, Symbol::NonTerm(_))) {
                    Some(idx)
                } else {
                    None
                }
            })
            .collect::<HashSet<_>>();

        loop {
            let mut new_added = HashSet::new();
            let mut rules_to_remove = HashSet::new();

            for &rule_num in &might_be_empty_rules {
                if self.rules[rule_num].right.iter().all(|sym| {
                    if let Symbol::NonTerm(nonterm) = sym
                        && could_be_empty.contains(nonterm)
                    {
                        true
                    } else {
                        false
                    }
                }) {
                    new_added.insert(self.rules[rule_num].left.clone());
                    rules_to_remove.insert(rule_num);
                }
            }

            if new_added.is_empty() {
                break;
            }

            could_be_empty.extend(new_added);
            might_be_empty_rules = might_be_empty_rules
                .difference(&rules_to_remove)
                .cloned()
                .collect::<HashSet<_>>();
        }

        // print all the emptyable Non-terminals here
        // #[cfg(debug_assertions)]
        // {
        //     for nt in &could_be_empty {
        //         println!("Could be empty: {:?}", nt);
        //     }
        // }

        // 2. calcualte the deps
        //    (we define deps(x) by all the symbols y where First() is needed to compute First(y))

        let mut deps: HashMap<Symbol<Tk>, HashSet<Symbol<Tk>>> = HashMap::new();
        for rule in &self.rules {
            let sym: Symbol<Tk> = rule.left.clone().into();
            // let entry = deps.entry(sym).or_default();

            // add dependencies
            let mut next_pos = 0;
            while next_pos < rule.right.len() {
                let next_sym = rule.right[next_pos].clone();

                if let Symbol::NonTerm(nonterm) = &next_sym
                    && could_be_empty.contains(nonterm)
                {
                    deps.entry(next_sym).or_default().insert(sym.clone());
                    next_pos += 1;
                } else {
                    deps.entry(next_sym).or_default().insert(sym.clone());
                    break;
                }
            }
        }

        // print dependencies here
        #[cfg(debug_assertions)]
        {
            for (sym, dep_set) in &deps {
                tracing::trace!("Deps for {:?}:", sym.name());
                for dep in dep_set {
                    tracing::trace!("  {:?}", dep.name());
                }
            }
            tracing::trace!("");
        }

        let nonterm_to_rules = self.rules.iter().enumerate().fold(
            HashMap::<NonTerminal, Vec<usize>>::new(),
            |mut acc, (idx, rule)| {
                acc.entry(rule.left.clone()).or_default().push(idx);
                acc
            },
        );

        // now we are cooking, using worklist algorithm to iterate to a fixed point

        debug!("calculating first set");
        let mut first_set: HashMap<Symbol<Tk>, HashSet<Tk>> = HashMap::new();

        let mut worklist = VecDeque::from(all_syms.into_iter().collect::<Vec<_>>());
        while !worklist.is_empty() {
            let cur = worklist.pop_front().unwrap();

            let changed = match &cur {
                Symbol::Term(term) => {
                    first_set
                        .entry(cur.clone())
                        .or_default()
                        .insert(term.clone());
                    true
                }
                Symbol::NonTerm(non_terminal) => {
                    let mut changed = false;
                    let rules = nonterm_to_rules
                        .get(non_terminal)
                        .expect(&format!("No rules for non-terminal {:?}", non_terminal));
                    for &rule_num in rules {
                        let rule = &self.rules[rule_num];
                        for sym in &rule.right {
                            let sym_first = first_set.get(sym).cloned().unwrap_or_default();
                            let mut can_be_empty = false;
                            if let Symbol::NonTerm(nt) = sym
                                && could_be_empty.contains(nt)
                            {
                                can_be_empty = true;
                            }

                            for term in sym_first {
                                changed |= first_set.entry(cur.clone()).or_default().insert(term);
                            }

                            if !can_be_empty {
                                break;
                            }
                        }
                    }
                    changed
                }
                Symbol::Epsilon => todo!(),
            };

            let empty = HashSet::new();

            if changed {
                for dep in deps.get(&cur).unwrap_or(&empty) {
                    worklist.push_back(dep.clone());
                }
            }
        }

        debug!("calculating follow set");

        let mut follow_set: HashMap<Symbol<Tk>, HashSet<Tk>> = HashMap::new();
        for rule in self.rules.iter().filter(|rule| !rule.right.is_empty()) {
            for idx in 0..(rule.right.len() - 1) {
                if matches!(&rule.right[idx], Symbol::NonTerm(_)) {
                    let mut all_follower_syms = vec![];
                    let mut follower_sym_idx = idx + 1;
                    while follower_sym_idx < rule.right.len() {
                        all_follower_syms.push(follower_sym_idx);

                        let sym = &rule.right[follower_sym_idx];
                        if let Symbol::NonTerm(nt) = sym
                            && could_be_empty.contains(nt)
                        {
                            follower_sym_idx += 1;
                        } else {
                            break;
                        }
                    }
                    for &follower_idx in &all_follower_syms {
                        follow_set
                            .entry(rule.right[idx].clone())
                            .or_default()
                            .extend(
                                first_set
                                    .get(&rule.right[follower_idx])
                                    .cloned()
                                    .unwrap_or_default(),
                            );
                    }
                }
            }
        }

        FirstFollow {
            first: first_set,
            follow: follow_set,
        }
    }
}

impl<Tk: Hash + Eq> Index<usize> for Grammar<Tk> {
    type Output = Rule<Tk>;

    fn index(&self, index: usize) -> &Self::Output {
        &self.rules[index]
    }
}

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct Item {
    // num of rule within the grammar
    pub rule: usize,
    // the '•' position
    pub idx: usize,
}

impl Item {
    pub fn new(rule: usize, idx: usize) -> Self {
        Self { rule, idx }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse1() {
        let grammar = parse_lines("S", vec!["S -> A B", "A -> a", "A -> ε", "B -> b"]);

        assert_eq!(grammar.start_sym, NonTerminal::new("S"));
        assert_eq!(grammar.rules[1].left, NonTerminal::new("S"));
        assert_eq!(
            grammar.rules[1].right,
            vec![
                Symbol::NonTerm(NonTerminal::new("A")),
                Symbol::NonTerm(NonTerminal::new("B")),
            ]
        );
        assert_eq!(grammar.rules[2].left, NonTerminal::new("A"));
        assert_eq!(
            grammar.rules[2].right,
            vec![Symbol::Term(Terminal::new("a"))]
        );
        assert_eq!(grammar.rules[3].left, NonTerminal::new("A"));
        assert_eq!(grammar.rules[3].right, vec![]);
        assert_eq!(grammar.rules[4].left, NonTerminal::new("B"));
        assert_eq!(
            grammar.rules[4].right,
            vec![Symbol::Term(Terminal::new("b"))]
        );
    }

    #[test]
    fn test_parse2() {
        let grammar = parse_lines::<_, Terminal>(
            "E",
            vec![
                "E -> E + T",
                "E -> T",
                "T -> T * F",
                "T -> F",
                "F -> ( E )",
                "F -> id",
            ],
        );

        assert_eq!(grammar.start_sym, NonTerminal::new("E"));
        assert_eq!(grammar.rules.len(), 7);
    }

    #[test]
    fn test_first_set1() {
        let grammar = parse_lines("S", vec!["S -> A B", "A -> A a", "A -> ε", "B -> b"]);

        let first_set = grammar.calculate_first_follow_set();

        let expect = FirstFollow::new_for_test(
            vec![
                (
                    grammar.pseudo_start_sym.clone().into(),
                    vec![Terminal::new("a"), Terminal::new("b")],
                ),
                (
                    Symbol::NonTerm(NonTerminal::new("S")),
                    vec![Terminal::new("a"), Terminal::new("b")],
                ),
                (
                    Symbol::NonTerm(NonTerminal::new("A")),
                    vec![Terminal::new("a")],
                ),
                (
                    Symbol::NonTerm(NonTerminal::new("B")),
                    vec![Terminal::new("b")],
                ),
                (Symbol::Term(Terminal::new("a")), vec![Terminal::new("a")]),
                (Symbol::Term(Terminal::new("b")), vec![Terminal::new("b")]),
            ],
            vec![],
        );

        #[cfg(debug_assertions)]
        {
            for (sym, first_set) in &first_set.first {
                println!("First({:?}) =", sym);
                for term in first_set {
                    println!("  {:?}", term);
                }
            }
        }
        assert!(first_set.assert_eq(CompareOption::First, &expect));
    }

    #[test]
    fn test_first_set2() {
        let grammar = parse_lines(
            "E",
            vec![
                "E -> E + T",
                "E -> T",
                "T -> T * F",
                "T -> F",
                "F -> ( E )",
                "F -> id",
            ],
        );

        let first_set = grammar.calculate_first_follow_set();

        let expect = FirstFollow::new_for_test(
            vec![
                (
                    grammar.pseudo_start_sym.clone().into(),
                    vec![Terminal::new("("), Terminal::new("id")],
                ),
                (
                    NonTerminal::new("E").into(),
                    vec![Terminal::new("("), Terminal::new("id")],
                ),
                (
                    NonTerminal::new("T").into(),
                    vec![Terminal::new("("), Terminal::new("id")],
                ),
                (
                    NonTerminal::new("F").into(),
                    vec![Terminal::new("("), Terminal::new("id")],
                ),
                (Symbol::Term(Terminal::new("+")), vec![Terminal::new("+")]),
                (Symbol::Term(Terminal::new("*")), vec![Terminal::new("*")]),
                (Symbol::Term(Terminal::new("(")), vec![Terminal::new("(")]),
                (Symbol::Term(Terminal::new(")")), vec![Terminal::new(")")]),
                (Symbol::Term(Terminal::new("id")), vec![Terminal::new("id")]),
            ],
            vec![],
        );

        #[cfg(debug_assertions)]
        {
            for (sym, first_set) in &first_set.first {
                println!("First({:?}) =", sym);
                for term in first_set {
                    println!("  {:?}", term);
                }
            }
        }
        assert!(first_set.assert_eq(CompareOption::First, &expect));
    }

    #[test]
    fn test_follower() {
        let grammar = parse_lines(
            "S",
            vec![
                "S -> A B",
                "S -> A",
                "A -> a C c",
                "C -> b b C",
                "C -> b",
                "B -> c d",
            ],
        );

        // we will ignore the $ pseduo terminal symbol at the end
        let first_follow = grammar.calculate_first_follow_set();
        assert!(first_follow.assert_eq(
            CompareOption::Follow,
            &FirstFollow::new_for_test(
                vec![],
                vec![
                    (
                        Symbol::NonTerm(NonTerminal::new("A")),
                        vec![Terminal::new("c")],
                    ),
                    (
                        Symbol::NonTerm(NonTerminal::new("C")),
                        vec![Terminal::new("c")],
                    ),
                ],
            ),
        ));
    }
}
