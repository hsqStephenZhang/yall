use std::cell::OnceCell;
use std::collections::{HashMap, HashSet, VecDeque};
use std::fmt::Debug;
use std::hash::Hash;
use std::ops::Index;

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
    pub fn id(&self) -> &str {
        match self {
            Symbol::Term(s) => s.id(),
            Symbol::NonTerm(non_terminal) => &non_terminal.0,
            Symbol::Epsilon => "ε",
        }
    }
}

impl<Tk: TerminalKind> Symbol<Tk> {
    pub fn into_term(self) -> Tk {
        if let Self::Term(term) = self { term } else { panic!() }
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
    // pseudo start symbol that at the top of the ast tree, i.e. S'
    pub pseudo_start_sym: NonTerminal,

    // actual start symbol defined by user
    pub start_sym: NonTerminal,

    // all production rules
    pub rules: Vec<Rule<Tk>>,

    // first set cache
    pub first: OnceCell<HashMap<Symbol<Tk>, HashSet<Tk>>>,

    // follow set cache
    pub follow: OnceCell<HashMap<Symbol<Tk>, HashSet<Tk>>>,

    pub emptyables: OnceCell<HashSet<NonTerminal>>,
}

impl<Tk: Clone + TerminalKind + Eq + Hash + Debug> Grammar<Tk> {
    pub fn new(
        pseudo_start_sym: NonTerminal,
        start_sym: NonTerminal,
        rules: Vec<Rule<Tk>>,
    ) -> Self {
        Self {
            pseudo_start_sym,
            start_sym,
            rules,
            first: OnceCell::new(),
            follow: OnceCell::new(),
            emptyables: OnceCell::new(),
        }
    }

    /// all non-terminals that could derive epsilon
    pub fn emptyables(&self) -> &HashSet<NonTerminal> {
        self.emptyables.get_or_init(|| {
            self.rules
                .iter()
                .filter_map(
                    |rule| {
                        if rule.right.is_empty() { Some(rule.left.clone()) } else { None }
                    },
                )
                .collect::<HashSet<_>>()
        })
    }

    // given a sequence of symbols, compute its first set
    // e.g. for symbols `βc`, it will be First(β) ∪ First(c) if β could be empty
    pub fn first_set_of_symbols(&self, symbols: &[Symbol<Tk>]) -> HashSet<Tk>
    where
        Tk: Clone,
    {
        let could_be_empty = self.emptyables();
        let first_set = self.first_set();
        let mut result = HashSet::new();

        for sym in symbols {
            let first_set = first_set.get(sym);
            if let Some(first) = first_set {
                result.extend(first.clone());
            }
            match sym {
                Symbol::NonTerm(nt) if could_be_empty.contains(nt) => {}
                Symbol::Epsilon => {}
                _ => break,
            }
        }

        result
    }

    pub fn first_set(&self) -> &HashMap<Symbol<Tk>, HashSet<Tk>> {
        self.first.get_or_init(|| self.calculate_first_set())
    }

    pub fn follow_set(&self) -> &HashMap<Symbol<Tk>, HashSet<Tk>> {
        self.follow.get_or_init(|| self.calculate_follow_set())
    }
}

impl<Tk: Clone + TerminalKind + Eq + Hash + Debug> Grammar<Tk> {
    pub fn rules_of(&self, non_term: &NonTerminal) -> impl Iterator<Item = (usize, &Rule<Tk>)> {
        self.rules.iter().enumerate().filter(|(_, rule)| rule.left == *non_term)
    }

    fn calculate_first_set(&self) -> HashMap<Symbol<Tk>, HashSet<Tk>> {
        let mut all_syms = self
            .rules
            .iter()
            .flat_map(|rule| {
                let mut right = rule.right.clone();
                right.push(rule.left.clone().into());
                right
            })
            .collect::<HashSet<_>>();
        all_syms.remove(&Symbol::Epsilon);

        // 1. calculate the emptyable Non-terminals

        // from sym to the syms that depend on it (for the first set)
        // we don't take account of epsilon here
        let could_be_empty = self.emptyables();

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

            might_be_empty_rules =
                might_be_empty_rules.difference(&rules_to_remove).cloned().collect::<HashSet<_>>();
        }

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
                    first_set.entry(cur.clone()).or_default().insert(term.clone());
                    true
                }
                Symbol::NonTerm(non_terminal) => {
                    let mut changed = false;
                    let rules = nonterm_to_rules
                        .get(non_terminal)
                        .unwrap_or_else(|| panic!("No rules for non-terminal {:?}", non_terminal));
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

        first_set
    }

    fn calculate_follow_set(&self) -> HashMap<Symbol<Tk>, HashSet<Tk>> {
        debug!("calculating follow set");

        // two rules for calculating Follow set:
        //      1. for A -> α B β γ, add First(β) to Follow(B) ; if β could be empty, recursively check γ
        //      2. for A -> α B, add Follow(A) to Follow(B)
        // (here α β γ represents any symbol kind, terminal or non-terminal, B is a non-terminal)
        //
        // we will iterate to a fixed point

        let mut follow_set: HashMap<Symbol<Tk>, HashSet<Tk>> = HashMap::new();

        let could_be_empty = self.emptyables();
        let first_set = self.first_set();

        let mut changed = true;
        while changed {
            changed = false;

            for rule in self.rules.iter().filter(|rule| !rule.right.is_empty()) {
                for idx in 0..rule.right.len() {
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

                        // case 2 get
                        let maybe_left_follow_set = if follower_sym_idx == rule.right.len() {
                            follow_set.get(&Symbol::NonTerm(rule.left.clone())).cloned()
                        } else {
                            None
                        };

                        let follower = follow_set.entry(rule.right[idx].clone()).or_default();
                        let before_size = follower.len();

                        // case 2 add
                        if let Some(left_follow_set) = maybe_left_follow_set {
                            follower.extend(left_follow_set);
                        }

                        // case 1
                        for &follower_idx in &all_follower_syms {
                            follower.extend(
                                first_set
                                    .get(&rule.right[follower_idx])
                                    .cloned()
                                    .unwrap_or_default(),
                            );
                        }
                        let after_size = follower.len();

                        if after_size > before_size {
                            changed = true;
                        }
                    }
                }
            }
        }

        follow_set.into_iter().filter(|(_, terms)| !terms.is_empty()).collect::<HashMap<_, _>>()
    }
}

impl<Tk: Hash + Eq> Index<usize> for Grammar<Tk> {
    type Output = Rule<Tk>;

    fn index(&self, index: usize) -> &Self::Output {
        &self.rules[index]
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::tests::parse_lines;

    fn new_set<Tk: TerminalKind + Hash + Eq>(
        expect_first: Vec<(Symbol<Tk>, Vec<Tk>)>,
    ) -> HashMap<Symbol<Tk>, HashSet<Tk>> {
        let mut first = HashMap::new();
        for (sym, terms) in expect_first {
            first.insert(sym, terms.into_iter().collect());
        }
        first
    }

    #[test]
    fn test_parse1() {
        let grammar = parse_lines("S", vec!["S -> A B", "A -> a", "A -> ε", "B -> b"]);

        assert_eq!(grammar.start_sym, NonTerminal::new("S"));
        assert_eq!(grammar.rules[1].left, NonTerminal::new("S"));
        assert_eq!(
            grammar.rules[1].right,
            vec![Symbol::NonTerm(NonTerminal::new("A")), Symbol::NonTerm(NonTerminal::new("B")),]
        );
        assert_eq!(grammar.rules[2].left, NonTerminal::new("A"));
        assert_eq!(grammar.rules[2].right, vec![Symbol::Term(Terminal::new("a"))]);
        assert_eq!(grammar.rules[3].left, NonTerminal::new("A"));
        assert_eq!(grammar.rules[3].right, vec![]);
        assert_eq!(grammar.rules[4].left, NonTerminal::new("B"));
        assert_eq!(grammar.rules[4].right, vec![Symbol::Term(Terminal::new("b"))]);
    }

    #[test]
    fn test_parse2() {
        let grammar = parse_lines::<_, Terminal>(
            "E",
            vec!["E -> E + T", "E -> T", "T -> T * F", "T -> F", "F -> ( E )", "F -> id"],
        );

        assert_eq!(grammar.start_sym, NonTerminal::new("E"));
        assert_eq!(grammar.rules.len(), 7);
    }

    #[test]
    fn test_first_set1() {
        let grammar = parse_lines("S", vec!["S -> A B", "A -> A a", "A -> ε", "B -> b"]);

        let first_set = grammar.first_set();

        let expect = new_set(vec![
            (grammar.pseudo_start_sym.clone().into(), vec![Terminal::new("a"), Terminal::new("b")]),
            (Symbol::NonTerm(NonTerminal::new("S")), vec![Terminal::new("a"), Terminal::new("b")]),
            (Symbol::NonTerm(NonTerminal::new("A")), vec![Terminal::new("a")]),
            (Symbol::NonTerm(NonTerminal::new("B")), vec![Terminal::new("b")]),
            (Symbol::Term(Terminal::new("a")), vec![Terminal::new("a")]),
            (Symbol::Term(Terminal::new("b")), vec![Terminal::new("b")]),
        ]);
        assert_eq!(first_set, &expect);
    }

    #[test]
    fn test_first_set2() {
        let grammar = parse_lines(
            "E",
            vec!["E -> E + T", "E -> T", "T -> T * F", "T -> F", "F -> ( E )", "F -> id"],
        );

        let first_set = grammar.first_set();

        let expect = new_set(vec![
            (
                grammar.pseudo_start_sym.clone().into(),
                vec![Terminal::new("("), Terminal::new("id")],
            ),
            (NonTerminal::new("E").into(), vec![Terminal::new("("), Terminal::new("id")]),
            (NonTerminal::new("T").into(), vec![Terminal::new("("), Terminal::new("id")]),
            (NonTerminal::new("F").into(), vec![Terminal::new("("), Terminal::new("id")]),
            (Symbol::Term(Terminal::new("+")), vec![Terminal::new("+")]),
            (Symbol::Term(Terminal::new("*")), vec![Terminal::new("*")]),
            (Symbol::Term(Terminal::new("(")), vec![Terminal::new("(")]),
            (Symbol::Term(Terminal::new(")")), vec![Terminal::new(")")]),
            (Symbol::Term(Terminal::new("id")), vec![Terminal::new("id")]),
        ]);
        assert_eq!(first_set, &expect);
    }

    #[test]
    fn test_follow_set() {
        let grammar = parse_lines(
            "S",
            vec!["S -> A B", "S -> A", "A -> a C c", "C -> b b C", "C -> b", "B -> c d"],
        );

        // we will ignore the $ pseduo terminal symbol at the end
        let first_follow = grammar.follow_set();
        let expect = new_set(vec![
            (Symbol::NonTerm(NonTerminal::new("A")), vec![Terminal::new("c")]),
            (Symbol::NonTerm(NonTerminal::new("C")), vec![Terminal::new("c")]),
        ]);
        assert_eq!(first_follow, &expect);
    }
}
