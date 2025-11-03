use std::{hash::Hash, ops::Index};

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

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct Terminal(pub(crate) char);

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum Symbol {
    Term(Terminal),
    NonTerm(NonTerminal),
    Epsilon,
}

impl From<NonTerminal> for Symbol {
    fn from(value: NonTerminal) -> Self {
        Self::NonTerm(value)
    }
}

impl From<Terminal> for Symbol {
    fn from(value: Terminal) -> Self {
        Self::Term(value)
    }
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct Rule {
    pub left: NonTerminal,
    pub right: Vec<Symbol>,
}

#[derive(Debug, Clone)]
pub struct Grammar {
    pub start_sym: NonTerminal,
    pub rules: Vec<Rule>,
}

impl Grammar {
    pub fn rules_of(&self, non_term: &NonTerminal) -> impl Iterator<Item = (usize, &Rule)> {
        self.rules
            .iter()
            .enumerate()
            .filter(|(_, rule)| rule.left == *non_term)
    }
}

impl Index<usize> for Grammar {
    type Output = Rule;

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
