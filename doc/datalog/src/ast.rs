use std::fmt;

#[derive(Debug, Clone, PartialEq)]
pub struct Program {
    pub statements: Vec<Statement>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Statement {
    Assertion(Clause),
    Retraction(Clause),
    Query(Literal),
    Requirement(String),
}

#[derive(Debug, Clone, PartialEq)]
pub struct Clause {
    pub head: Literal,
    pub body: Option<Vec<Literal>>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Literal {
    Predicate(PredicateSym, Vec<Term>),
    PredicateNoArgs(PredicateSym),
    Equals(Term, Term),
    NotEquals(Term, Term),
    External(String, String, Vec<Term>), // VARIABLE :- external_sym ( terms )
}

#[derive(Debug, Clone, PartialEq)]
pub enum PredicateSym {
    Identifier(String),
    String(String),
}

#[derive(Debug, Clone, PartialEq)]
pub enum Term {
    Variable(String),
    Constant(Constant),
}

#[derive(Debug, Clone, PartialEq)]
pub enum Constant {
    Identifier(String),
    String(String),
    Integer(i64),
    True,
    False,
}

impl fmt::Display for PredicateSym {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            PredicateSym::Identifier(s) => write!(f, "{}", s),
            PredicateSym::String(s) => write!(f, "\"{}\"", s),
        }
    }
}
