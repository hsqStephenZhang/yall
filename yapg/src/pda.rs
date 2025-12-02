use core::panic;
use std::fmt::Debug;
use std::hash::Hash;
use std::iter::Peekable;

use tracing::trace;

use crate::grammar::*;
use crate::nfa_dfa::{DFA, DfaStateId, PrintableDFAState};

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

#[derive(Clone)]
pub struct PDA<'a, Tk: Hash + Eq, Value, Actioner> {
    stack: Vec<DfaStateId>,
    value_stack: Vec<Value>,
    dfa: DFA<Tk>,
    grammar: Grammar<Tk>,
    actioner: Actioner,
    actions: &'a [fn(&mut Actioner, &mut Vec<Value>) -> Value],
}

impl<'a, Tk, Value, Actioner> PDA<'a, Tk, Value, Actioner>
where
    Tk: Clone + TerminalKind + Hash + Eq + Debug,
    Value: From<Tk> + Debug,
{
    pub fn new(
        dfa: DFA<Tk>,
        grammar: Grammar<Tk>,
        actioner: Actioner,
        actions: &'a [fn(&mut Actioner, &mut Vec<Value>) -> Value],
    ) -> Self {
        Self { stack: vec![dfa.start], value_stack: vec![], dfa, grammar, actioner, actions }
    }

    pub fn process<I: Iterator<Item = Tk>>(&mut self, mut token_stream: Peekable<I>) -> bool {
        while token_stream.peek().is_some() {
            let tk = token_stream.next().unwrap().clone();
            if !self.process_one(tk, &mut token_stream) {
                break;
            }
        }
        for (idx, state) in self.stack.iter().enumerate() {
            println!(
                "Stack state #{}: {:?}",
                idx,
                PrintableDFAState::new(&self.dfa.id_to_state[state], &self.grammar)
            );
        }

        token_stream.peek().is_none()
            && self.stack.len() == 2
            && self.stack[0] == self.dfa.start
            && self.stack[1] == self.dfa.end
    }

    pub fn process_one<I: Iterator<Item = Tk>>(
        &mut self,
        tk: Tk,
        token_stream: &mut Peekable<I>,
    ) -> bool {
        assert!(!self.stack.is_empty());

        // first try to shift
        // push the next state onto the stack according to the dfa transition table
        let current_state = self.stack.last().unwrap();
        if let Some(next_state) = self.dfa.transitions[current_state].get(&Symbol::Term(tk.clone()))
        {
            trace!("Shifted token: {:?}", tk);
            self.stack.push(*next_state);
            self.value_stack.push(tk.into());
            println!("stack after shift: {:?}", self.value_stack);
        }

        // then try to reduce until it's unreduceable
        loop {
            let current_state_id = self.stack.last().unwrap();
            if !self.dfa.final_states.contains(current_state_id) {
                break;
            }

            let current_state = &self.dfa.id_to_state[current_state_id];

            // in final state, need to reduce
            let rule_to_apply = current_state
                .reduce_rule(&self.grammar)
                .expect("should exist only one reduce rule");

            // resolve conflict by looking ahead
            if let Some(follow_set) = self.dfa.conflict_resolver.get(current_state_id)
                && let Some(next_tk) = token_stream.peek()
            {
                // not in the follow set, should not reduce
                if !follow_set.contains(next_tk) {
                    break;
                } else {
                    trace!(
                        "Lookahead token '{:?}' is in follow set, reducing by rule {}",
                        next_tk, rule_to_apply
                    );
                }
            }

            let rule = &self.grammar[rule_to_apply];
            trace!("Reducing by rule {}: {:?}", rule_to_apply, rule);
            if rule_to_apply == 0
                && token_stream.peek().is_none()
                && self.stack.last().unwrap() == &self.dfa.end
            {
                trace!("Parse done!");
                return false;
            }

            let to_pop = rule.right.iter().filter(|sym| !matches!(sym, Symbol::Epsilon)).count();
            for _ in 0..to_pop {
                self.stack.pop();
            }
            let action_fn = self.actions[rule_to_apply];
            let top_state_id = self.stack.last().unwrap();
            let top_state = &self.dfa.id_to_state[top_state_id];
            let goto_state = self.dfa.transitions[top_state_id]
                .get(&Symbol::NonTerm(rule.left.clone()))
                .unwrap_or_else(|| {
                    panic!(
                        "No goto state found! state:\n{:?}, symbol: {}",
                        PrintableDFAState::new(top_state, &self.grammar),
                        rule.left.0.clone(),
                    )
                });
            self.stack.push(*goto_state);
            let result = action_fn(&mut self.actioner, &mut self.value_stack);
            self.value_stack.push(result);
            println!("stack after reduce: {:?}", self.value_stack);
        }
        true
    }

    pub fn final_value(self) -> Value {
        assert!(self.value_stack.len() == 1);
        self.value_stack.into_iter().next().unwrap()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::nfa_dfa::{NFAState, PrintableNFAState};
    use crate::tests::parse_lines;

    #[derive(Clone)]
    pub struct SimplyPDA<Tk: Hash + Eq> {
        stack: Vec<DfaStateId>,
        dfa: DFA<Tk>,
        grammar: Grammar<Tk>,
    }

    impl<Tk> SimplyPDA<Tk>
    where
        Tk: Clone + TerminalKind + Hash + Eq + Debug,
    {
        pub fn new(dfa: DFA<Tk>, grammar: Grammar<Tk>) -> Self {
            Self { stack: vec![dfa.start.clone()], dfa, grammar }
        }

        pub fn process<I: Iterator<Item = Tk>>(&mut self, mut token_stream: Peekable<I>) -> bool {
            while token_stream.peek().is_some() {
                let tk = token_stream.next().unwrap().clone();
                if !self.process_one(tk, &mut token_stream) {
                    break;
                }
            }
            for (idx, state) in self.stack.iter().enumerate() {
                println!(
                    "Stack state #{}: {:?}",
                    idx,
                    PrintableDFAState::new(&self.dfa.id_to_state[state], &self.grammar)
                );
            }

            return token_stream.peek().is_none()
                && self.stack.len() == 2
                && self.stack[0] == self.dfa.start
                && self.stack[1] == self.dfa.end;
        }

        pub fn process_one<I: Iterator<Item = Tk>>(
            &mut self,
            tk: Tk,
            token_stream: &mut Peekable<I>,
        ) -> bool {
            assert!(!self.stack.is_empty());

            // first try to shift
            // push the next state onto the stack according to the dfa transition table
            let current_state = self.stack.last().unwrap();
            if let Some(next_state) =
                self.dfa.transitions[current_state].get(&Symbol::Term(tk.clone()))
            {
                trace!("Shifted token: {:?}", tk);
                self.stack.push(next_state.clone());
            }

            // then try to reduce until it's unreduceable
            loop {
                let current_state_id = self.stack.last().unwrap();
                if !self.dfa.final_states.contains(current_state_id) {
                    break;
                }

                let current_state = &self.dfa.id_to_state[current_state_id];

                // in final state, need to reduce
                let rule_to_apply = current_state
                    .reduce_rule(&self.grammar)
                    .expect("should exist only oane reduce rule");

                // resolve conflict by looking ahead
                if let Some(follow_set) = self.dfa.conflict_resolver.get(current_state_id) {
                    if let Some(next_tk) = token_stream.peek() {
                        // not in the follow set, should not reduce
                        if !follow_set.contains(next_tk) {
                            break;
                        } else {
                            trace!(
                                "Lookahead token '{:?}' is in follow set, reducing by rule {}",
                                next_tk, rule_to_apply
                            );
                        }
                    }
                }

                let rule = &self.grammar[rule_to_apply];
                trace!("Reducing by rule: {:?}", rule);
                if rule_to_apply == 0
                    && token_stream.peek().is_none()
                    && self.stack.last().unwrap() == &self.dfa.end
                {
                    trace!("Parse done!");
                    return false;
                }

                let to_pop = rule
                    .right
                    .iter()
                    .filter(|sym| match sym {
                        Symbol::Epsilon => false,
                        _ => true,
                    })
                    .count();
                for _ in 0..to_pop {
                    self.stack.pop();
                }
                let top_state_id = self.stack.last().unwrap();
                let top_state = &self.dfa.id_to_state[top_state_id];
                let goto_state = self.dfa.transitions[top_state_id]
                    .get(&Symbol::NonTerm(rule.left.clone()))
                    .expect(&format!(
                        "No goto state found! state:\n{:?}, symbol: {}",
                        PrintableDFAState::new(top_state, &self.grammar),
                        rule.left.0.clone(),
                    ));
                self.stack.push(goto_state.clone());
            }
            true
        }
    }

    static INIT: std::sync::Once = std::sync::Once::new();
    fn setup() {
        INIT.call_once(|| {
            let _ = tracing_subscriber::fmt()
                .with_max_level(tracing::Level::TRACE)
                .with_test_writer()
                .try_init();
        });
    }

    #[test]
    fn test_exercise() {
        setup();
        // grammar:
        //      S' -> S
        //      S -> A B | A
        //      A -> a C c
        //      C -> b b C | b
        //      B -> c d

        let grammar = parse_lines(
            "S",
            vec!["S -> A B", "S -> A", "A -> a C c", "C -> b b C", "C -> b", "B -> c d"],
        );

        let dfa = DFA::build(&grammar);
        let pda = SimplyPDA::new(dfa, grammar);

        // a b b b b b c c d
        let ts = vec![
            Terminal("a".into()),
            Terminal("b".into()),
            Terminal("b".into()),
            Terminal("b".into()),
            Terminal("b".into()),
            Terminal("b".into()),
            Terminal("c".into()),
            Terminal("c".into()),
            Terminal("d".into()),
        ];

        let res = pda.clone().process(ts.into_iter().peekable());
        assert!(res);
    }

    #[allow(unused)]
    #[derive(Clone, Debug, Eq)]
    enum ExprToken {
        LParen,
        RParen,
        Plus,
        Minus,
        Star,
        Slash,
        Identifier(String),
    }

    impl PartialEq for ExprToken {
        fn eq(&self, other: &Self) -> bool {
            self.id() == other.id()
        }
    }

    impl TerminalKind for ExprToken {
        fn id(&self) -> &str {
            match self {
                ExprToken::LParen => "(",
                ExprToken::RParen => ")",
                ExprToken::Plus => "+",
                ExprToken::Minus => "-",
                ExprToken::Star => "*",
                ExprToken::Slash => "/",
                ExprToken::Identifier(_) => "id",
            }
        }
    }

    impl Hash for ExprToken {
        fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
            self.id().hash(state);
        }
    }

    impl<'a> From<&'a str> for ExprToken {
        fn from(value: &'a str) -> Self {
            match value {
                "(" => Self::LParen,
                ")" => Self::RParen,
                "+" => Self::Plus,
                "-" => Self::Minus,
                "*" => Self::Star,
                "/" => Self::Slash,
                other => Self::Identifier(other.into()),
            }
        }
    }

    #[test]
    fn test_expr() {
        setup();
        let grammar = parse_lines::<_, ExprToken>(
            "E",
            vec![
                "E -> E + T",
                "E -> T",
                "T -> T * F",
                "T -> T / F",
                "T -> F",
                "F -> ( E )",
                "F -> id",
            ],
        );

        let dfa = DFA::build(&grammar);
        let pda = SimplyPDA::new(dfa, grammar);

        let ts = vec![
            ExprToken::Identifier("a".into()),
            ExprToken::Plus,
            ExprToken::Identifier("b".into()),
            ExprToken::Star,
            ExprToken::Identifier("c".into()),
        ];
        let res = pda.clone().process(ts.into_iter().peekable());
        assert!(res);
    }

    #[should_panic]
    #[test]
    fn test_slr() {
        // S → a E c
        // S → a F d
        // S → b F c
        // S → b E d
        // E → e
        // F → e
        let grammar = parse_lines::<_, Terminal>(
            "S",
            vec!["S -> a E c", "S -> a F d", "S -> b F c", "S -> b E d", "E -> e", "F -> e"],
        );
        let dfa = DFA::build(&grammar);
        let pda = SimplyPDA::new(dfa, grammar);

        let ts = vec![Terminal("a".into()), Terminal("e".into()), Terminal("d".into())];
        let res = pda.clone().process(ts.into_iter().peekable());
        println!("Result: {}", res);
    }

    #[test]
    fn test_lalr() {
        setup();
        let grammar = parse_lines::<_, Terminal>(
            "S",
            vec!["S -> L = R", "S -> R", "L -> * R", "L -> id", "R -> L"],
        );
        let dfa = DFA::build(&grammar);
        let lookahead = dfa.build_lookahead_for_lalr(&grammar);
        for ((state_id, item), lookahead_set) in &lookahead {
            println!(
                "State {:?}, Item {:?}, Lookahead: {:?}",
                PrintableDFAState::new(&dfa.id_to_state[state_id], &grammar),
                PrintableNFAState::new(&NFAState(item.clone()), &grammar),
                lookahead_set
            );
        }
    }

    #[test]
    fn test_lalr2() {
        setup();
        let grammar = parse_lines::<_, Terminal>(
            "S",
            vec!["S -> A a", "S -> b A c", "S -> d c", "S -> b d a", "A -> d"],
        );
        let dfa = DFA::build(&grammar);
        let lookahead = dfa.build_lookahead_for_lalr(&grammar);
        for ((state_id, item), lookahead_set) in &lookahead {
            println!(
                "State {:?}, Item {:?}, Lookahead: {:?}",
                PrintableDFAState::new(&dfa.id_to_state[state_id], &grammar),
                PrintableNFAState::new(&NFAState(item.clone()), &grammar),
                lookahead_set
            );
        }
    }
}
