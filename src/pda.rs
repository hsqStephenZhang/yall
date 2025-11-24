use core::panic;
use std::{
    collections::{BTreeSet, HashMap, HashSet, VecDeque},
    fmt::Debug,
    hash::Hash,
};

use tracing::trace;

use crate::grammar::*;

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

#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct NFAState(Item);

pub struct PrintableNFAState<'a, Tk: Hash + Eq>(&'a NFAState, &'a Grammar<Tk>);

impl<Tk: TerminalKind + Hash + Eq> std::fmt::Debug for PrintableNFAState<'_, Tk> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let rule = &self.1.rules[(self.0).0.rule];
        let dot_pos = self.0.0.idx;
        write!(f, "{} -> ", rule.left.0)?;
        for (idx, sym) in rule.right.iter().enumerate() {
            if idx == dot_pos {
                write!(f, "• ")?;
            }
            match sym {
                Symbol::Term(t) => write!(f, "'{}' ", t.id())?,
                Symbol::NonTerm(nt) => write!(f, "{} ", nt.0)?,
                Symbol::Epsilon => write!(f, "ε ")?,
            }
        }
        if dot_pos == rule.right.len() {
            write!(f, "•")?;
        }
        Ok(())
    }
}

impl From<Item> for NFAState {
    fn from(value: Item) -> Self {
        Self(value)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct DFAState(BTreeSet<NFAState>);

impl DFAState {
    pub fn reduce_rule(&self, grammar: &Grammar<impl Hash + Eq>) -> Option<usize> {
        let reduce_rules = self
            .0
            .iter()
            .filter_map(|nfa_state| {
                let Item { rule, idx } = nfa_state.0;
                if idx == grammar[rule].right.len() {
                    Some(rule)
                } else {
                    None
                }
            })
            .collect::<HashSet<_>>();
        if reduce_rules.len() == 1 {
            Some(*reduce_rules.iter().next().unwrap())
        } else {
            None
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct DfaStateId(usize);

pub struct PrintableDFAState<'a, Tk: Hash + Eq>(&'a DFAState, &'a Grammar<Tk>);

impl<Tk: TerminalKind + Hash + Eq> std::fmt::Debug for PrintableDFAState<'_, Tk> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for nfa_state in &self.0.0 {
            writeln!(f, "{:?}", PrintableNFAState(nfa_state, self.1))?;
        }
        Ok(())
    }
}

impl From<BTreeSet<NFAState>> for DFAState {
    fn from(value: BTreeSet<NFAState>) -> Self {
        Self(value)
    }
}
#[allow(unused)]
#[derive(Clone, Debug)]
pub struct DFA<Tk: Hash + Eq> {
    start: DfaStateId,
    end: DfaStateId,
    transitions: HashMap<DfaStateId, HashMap<Symbol<Tk>, DfaStateId>>,
    final_states: HashSet<DfaStateId>,
    // from inadequate state to follow set of the reduce rule
    conflict_resolver: HashMap<DfaStateId, HashSet<Tk>>,
    state_to_id: HashMap<DFAState, DfaStateId>,
    id_to_state: HashMap<DfaStateId, DFAState>,
}

pub struct Conflict {
    // item for shift
    pub shift: Item,
    // rule number
    pub reduce: usize,
}

impl<Tk: Clone + TerminalKind + Hash + Eq + Debug> DFA<Tk> {
    // from a NFA to DFA
    pub fn build(grammar: &Grammar<Tk>) -> DFA<Tk> {
        // let pseudo_start = NonTerminal("S_prime".into());

        // 1. build NFA

        // 1.1 build all the transitions
        let mut transitions: HashMap<NFAState, HashMap<Symbol<Tk>, BTreeSet<NFAState>>> =
            HashMap::new();
        for (rule_num, rule) in grammar.rules.iter().enumerate() {
            for (idx, symbol) in rule.right.iter().enumerate() {
                let cur: NFAState = Item::new(rule_num, idx).into();
                let next: NFAState = Item::new(rule_num, idx + 1).into();
                transitions
                    .entry(cur.clone())
                    .or_default()
                    .entry(symbol.clone())
                    .or_default()
                    .insert(next);

                // add epsilon transition if the symbol next to dot is non-terminal
                if let Symbol::NonTerm(nonterm) = symbol {
                    for (target_rule_num, _) in grammar.rules_of(nonterm) {
                        let next: NFAState = Item::new(target_rule_num, 0).into();
                        transitions
                            .entry(cur.clone())
                            .or_default()
                            .entry(Symbol::Epsilon)
                            .or_default()
                            .insert(next);
                    }
                }
            }
        }

        // 1.2 now all the transitions for the NFA is built, let's calculate the epsilon-closures
        let mut epsilon_closure_excluding_self: HashMap<NFAState, BTreeSet<NFAState>> =
            HashMap::new();

        let empty_set = BTreeSet::new();
        for (rule_num, rule) in grammar.rules.iter().enumerate() {
            for idx in 0..rule.right.len() {
                let mut closure = BTreeSet::new();
                let state = NFAState::from(Item::new(rule_num, idx));
                let mut worklist = VecDeque::from([state]);
                let mut visited = BTreeSet::new();
                while !worklist.is_empty() {
                    let cur = worklist.pop_front().unwrap();
                    if !visited.insert(cur) {
                        continue;
                    }

                    let epsilon_nexts = transitions
                        .get(&cur)
                        .and_then(|m| m.get(&Symbol::Epsilon))
                        .unwrap_or(&empty_set);

                    closure.extend(epsilon_nexts.iter());

                    for next in epsilon_nexts {
                        if let Some(calculated) = epsilon_closure_excluding_self.get(next) {
                            closure.extend(calculated);
                        } else {
                            worklist.push_back(*next);
                        }
                    }
                }

                epsilon_closure_excluding_self.insert(state, closure);
            }
        }

        // pretty print closure
        // #[cfg(debug_assertions)]
        // {
        //     for (state, closure) in epsilon_closure_excluding_self
        //         .iter()
        //         .filter(|(_, v)| !v.is_empty())
        //     {
        //         println!("{:?} closure:", PrintableNFAState(state, grammar));
        //         for st in closure {
        //             println!("    {:?}", PrintableNFAState(st, grammar));
        //         }
        //     }
        // }

        // 2. NFA to DFA
        let get_closure = |nfa_state: NFAState| {
            let mut res = epsilon_closure_excluding_self
                .get(&nfa_state)
                .cloned()
                .unwrap_or_default();
            res.insert(nfa_state);
            res
        };

        let mut state_id_counter = 0;
        let mut id_to_state = HashMap::<DfaStateId, DFAState>::new();
        let mut state_to_id = HashMap::<DFAState, DfaStateId>::new();
        let mut get_or_new_state_id = |state: &DFAState| {
            if let Some(id) = state_to_id.get(state) {
                *id
            } else {
                let id = DfaStateId(state_id_counter);
                state_id_counter += 1;
                state_to_id.insert(state.clone(), id);
                id_to_state.insert(id, state.clone());
                id
            }
        };

        let mut dfa_transitions: HashMap<DfaStateId, HashMap<Symbol<Tk>, DfaStateId>> =
            HashMap::new();
        let mut final_states = HashSet::new();

        let start_state = DFAState::from(get_closure(Item::new(0, 0).into()));
        let start = get_or_new_state_id(&start_state);

        let mut visited = HashSet::new();
        let mut worklist = VecDeque::from([start_state.clone()]);
        while !worklist.is_empty() {
            let cur = worklist.pop_front().unwrap();
            let cur_id = get_or_new_state_id(&cur);
            if !visited.insert(cur_id) {
                continue;
            }
            // mark as final state
            if cur.0.iter().any(|nfa_state| {
                let Item { rule, idx } = nfa_state.0;
                idx == grammar[rule].right.len()
            }) {
                final_states.insert(cur_id);
            }

            let mut all_actions = HashSet::new();

            for nfa_state in &cur.0 {
                let Item { rule, idx } = nfa_state.0;
                if idx < grammar[rule].right.len() {
                    all_actions.insert(grammar[rule].right[idx].clone());
                }
            }

            for action in all_actions {
                let mut next_dfa_state = BTreeSet::new();

                for nfa_state in &cur.0 {
                    let Item { rule, idx } = nfa_state.0;
                    if idx < grammar[rule].right.len() && grammar[rule].right[idx] == action {
                        let next_nfa_state = NFAState::from(Item::new(rule, idx + 1));
                        next_dfa_state.extend(get_closure(next_nfa_state));
                    }
                }

                let next_id = get_or_new_state_id(&DFAState(next_dfa_state.clone()));

                dfa_transitions
                    .entry(cur_id)
                    .or_default()
                    .insert(action, next_id);

                worklist.push_back(next_dfa_state.into());
            }
        }

        #[cfg(debug_assertions)]
        {
            use std::collections::BTreeMap;

            let print_order = BTreeMap::from_iter(state_to_id.iter().map(|(k, v)| (*v, k)));
            for (id, state) in print_order {
                tracing::trace!("DFA State #{:?}:", id);
                tracing::trace!("{:?}", PrintableDFAState(state, grammar));
            }
        }

        // mark all inadequate states
        let inadequate_states: HashMap<DfaStateId, (HashSet<Item>, usize)> = final_states
            .iter()
            .filter_map(|state_id| {
                let state = &id_to_state[state_id];
                let reduce_rules: HashSet<usize> = state
                    .0
                    .iter()
                    .filter_map(|nfa_state| {
                        let Item { rule, idx } = nfa_state.0;
                        if idx == grammar[rule].right.len() {
                            Some(rule)
                        } else {
                            None
                        }
                    })
                    .collect();
                let shift_rules: HashSet<Item> = state
                    .0
                    .iter()
                    .filter_map(|nfa_state| {
                        let Item { rule, idx } = nfa_state.0;
                        if idx < grammar[rule].right.len() {
                            let next_sym = &grammar[rule].right[idx];
                            if matches!(next_sym, Symbol::Term(_)) {
                                Some(nfa_state.0)
                            } else {
                                None
                            }
                        } else {
                            None
                        }
                    })
                    .collect::<HashSet<_>>();
                if reduce_rules.len() > 1 {
                    panic!(
                        "Reduce-reduce conflict detected at state:\n{:?}",
                        PrintableDFAState(state, grammar)
                    );
                } else if shift_rules.len() > 1 {
                    let shift_lookahead = shift_rules
                        .iter()
                        .map(|item| {
                            let Item { rule, idx } = item;
                            let symbol = &grammar.rules[*rule].right[*idx];
                            let expect = symbol.name();
                            expect
                        })
                        .collect::<HashSet<_>>();
                    if shift_lookahead.len() != shift_rules.len() {
                        panic!(
                            "Shift-shift conflict cannot be resolved by lookahead at state:\n{:?}",
                            PrintableDFAState(state, grammar)
                        );
                    }
                    Some((
                        state_id.clone(),
                        (shift_rules, *reduce_rules.iter().next().unwrap()),
                    ))
                } else if reduce_rules.len() == 1 && shift_rules.len() == 1 {
                    Some((
                        state_id.clone(),
                        (shift_rules, *reduce_rules.iter().next().unwrap()),
                    ))
                } else {
                    None
                }
            })
            .collect::<HashMap<_, _>>();

        #[cfg(debug_assertions)]
        {
            use tracing::trace;
            for (state_id, (shifts, reduce)) in &inadequate_states {
                let state = &id_to_state[state_id];
                trace!(
                    "Inadequate DFA State #{:?}:",
                    state_to_id.get(state).unwrap()
                );
                for nfa_state in &state.0 {
                    trace!("    {:?}", PrintableNFAState(nfa_state, grammar));
                }
                for shift in shifts {
                    trace!(
                        "    Shift on {:?}",
                        PrintableNFAState(&NFAState(shift.clone()), grammar)
                    );
                }

                let rule = &grammar.rules[*reduce];
                trace!("    Reduce by rule: {:?}", rule);
                let follow = grammar.first_follow_set().follow();
                let empty_set = HashSet::new();
                let followers = follow
                    .get(&(rule.left.clone().into()))
                    .unwrap_or(&empty_set);
                let shift_syms = shifts
                    .iter()
                    .map(|item| {
                        let Item { rule, idx } = item;
                        let symbol = &grammar.rules[*rule].right[*idx];
                        symbol.clone().into_term()
                    })
                    .collect::<HashSet<_>>();
                trace!(
                    "follower set: {:?}, shift_sym: {:?}, resolved: {}",
                    followers,
                    shift_syms,
                    followers
                        .intersection(&shift_syms)
                        .collect::<HashSet<_>>()
                        .is_empty()
                );
                println!();
            }
        }

        // now we know that lookahead could resolve the conflicts
        // copy the follow set to DFA
        let conflict_resolver = inadequate_states
            .into_iter()
            .map(|(state, (_shift, reduce))| {
                let rule = &grammar.rules[reduce];
                let first_follow = grammar.first_follow_set();
                let empty_set = HashSet::new();
                let followers = first_follow
                    .follow()
                    .get(&(rule.left.clone().into()))
                    .unwrap_or(&empty_set);
                (state, followers.clone())
            })
            .collect();

        let end = dfa_transitions[&start]
            .get(&Symbol::NonTerm(grammar.start_sym.clone()))
            .unwrap()
            .clone();

        // let first_follow = grammar.first_follow_set();
        DFA {
            start,
            end,
            transitions: dfa_transitions,
            final_states,
            conflict_resolver,
            state_to_id,
            id_to_state,
        }
    }
}

pub struct TokenStream<Tk> {
    tokens: Vec<Tk>,
    position: usize,
}

impl<Tk> TokenStream<Tk> {
    pub fn new(tokens: Vec<Tk>) -> Self {
        Self {
            tokens,
            position: 0,
        }
    }

    pub fn next(&mut self) -> Option<&Tk> {
        if self.position < self.tokens.len() {
            let tk = &self.tokens[self.position];
            self.position += 1;
            Some(tk)
        } else {
            None
        }
    }

    pub fn peek(&self) -> Option<&Tk> {
        if self.position < self.tokens.len() {
            Some(&self.tokens[self.position])
        } else {
            None
        }
    }

    pub fn is_eof(&self) -> bool {
        self.position >= self.tokens.len()
    }
}

#[derive(Clone)]
pub struct PDA<'a, Tk: Hash + Eq, Value> {
    stack: Vec<DfaStateId>,
    value_stack: Vec<Value>,
    dfa: DFA<Tk>,
    grammar: Grammar<Tk>,
    actions: &'a [fn(&mut Vec<Value>) -> Value],
}

impl<'a, Tk, Value> PDA<'a, Tk, Value>
where
    Tk: Clone + TerminalKind + Hash + Eq + Debug,
    Value: From<Tk> + Debug,
{
    pub fn new(
        dfa: DFA<Tk>,
        grammar: Grammar<Tk>,
        actions: &'a [fn(&mut Vec<Value>) -> Value],
    ) -> Self {
        Self {
            stack: vec![dfa.start.clone()],
            value_stack: vec![],
            dfa,
            grammar,
            actions,
        }
    }

    pub fn process(&mut self, mut token_stream: TokenStream<Tk>) -> bool {
        while !token_stream.is_eof() {
            let tk = token_stream.next().unwrap().clone();
            if !self.process_one(tk, &token_stream) {
                break;
            }
        }
        for (idx, state) in self.stack.iter().enumerate() {
            println!(
                "Stack state #{}: {:?}",
                idx,
                PrintableDFAState(&self.dfa.id_to_state[state], &self.grammar)
            );
        }

        return token_stream.is_eof()
            && self.stack.len() == 2
            && self.stack[0] == self.dfa.start
            && self.stack[1] == self.dfa.end;
    }

    pub fn process_one(&mut self, tk: Tk, token_stream: &TokenStream<Tk>) -> bool {
        assert!(!self.stack.is_empty());

        // first try to shift
        // push the next state onto the stack according to the dfa transition table
        let current_state = self.stack.last().unwrap();
        if let Some(next_state) = self.dfa.transitions[current_state].get(&Symbol::Term(tk.clone()))
        {
            self.stack.push(next_state.clone());
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
            trace!("Reducing by rule {}: {:?}", rule_to_apply, rule);
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
            let action_fn = self.actions[rule_to_apply];
            let top_state_id = self.stack.last().unwrap();
            let top_state = &self.dfa.id_to_state[top_state_id];
            let goto_state = self.dfa.transitions[top_state_id]
                .get(&Symbol::NonTerm(rule.left.clone()))
                .expect(&format!(
                    "No goto state found! state:\n{:?}, symbol: {}",
                    PrintableDFAState(top_state, &self.grammar),
                    rule.left.0.clone(),
                ));
            self.stack.push(goto_state.clone());
            let result = action_fn(&mut self.value_stack);
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
            Self {
                stack: vec![dfa.start.clone()],
                dfa,
                grammar,
            }
        }

        pub fn process(&mut self, mut token_stream: TokenStream<Tk>) -> bool {
            while !token_stream.is_eof() {
                let tk = token_stream.next().unwrap().clone();
                if !self.process_one(tk, &token_stream) {
                    break;
                }
            }
            for (idx, state) in self.stack.iter().enumerate() {
                println!(
                    "Stack state #{}: {:?}",
                    idx,
                    PrintableDFAState(&self.dfa.id_to_state[state], &self.grammar)
                );
            }

            return token_stream.is_eof()
                && self.stack.len() == 2
                && self.stack[0] == self.dfa.start
                && self.stack[1] == self.dfa.end;
        }

        pub fn process_one(&mut self, tk: Tk, token_stream: &TokenStream<Tk>) -> bool {
            assert!(!self.stack.is_empty());

            // first try to shift
            // push the next state onto the stack according to the dfa transition table
            let current_state = self.stack.last().unwrap();
            if let Some(next_state) =
                self.dfa.transitions[current_state].get(&Symbol::Term(tk.clone()))
            {
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
                    .expect("should exist only one reduce rule");

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
                        PrintableDFAState(top_state, &self.grammar),
                        rule.left.0.clone(),
                    ));
                self.stack.push(goto_state.clone());
            }
            true
        }
    }
    use super::*;

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
            vec![
                "S -> A B",
                "S -> A",
                "A -> a C c",
                "C -> b b C",
                "C -> b",
                "B -> c d",
            ],
        );

        let dfa = DFA::build(&grammar);
        let pda = SimplyPDA::new(dfa, grammar);

        // let ts = TokenStream::new(vec![
        //     Terminal("a".into()),
        //     Terminal("b".into()),
        //     Terminal("c".into()),
        // ]);

        // let res = pda.clone().process(ts);
        // println!("Result: {}", res);

        // a b b b b b c c d
        let ts = TokenStream::new(vec![
            Terminal("a".into()),
            Terminal("b".into()),
            Terminal("b".into()),
            Terminal("b".into()),
            Terminal("b".into()),
            Terminal("b".into()),
            Terminal("c".into()),
            Terminal("c".into()),
            Terminal("d".into()),
        ]);

        let res = pda.clone().process(ts);
        println!("Result: {}", res);
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

        let ts = TokenStream::new(vec![
            ExprToken::Identifier("a".into()),
            ExprToken::Plus,
            ExprToken::Identifier("b".into()),
            ExprToken::Star,
            ExprToken::Identifier("c".into()),
        ]);
        let res = pda.clone().process(ts);
        println!("Result: {}", res);
    }

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
            vec![
                "S -> a E c",
                "S -> a F d",
                "S -> b F c",
                "S -> b E d",
                "E -> e",
                "F -> e",
            ],
        );
        let dfa = DFA::build(&grammar);
        let pda = SimplyPDA::new(dfa, grammar);

        let ts = TokenStream::new(vec![
            Terminal("a".into()),
            Terminal("e".into()),
            Terminal("d".into()),
        ]);
        let res = pda.clone().process(ts);
        println!("Result: {}", res);
    }
}
