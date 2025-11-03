use std::collections::{BTreeSet, HashMap, HashSet, VecDeque};

use crate::grammar::*;

#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct NFAState(Item);

pub struct PrintableNFAState<'a>(&'a NFAState, &'a Grammar);

impl std::fmt::Debug for PrintableNFAState<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let rule = &self.1.rules[(self.0).0.rule];
        let dot_pos = self.0.0.idx;
        write!(f, "{} -> ", rule.left.0)?;
        for (idx, sym) in rule.right.iter().enumerate() {
            if idx == dot_pos {
                write!(f, "• ")?;
            }
            match sym {
                Symbol::Term(t) => write!(f, "'{}' ", t.0)?,
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

impl From<BTreeSet<NFAState>> for DFAState {
    fn from(value: BTreeSet<NFAState>) -> Self {
        Self(value)
    }
}

#[derive(Clone, Debug)]
pub struct DFA {
    transitions: HashMap<DFAState, HashMap<Symbol, DFAState>>,
    final_states: HashSet<DFAState>,
    state_ids_map: HashMap<DFAState, usize>,
}

impl DFA {
    // from a NFA to DFA
    pub fn build(grammar: &Grammar) -> DFA {
        // let pseudo_start = NonTerminal("S_prime".into());

        // 1. build NFA

        // 1.1 build all the transitions
        let mut transitions: HashMap<NFAState, HashMap<Symbol, BTreeSet<NFAState>>> =
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
        let mut state_ids_map = HashMap::<DFAState, usize>::new();
        let mut get_or_new_state_id = |state: &DFAState| {
            if let Some(id) = state_ids_map.get(state) {
                *id
            } else {
                let id = state_id_counter;
                state_id_counter += 1;
                state_ids_map.insert(state.clone(), id);
                id
            }
        };

        let mut dfa_transitions: HashMap<DFAState, HashMap<Symbol, DFAState>> = HashMap::new();
        let mut final_states = HashSet::new();

        let start = DFAState::from(get_closure(Item::new(0, 0).into()));
        let _ = get_or_new_state_id(&start);

        let mut visited = HashSet::new();
        let mut worklist = VecDeque::from([start]);
        while !worklist.is_empty() {
            let cur = worklist.pop_front().unwrap();
            let cur_state_id = get_or_new_state_id(&cur);
            if !visited.insert(cur_state_id) {
                continue;
            }
            // mark as final state
            if cur.0.iter().any(|nfa_state| {
                let Item { rule, idx } = nfa_state.0;
                idx == grammar[rule].right.len()
            }) {
                final_states.insert(cur.clone());
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

                dfa_transitions
                    .entry(cur.clone())
                    .or_default()
                    .insert(action, next_dfa_state.clone().into());

                worklist.push_back(next_dfa_state.into());
            }
        }

        #[cfg(debug_assertions)]
        {
            use std::collections::BTreeMap;

            let print_order = BTreeMap::from_iter(state_ids_map.iter().map(|(k, v)| (*v, k)));
            for (id, state) in print_order {
                println!("DFA State #{}:", id);
                for nfa_state in &state.0 {
                    println!("    {:?}", PrintableNFAState(nfa_state, grammar));
                }
            }
        }

        DFA {
            transitions: dfa_transitions,
            final_states,
            state_ids_map,
        }
    }
}

#[derive(Clone, Debug)]
pub struct PDA {
    stack: Vec<DFAState>,
    dfa: DFA,
    grammar: Grammar,
}

impl PDA {
    pub fn process(&mut self, token_stream: Vec<Terminal>) {
        for tk in token_stream {
            self.process_one(tk);
        }
    }

    pub fn process_one(&mut self, tk: Terminal) {
        assert!(!self.stack.is_empty());

        // first try to shift
        // push the next state onto the stack according to the dfa transition table
        let current_state = self.stack.last().unwrap();
        if let Some(next_state) = self.dfa.transitions[current_state].get(&Symbol::Term(tk.clone()))
        {
            self.stack.push(next_state.clone());
        }

        // then try to reduce until it's unreduceable
        loop {
            let current_state = self.stack.last().unwrap();
            if !self.dfa.final_states.contains(current_state) {
                break;
            }
            // in final state, need to reduce
            let rule_to_apply = {
                // find which rule to apply
                let possible_rules: Vec<usize> = current_state
                    .0
                    .iter()
                    .filter_map(|nfa_state| {
                        let Item { rule, idx } = nfa_state.0;
                        if idx == self.grammar[rule].right.len() {
                            Some(rule)
                        } else {
                            None
                        }
                    })
                    .collect();
                assert!(possible_rules.len() == 1, "Ambiguous reduce actions!");
                possible_rules[0]
            };
            let rule = &self.grammar[rule_to_apply];
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
            let top_state = self.stack.last().unwrap();
            let goto_state = self.dfa.transitions[top_state]
                .get(&Symbol::NonTerm(rule.left.clone()))
                .expect("No goto state found!");
            self.stack.push(goto_state.clone());
        }
    }
}

pub struct PDABuilder {
    grammar: Grammar,
}

impl PDABuilder {
    pub fn build() -> PDA {
        // 1. from the grammar to characteristic NDFA
        // 2. from characteristic NDFA to DFA

        // 3. mark all inadequate states, add look ahead(conflict resolving) for at these states

        // 4. build the PDA with the DFA

        todo!()
    }
}

#[cfg(test)]
mod tests {

    use super::*;

    #[test]
    fn t1() {
        let s_prime = NonTerminal::from("S'");
        let s = NonTerminal::from("S");
        let a = NonTerminal::from("A");
        let b = NonTerminal::from("B");
        let c = NonTerminal::from("C");

        let grammar = Grammar {
            start_sym: s_prime.clone(),
            rules: vec![
                // S->A
                Rule {
                    left: s_prime.clone(),
                    right: vec![s.clone().into()],
                },
                // S -> A B
                Rule {
                    left: s.clone(),
                    right: vec![a.clone().into(), b.clone().into()],
                },
                // S->A
                Rule {
                    left: s.clone(),
                    right: vec![a.clone().into()],
                },
                // A -> a C c
                Rule {
                    left: a.clone(),
                    right: vec![Terminal('a').into(), c.clone().into(), Terminal('c').into()],
                },
                // C -> b b C
                Rule {
                    left: c.clone(),
                    right: vec![Terminal('b').into(), Terminal('b').into(), c.clone().into()],
                },
                // C -> b
                Rule {
                    left: c.clone(),
                    right: vec![Terminal('b').into()],
                },
                // B -> c d
                Rule {
                    left: b.clone(),
                    right: vec![Terminal('c').into(), Terminal('d').into()],
                },
            ],
        };

        let _ = DFA::build(&grammar);
    }
}
