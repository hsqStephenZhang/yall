use core::panic;
use std::collections::{BTreeSet, HashMap, HashSet, VecDeque};
use std::fmt::Debug;
use std::hash::Hash;

use proc_macro2::TokenStream;
use quote::{format_ident, quote};

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
pub struct NFAState(pub(crate) Item);

pub struct PrintableNFAState<'a, Tk: Hash + Eq>(&'a NFAState, &'a Grammar<Tk>);

impl<'a, Tk: Hash + Eq> PrintableNFAState<'a, Tk> {
    pub fn new(state: &'a NFAState, grammar: &'a Grammar<Tk>) -> Self {
        Self(state, grammar)
    }
}

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
                if idx == grammar[rule].right.len() { Some(rule) } else { None }
            })
            .collect::<HashSet<_>>();
        if reduce_rules.len() == 1 { Some(*reduce_rules.iter().next().unwrap()) } else { None }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct DfaStateId(usize);

pub struct PrintableDFAState<'a, Tk: Hash + Eq>(&'a DFAState, &'a Grammar<Tk>);

impl<'a, Tk: Hash + Eq> PrintableDFAState<'a, Tk> {
    pub fn new(state: &'a DFAState, grammar: &'a Grammar<Tk>) -> Self {
        Self(state, grammar)
    }
}

impl<Tk: TerminalKind + Hash + Eq> std::fmt::Debug for PrintableDFAState<'_, Tk> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for nfa_state in self.0.0.iter().take(self.0.0.len() - 1) {
            write!(f, "{:?}, ", PrintableNFAState(nfa_state, self.1))?;
        }
        write!(f, "{:?}", PrintableNFAState(self.0.0.iter().last().unwrap(), self.1))?;
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
    // start state id
    pub(crate) start: DfaStateId,
    // end state id
    pub(crate) end: DfaStateId,
    // transition table
    pub(crate) transitions: HashMap<DfaStateId, HashMap<Symbol<Tk>, DfaStateId>>,
    // set of final states that contains items like A -> α•
    pub(crate) final_states: HashSet<DfaStateId>,
    pub(crate) conflict_resolver: HashMap<DfaStateId, HashSet<Tk>>,
    pub(crate) state_to_id: HashMap<DFAState, DfaStateId>,
    pub(crate) id_to_state: HashMap<DfaStateId, DFAState>,
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
        // 1. build NFA

        // 1.1 build all the transitions
        let mut transitions: HashMap<NFAState, HashMap<Symbol<Tk>, BTreeSet<NFAState>>> =
            HashMap::new();
        for (rule_num, rule) in grammar.rules.iter().enumerate() {
            for (idx, symbol) in rule.right.iter().enumerate() {
                let cur: NFAState = Item::new(rule_num, idx).into();
                let next: NFAState = Item::new(rule_num, idx + 1).into();
                transitions.entry(cur).or_default().entry(symbol.clone()).or_default().insert(next);

                // add epsilon transition if the symbol next to dot is non-terminal
                if let Symbol::NonTerm(nonterm) = symbol {
                    for (target_rule_num, _) in grammar.rules_of(nonterm) {
                        let next: NFAState = Item::new(target_rule_num, 0).into();
                        transitions
                            .entry(cur)
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

        // 2. NFA to DFA
        let get_closure = |nfa_state: NFAState| {
            let mut res =
                epsilon_closure_excluding_self.get(&nfa_state).cloned().unwrap_or_default();
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

                dfa_transitions.entry(cur_id).or_default().insert(action, next_id);

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
            .filter_map(|&state_id| {
                let state = &id_to_state[&state_id];
                let reduce_rules: HashSet<usize> = state
                    .0
                    .iter()
                    .filter_map(|nfa_state| {
                        let Item { rule, idx } = nfa_state.0;
                        if idx == grammar[rule].right.len() { Some(rule) } else { None }
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
                            symbol.name()
                        })
                        .collect::<HashSet<_>>();
                    if shift_lookahead.len() != shift_rules.len() {
                        panic!(
                            "Shift-shift conflict cannot be resolved by lookahead at state:\n{:?}",
                            PrintableDFAState(state, grammar)
                        );
                    }
                    Some((state_id, (shift_rules, *reduce_rules.iter().next().unwrap())))
                } else if reduce_rules.len() == 1 && shift_rules.len() == 1 {
                    Some((state_id, (shift_rules, *reduce_rules.iter().next().unwrap())))
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
                trace!("Inadequate DFA State #{:?}:", state_to_id.get(state).unwrap());
                for nfa_state in &state.0 {
                    trace!("    {:?}", PrintableNFAState(nfa_state, grammar));
                }
                for shift in shifts {
                    trace!("    Shift on {:?}", PrintableNFAState(&NFAState(*shift), grammar));
                }

                let rule = &grammar.rules[*reduce];
                trace!("    Reduce by rule: {:?}", rule);
                let follow = grammar.follow_set();
                let empty_set = HashSet::new();
                let followers = follow.get(&(rule.left.clone().into())).unwrap_or(&empty_set);
                let shift_syms = shifts
                    .iter()
                    .map(|item| {
                        let Item { rule, idx } = item;
                        let symbol = &grammar.rules[*rule].right[*idx];
                        symbol.clone().into_term()
                    })
                    .collect::<HashSet<_>>();
                trace!(
                    "follower set: {:?}, shift_sym: {:?}, resolved: {}\n",
                    followers,
                    shift_syms,
                    followers.intersection(&shift_syms).collect::<HashSet<_>>().is_empty()
                );
            }
        }

        // now we know that lookahead could resolve the conflicts
        // copy the follow set to DFA
        let conflict_resolver = inadequate_states
            .into_iter()
            .map(|(state, (_shift, reduce))| {
                let rule = &grammar.rules[reduce];
                let follow = grammar.follow_set();
                let empty_set = HashSet::new();
                let followers = follow.get(&(rule.left.clone().into())).unwrap_or(&empty_set);
                (state, followers.clone())
            })
            .collect();

        let end =
            *dfa_transitions[&start].get(&Symbol::NonTerm(grammar.start_sym.clone())).unwrap();

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

    pub fn build_lookahead_for_lalr(
        &self,
        grammar: &Grammar<Tk>,
    ) -> HashMap<(DfaStateId, Item), HashSet<Tk>> {
        let mut set: HashMap<(DfaStateId, Item), HashSet<Tk>> = HashMap::new();

        let could_be_empty_nonterms = grammar.emptyables();
        let could_be_empty = |syms: &[Symbol<Tk>]| -> bool {
            syms.iter().all(|sym| match sym {
                Symbol::NonTerm(nt) => could_be_empty_nonterms.contains(nt),
                Symbol::Epsilon => true,
                Symbol::Term(_) => false,
            })
        };

        let mut changed = true;
        while changed {
            changed = false;

            for &cur_state in self.transitions.keys() {
                let dfa_state = &self.id_to_state[&cur_state];
                for nfa_state in &dfa_state.0 {
                    let Item { rule, idx } = nfa_state.0;
                    let grammar_rule = &grammar.rules[rule];
                    if let Some(symbol) = grammar_rule.right.get(idx) {
                        // rule 1, propagate inside the cur_state(closure)
                        if matches!(symbol, Symbol::NonTerm(_)) {
                            let rest = &grammar_rule.right[idx + 1..];
                            let mut first_set = grammar.first_set_of_symbols(rest);
                            // inside the state, the lookahead can only be propagated if the rest could be empty
                            if could_be_empty(rest) {
                                first_set.extend(
                                    set.get(&(cur_state, nfa_state.0)).cloned().unwrap_or_default(),
                                );
                            }

                            let expansions = dfa_state.0.iter().filter(|s| {
                                let Item { rule: r, idx: i } = s.0;
                                if i == 0
                                    && let Symbol::NonTerm(nt) = &grammar_rule.right[idx]
                                {
                                    &grammar.rules[r].left == nt
                                } else {
                                    false
                                }
                            });

                            // rule 1, inside the cur_state
                            for item in expansions {
                                let key = (cur_state, item.0);
                                let entry = set.entry(key).or_default();
                                let before_size = entry.len();
                                entry.extend(first_set.iter().cloned());
                                if entry.len() > before_size {
                                    changed = true;
                                }
                            }
                        }

                        // rule 2, from cur_state to next_state
                        if let Some(next_state) = self.transitions[&cur_state].get(symbol)
                            && let Some(lookahead_set) = set.get(&(cur_state, nfa_state.0)).cloned()
                        {
                            let next_item = Item::new(rule, idx + 1);
                            let key = (*next_state, next_item);
                            let entry = set.entry(key).or_default();
                            let before_size = entry.len();
                            entry.extend(lookahead_set.iter().cloned());
                            if entry.len() > before_size {
                                changed = true;
                            }
                        }
                    }
                }
            }
        }

        // filter empty lookahead entries
        set.into_iter().filter(|(_, lookahead_set)| !lookahead_set.is_empty()).collect()
    }

    // should generate code like:
    pub fn generate_rust_code(&self, grammar: &Grammar<Tk>) -> TokenStream {
        let state_num = self.state_to_id.len();
        let start_state = self.start.0;
        let end_state = self.end.0;
        let final_states =
            self.final_states.iter().map(|DfaStateId(id)| quote! { #id }).collect::<Vec<_>>();

        let start_end_tks = quote! {
            const FINAL_STATES_SET: phf::Set<usize> = phf::phf_set! { #(#final_states),* } ;
            const START_STATE: usize = #start_state ;
            const END_STATE: usize = #end_state ;
        };

        let transition_maps = (start_state..(start_state + state_num))
            .map(|state_id| {
                let entries = match self.transitions.get(&DfaStateId(state_id)) {
                    None => vec![],
                    Some(trans_map) => trans_map
                        .iter()
                        .map(|(symbol, DfaStateId(target_id))| {
                            let sym_id = match symbol {
                                Symbol::Term(t) => t.id(),
                                Symbol::NonTerm(nt) => nt.0.as_str(),
                                Symbol::Epsilon => {
                                    panic!("Epsilon found in DFA transition, which is invalid")
                                }
                            };
                            quote! { #sym_id => #target_id }
                        })
                        .collect::<Vec<_>>(),
                };
                let name = format_ident!("TRANSITION{}", state_id);
                quote! {
                    static #name: phf::Map<&'static str, usize> = phf::phf_map! { #(#entries),* } ;
                }
            })
            .collect::<Vec<_>>();

        let transitions_array = (0..state_num)
            .map(|state_id| {
                let name = format_ident!("TRANSITION{}", state_id);
                quote! { & #name }
            })
            .collect::<Vec<_>>();

        let transition = quote! {
            static TRANSITIONS: &[&phf::Map<&'static str, usize>] = &[ #(#transitions_array),* ] ;
        };

        let reduce_table = (0..state_num)
            .map(|state_id| {
                if let Some(reduce_rule) =
                    self.id_to_state[&DfaStateId(state_id)].reduce_rule(grammar)
                {
                    quote! { Some(#reduce_rule) }
                } else {
                    quote! { None }
                }
            })
            .collect::<Vec<_>>();
        let reduce_table = quote! {
            const REDUCE_RULE: &[Option<usize>] = &[ #(#reduce_table),* ] ;
        };

        let rules_table = grammar.rules.iter().map(|rule| {
            let left = &rule.left.0;
            let right = rule.right.iter().map(|sym| match sym {
                Symbol::Term(t) => {
                    let id = t.id();
                    quote! { #id }
                }
                Symbol::NonTerm(nt) => {
                    let id = &nt.0;
                    quote! { #id }
                }
                Symbol::Epsilon => quote! { "" },
            });
            quote! { (#left, &[#(#right),*]) }
        });

        let rules_table = quote! {
            const RULES: &[(&str, &[&str])] = &[ #(#rules_table),* ] ;
        };

        let lookup_item = self.conflict_resolver.iter().map(|(DfaStateId(state_id), set)| {
            let lookaheads = set.iter().map(|tk| {
                let id = tk.id();
                quote! { #id }
            });
            quote! {
                #state_id => phf::phf_set!{ #(#lookaheads),* }
            }
        });
        
        let lookup_set = quote! {
            static CONFLICT_RESOLVER: phf::Map<usize, phf::Set<&'static str>> = phf::phf_map! {
                #(#lookup_item),*
            } ;
        };

        quote! {
            #start_end_tks

            #(#transition_maps)*

            #transition

            #reduce_table

            #rules_table

            #lookup_set
        }
    }
}
