use tracing::trace;

use crate::grammar::TerminalKind;

pub struct ParseContext<'a> {
    pub start_state: usize,
    pub end_state: usize,
    pub final_states: phf::Set<usize>,
    pub transitions: &'static [&'static phf::Map<&'static str, usize>],
    pub reduce_rule: &'static [Option<usize>],
    pub rules: &'static [(&'static str, &'static [&'static str])],
    pub conflict_resolver: &'a phf::Map<usize, phf::Set<&'static str>>,
}

#[derive(Clone)]
pub struct PdaImpl<'a, Value, Actioner> {
    stack: Vec<usize>,
    value_stack: Vec<Value>,
    actioner: Actioner,
    actions: &'a [fn(&mut Actioner, &mut Vec<Value>) -> Value],
}

impl<'a, Value, Actioner> PdaImpl<'a, Value, Actioner> {
    pub fn new(
        start_state: usize,
        actioner: Actioner,
        actions: &'a [fn(&mut Actioner, &mut Vec<Value>) -> Value],
    ) -> Self {
        Self { stack: vec![start_state], value_stack: vec![], actioner, actions }
    }

    pub fn process<Tk, I: Iterator<Item = Tk>>(
        &mut self,
        mut token_stream: std::iter::Peekable<I>,
        ctx: &ParseContext,
    ) -> bool
    where
        Tk: std::fmt::Debug + TerminalKind,
        Value: From<Tk> + std::fmt::Debug,
    {
        while token_stream.peek().is_some() {
            let tk = token_stream.next().unwrap();
            if !self.process_one(tk, &mut token_stream, ctx) {
                break;
            }
        }

        token_stream.peek().is_none()
            && self.stack.len() == 2
            && self.stack[0] == ctx.start_state
            && self.stack[1] == ctx.end_state
    }

    pub fn process_one<Tk, I: Iterator<Item = Tk>>(
        &mut self,
        tk: Tk,
        token_stream: &mut std::iter::Peekable<I>,
        ctx: &ParseContext,
    ) -> bool
    where
        Tk: std::fmt::Debug + TerminalKind,
        Value: From<Tk> + std::fmt::Debug,
    {
        println!("handling token: {:?}", tk);
        assert!(!self.stack.is_empty());

        // first try to shift
        // push the next state onto the stack according to the dfa transition table
        let current_state = self.stack.last().unwrap();
        let transition = ctx.transitions[*current_state];
        if let Some(next_state) = transition.get(tk.id()) {
            trace!("Shifted token: {:?}", tk);
            self.stack.push(*next_state);
            self.value_stack.push(tk.into());
            trace!("stack after shift: {:?}", self.value_stack);
            trace!("pda stack after shift: {:?}", self.stack);
        }

        // then try to reduce until it's unreduceable
        loop {
            let current_state_id = self.stack.last().unwrap();

            if !ctx.final_states.contains(current_state_id) {
                break;
            }

            // in final state, need to reduce
            let rule_to_apply = ctx.reduce_rule[*current_state_id].unwrap();

            // resolve conflict by looking ahead
            if let Some(follow_set) = ctx.conflict_resolver.get(current_state_id)
                && let Some(next_tk) = token_stream.peek()
            {
                // not in the follow set, should not reduce
                if !follow_set.contains(next_tk.id()) {
                    break;
                } else {
                    trace!(
                        "Lookahead token '{:?}' is in follow set, reducing by rule {}",
                        next_tk, rule_to_apply
                    );
                }
            }

            trace!("Reducing by rule {}", rule_to_apply);
            if rule_to_apply == 0
                && token_stream.peek().is_none()
                && *self.stack.last().unwrap() == ctx.end_state
            {
                trace!("Parse done!");
                return false;
            }

            let to_pop = ctx.rules[rule_to_apply].1.len();
            for _ in 0..to_pop {
                self.stack.pop();
            }
            let action_fn = self.actions[rule_to_apply];
            let top_state_id = self.stack.last().unwrap();
            let transition = ctx.transitions[*top_state_id];
            let rule_left = ctx.rules[rule_to_apply].0;
            let goto_state = transition
                .get(rule_left)
                .unwrap_or_else(|| panic!("No goto state found! state: {}", top_state_id));
            self.stack.push(*goto_state);
            let result = action_fn(&mut self.actioner, &mut self.value_stack);
            self.value_stack.push(result);
            trace!("stack after reduce: {:?}", self.value_stack);
            trace!("pda stack after reduce: {:?}", self.stack);
        }
        true
    }

    pub fn final_value(self) -> Value {
        assert!(self.value_stack.len() == 1);
        self.value_stack.into_iter().next().unwrap()
    }
}
