use core::panic;

use tracing::trace;

use crate::grammar::TerminalKind;

pub struct ParseContext {
    pub start_state: usize,
    pub end_state: usize,
    pub is_final_state: fn(usize) -> bool,
    pub transitions: fn(usize, &str) -> Option<usize>,
    pub reduce_rule: &'static [Option<usize>],
    pub rules: &'static [(&'static str, &'static [&'static str])],
    pub lookahead: fn(usize, Option<&str>) -> Option<usize>,
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
        while let Some(tk) = token_stream.next() {
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
        trace!("handling token: {:?}", tk);
        assert!(!self.stack.is_empty());

        let mut changed = false;

        // first try to shift
        // push the next state onto the stack according to the dfa transition table
        let current_state = self.stack.last().unwrap();
        let transition = (ctx.transitions)(*current_state, tk.id());
        if let Some(next_state) = transition {
            trace!("Shifted token: {:?}", tk);
            self.stack.push(next_state);
            self.value_stack.push(tk.into());
            changed = true;
            trace!("stack after shift: {:?}", self.value_stack);
            trace!("pda stack after shift: {:?}", self.stack);
        }

        // then try to reduce until it's unreduceable
        loop {
            let current_state_id = self.stack.last().unwrap();

            if !(ctx.is_final_state)(*current_state_id) {
                break;
            }

            // in final state, need to reduce
            let rule_to_apply = match ctx.reduce_rule[*current_state_id] {
                Some(rule_idx) => Some(rule_idx),
                None => (ctx.lookahead)(*current_state_id, token_stream.peek().map(|tk| tk.id())),
            };

            let rule_to_apply = match rule_to_apply {
                Some(idx) => idx,
                None => {
                    break;
                }
            };

            trace!("Reducing by rule {}", rule_to_apply);
            if rule_to_apply == 0
                && token_stream.peek().is_none()
                && *self.stack.last().unwrap() == ctx.end_state
            {
                trace!("Parse done!");
                return changed;
            }

            let to_pop = ctx.rules[rule_to_apply].1.len();
            for _ in 0..to_pop {
                self.stack.pop();
            }
            let action_fn = self.actions[rule_to_apply];
            let top_state_id = self.stack.last().unwrap();
            let rule_left = ctx.rules[rule_to_apply].0;
            let goto_state = (ctx.transitions)(*top_state_id, rule_left)
                .unwrap_or_else(|| panic!("No goto state found! state: {}", top_state_id));
            self.stack.push(goto_state);
            let result = action_fn(&mut self.actioner, &mut self.value_stack);
            self.value_stack.push(result);
            changed = true;
            trace!("stack after reduce: {:?}", self.value_stack);
            trace!("pda stack after reduce: {:?}", self.stack);
        }
        changed
    }

    pub fn final_value(self) -> Value {
        assert!(self.value_stack.len() == 1);
        self.value_stack.into_iter().next().unwrap()
    }
}
