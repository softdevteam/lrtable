// Copyright (c) 2017 King's College London
// created by the Software Development Team <http://soft-dev.org/>
//
// The Universal Permissive License (UPL), Version 1.0
//
// Subject to the condition set forth below, permission is hereby granted to any person obtaining a
// copy of this software, associated documentation and/or data (collectively the "Software"), free
// of charge and under any and all copyright rights in the Software, and any and all patent rights
// owned or freely licensable by each licensor hereunder covering either (i) the unmodified
// Software as contributed to or provided by such licensor, or (ii) the Larger Works (as defined
// below), to deal in both
//
// (a) the Software, and
// (b) any piece of software and/or hardware listed in the lrgrwrks.txt file
// if one is included with the Software (each a "Larger Work" to which the Software is contributed
// by such licensors),
//
// without restriction, including without limitation the rights to copy, create derivative works
// of, display, perform, and distribute the Software and make, use, sell, offer for sale, import,
// export, have made, and have sold the Software and the Larger Work(s), and to sublicense the
// foregoing rights on either these or other terms.
//
// This license is subject to the following condition: The above copyright notice and either this
// complete permission notice or at a minimum a reference to the UPL must be included in all copies
// or substantial portions of the Software.
//
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING
// BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
// NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
// DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
// OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

use std::collections::hash_map::{Entry, HashMap, OccupiedEntry};
use std::hash::BuildHasherDefault;
use std::fmt;

use cfgrammar::{Grammar, PIdx, NTIdx, SIdx, Symbol, TIdx};
use cfgrammar::yacc::{AssocKind, YaccGrammar};
use fnv::FnvHasher;
use vob::{IterSetBits, Vob};

use StIdx;
use stategraph::StateGraph;

/// The various different possible Yacc parser errors.
#[derive(Debug)]
pub enum StateTableErrorKind {
    AcceptReduceConflict
}

/// Any error from the Yacc parser returns an instance of this struct.
#[derive(Debug)]
pub struct StateTableError {
    pub kind: StateTableErrorKind,
    pub prod_idx: PIdx
}

impl fmt::Display for StateTableError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let s;
        match self.kind {
            StateTableErrorKind::AcceptReduceConflict => s = "Accept/reduce conflict",
        }
        write!(f, "{}", s)
    }
}

/// A representation of a `StateTable` for a grammar. `actions` and `gotos` are split into two
/// separate hashmaps, rather than a single table, due to the different types of their values.
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct StateTable {
    // For actions, we use a HashMap as a quick representation of a sparse table. We use the normal
    // statetable representation where rows represent states and columns represent terminals. Thus
    // the statetable:
    //        A         B
    //   0  shift 1
    //   1  shift 0  reduce B
    // is represented as a hashtable {0: shift 1, 2: shift 0, 3: reduce 4}.
    actions          : HashMap<u32, Action, BuildHasherDefault<FnvHasher>>,
    state_actions    : Vob,
    gotos            : HashMap<u32, StIdx, BuildHasherDefault<FnvHasher>>,
    core_reduces     : Vob,
    state_shifts     : Vob,
    reduce_states    : Vob,
    nonterms_len     : u32,
    prods_len        : u32,
    terms_len        : u32,
    /// The number of reduce/reduce errors encountered.
    pub reduce_reduce: u64,
    /// The number of shift/reduce errors encountered.
    pub shift_reduce : u64,
    pub final_state  : StIdx
}

#[derive(Clone, Copy, Debug, PartialEq)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub enum Action {
    /// Shift to state X in the statetable.
    Shift(StIdx),
    /// Reduce production X in the grammar.
    Reduce(PIdx),
    /// Accept this input.
    Accept
}

impl StateTable {
    pub fn new(grm: &YaccGrammar, sg: &StateGraph) -> Result<StateTable, StateTableError> {
        let mut actions = HashMap::with_hasher(BuildHasherDefault::<FnvHasher>::default());
        let mut state_actions = Vob::from_elem((sg.all_states_len() * grm.terms_len()) as usize, false);
        let mut gotos = HashMap::with_hasher(BuildHasherDefault::<FnvHasher>::default());
        let mut reduce_reduce = 0; // How many automatically resolved reduce/reduces were made?
        let mut shift_reduce  = 0; // How many automatically resolved shift/reduces were made?
        let mut final_state = None;

        // Assert that we can fit the actions table into a u32
        assert!(sg.all_states_len().checked_mul(grm.terms_len()).is_some());
        for (state_i, state) in sg.iter_closed_states()
                                  .enumerate()
                                  .map(|(x, y)| (StIdx::from(x), y)) {
            // Populate reduce and accepts
            for (&(prod_i, dot), ctx) in &state.items {
                if dot < SIdx::from(grm.prod(prod_i).len()) {
                    continue;
                }
                for term_i in ctx.iter_set_bits(..) {
                    let off = StateTable::actions_offset(grm.terms_len(),
                                                         state_i,
                                                         TIdx::from(term_i));
                    state_actions.set(off as usize, true);
                    match actions.entry(off) {
                        Entry::Occupied(mut e) => {
                            match *e.get_mut() {
                                Action::Reduce(prod_j) => {
                                    if prod_i == grm.start_prod() && term_i == usize::from(grm.eof_term_idx()) {
                                        return Err(StateTableError{
                                            kind: StateTableErrorKind::AcceptReduceConflict,
                                            prod_idx: prod_i
                                        });
                                    }
                                    // By default, Yacc resolves reduce/reduce conflicts in favour
                                    // of the earlier production in the grammar.
                                    if prod_i < prod_j {
                                        reduce_reduce += 1;
                                        e.insert(Action::Reduce(prod_i));
                                    }
                                    else if prod_i > prod_j {
                                        reduce_reduce += 1;
                                    }
                                },
                                Action::Accept => {
                                    return Err(StateTableError{
                                        kind: StateTableErrorKind::AcceptReduceConflict,
                                        prod_idx: prod_i
                                    })
                                }
                                _ => panic!("Internal error")
                            }
                        }
                        Entry::Vacant(e) => {
                            if prod_i == grm.start_prod() && term_i == usize::from(grm.eof_term_idx()) {
                                assert!(final_state.is_none());
                                final_state = Some(state_i);
                                e.insert(Action::Accept);
                            }
                            else {
                                e.insert(Action::Reduce(prod_i.into()));
                            }
                        }
                    }
                }
            }

            let nt_len = grm.nonterms_len();
            // Assert that we can fit the goto table into a u32
            assert!(sg.all_states_len().checked_mul(nt_len).is_some());
            for (&sym, state_j) in sg.edges(state_i) {
                match sym {
                    Symbol::Nonterm(nonterm_i) => {
                        // Populate gotos
                        let off = (u32::from(state_i) * nt_len) + u32::from(nonterm_i);
                        debug_assert!(gotos.get(&off).is_none());
                        gotos.insert(off, *state_j);
                    },
                    Symbol::Term(term_k) => {
                        // Populate shifts
                        let off = StateTable::actions_offset(grm.terms_len(), state_i, term_k);
                        state_actions.set(off as usize, true);
                        match actions.entry(off) {
                            Entry::Occupied(mut e) => {
                                match *e.get_mut() {
                                    Action::Shift(x) => assert_eq!(*state_j, x),
                                    Action::Reduce(prod_k) => {
                                        shift_reduce += resolve_shift_reduce(grm, e, term_k,
                                                                             prod_k, *state_j);
                                    }
                                    Action::Accept => panic!("Internal error")
                                }
                            },
                            Entry::Vacant(e) => {
                                e.insert(Action::Shift(*state_j));
                            }
                        }
                    }
                }
            }
        }
        assert!(final_state.is_some());

        let mut nt_depth = HashMap::new();
        let mut core_reduces = Vob::from_elem((sg.all_states_len() * grm.prods_len()) as usize, false);
        let mut state_shifts = Vob::from_elem((sg.all_states_len() * grm.terms_len()) as usize, false);
        let mut reduce_states = Vob::from_elem(sg.all_states_len() as usize, false);
        for i in 0..sg.all_states_len() {
            nt_depth.clear();
            let mut only_reduces = true;
            for j in 0..grm.terms_len() {
                let off = StateTable::actions_offset(grm.terms_len(), StIdx::from(i), TIdx::from(j));
                match actions.get(&off) {
                    Some(&Action::Reduce(p_idx)) => {
                        let prod_len = grm.prod(p_idx).len();
                        let nt_idx = grm.prod_to_nonterm(p_idx);
                        nt_depth.insert((nt_idx, prod_len), p_idx);
                    },
                    Some(&Action::Shift(_)) => {
                        only_reduces = false;
                        state_shifts.set(off as usize, true);
                    },
                    Some(&Action::Accept) => {
                        only_reduces = false;
                    },
                    None => ()
                }
            }

            let mut distinct_reduces = 0; // How many distinct reductions do we have?
            for &p_idx in nt_depth.values() {
                let off = (i * grm.prods_len() + u32::from(p_idx)) as usize;
                if core_reduces.set(off, true) == Some(true) {
                    distinct_reduces += 1;
                }
            }

            if only_reduces && distinct_reduces == 1 {
                reduce_states.set(i as usize, true);
            }
        }

        Ok(StateTable {actions,
                       state_actions,
                       gotos,
                       state_shifts,
                       core_reduces,
                       reduce_states,
                       nonterms_len: grm.nonterms_len(),
                       prods_len: grm.prods_len(),
                       terms_len: grm.terms_len(),
                       reduce_reduce,
                       shift_reduce,
                       final_state: final_state.unwrap()})
    }


    /// Return the action for `state_idx` and `sym`, or `None` if there isn't any.
    pub fn action(&self, state_idx: StIdx, term_idx: TIdx) -> Option<Action> {
        let off = StateTable::actions_offset(self.terms_len, state_idx, term_idx);
        self.actions.get(&off).map_or(None, |x| Some(*x))
    }

    /// Return an iterator over the indexes of all non-empty actions of `state_idx`.
    pub fn state_actions(&self, state_idx: StIdx) -> StateActionsIterator {
        let start = usize::from(state_idx) * self.terms_len as usize;
        let end = start + self.terms_len as usize;
        StateActionsIterator{iter: self.state_actions.iter_set_bits(start..end),
                             start}
    }

    /// Return an iterator over the indexes of all shift actions of `state_idx`. By definition this
    /// is a subset of the indexes produced by [`state_actions`](#method.state_actions).
    pub fn state_shifts(&self, state_idx: StIdx) -> StateActionsIterator {
        let start = usize::from(state_idx) * self.terms_len as usize;
        let end = start + self.terms_len as usize;
        StateActionsIterator{iter: self.state_shifts.iter_set_bits(start..end),
                            start}
    }

    /// Does the state `state_idx` 1) only contain reduce (and error) actions 2) do those
    /// reductions all reduce to the same production?
    pub fn reduce_only_state(&self, state_idx: StIdx) -> bool {
        self.reduce_states[usize::from(state_idx)]
    }

    /// Return an iterator over a set of "core" reduces of `state_idx`. This is a minimal set of
    /// reduce actions which explore all possible reductions from a given state. Note that these
    /// are chosen non-deterministically from a set of equivalent reduce actions: you must not rely
    /// on always seeing the same reduce actions. For example if a state has these three items:
    ///
    ///   [E -> a ., $]
    ///   [E -> b ., $]
    ///   [F -> c ., $]
    ///
    /// then the core reduces will be:
    ///
    ///   One of: [E -> a., $] or [E -> b., $]
    ///   And:    [F -> c., $]
    ///
    /// since the two [E -> ...] items both have the same effects on a parse stack.
    pub fn core_reduces(&self, state_idx: StIdx) -> CoreReducesIterator {
        let start = usize::from(state_idx) * self.prods_len as usize;
        let end = start + self.prods_len as usize;
        CoreReducesIterator{iter: self.core_reduces.iter_set_bits(start..end),
                            start}
    }

    /// Return the goto state for `state_idx` and `nonterm_idx`, or `None` if there isn't any.
    pub fn goto(&self, state_idx: StIdx, nonterm_idx: NTIdx) -> Option<StIdx> {
        let off = (u32::from(state_idx) * self.nonterms_len) + u32::from(nonterm_idx);
        self.gotos.get(&off).map_or(None, |x| Some(*x))
    }

    fn actions_offset(terms_len: u32, state_idx: StIdx, term_idx: TIdx) -> u32 {
        u32::from(state_idx) * terms_len + u32::from(term_idx)
    }
}

pub struct StateActionsIterator<'a> {
    iter: IterSetBits<'a, usize>,
    start: usize
}

impl<'a> Iterator for StateActionsIterator<'a> {
    type Item = TIdx;

    fn next(&mut self) -> Option<TIdx> {
        self.iter.next().map(|i| TIdx::from(i - self.start))
    }
}

pub struct CoreReducesIterator<'a> {
    iter: IterSetBits<'a, usize>,
    start: usize
}

impl<'a> Iterator for CoreReducesIterator<'a> {
    type Item = PIdx;

    fn next(&mut self) -> Option<PIdx> {
        self.iter.next().map(|i| PIdx::from(i - self.start))
    }
}

fn resolve_shift_reduce(grm: &YaccGrammar, mut e: OccupiedEntry<u32, Action>, term_k: TIdx,
                        prod_k: PIdx, state_j: StIdx) -> u64 {
    let mut shift_reduce = 0;
    let term_k_prec = grm.term_precedence(term_k);
    let prod_k_prec = grm.prod_precedence(prod_k);
    match (term_k_prec, prod_k_prec) {
        (_, None) | (None, _) => {
            // If the terminal and production don't both have precedences, we use Yacc's default
            // resolution, which is in favour of the shift.
            e.insert(Action::Shift(state_j));
            shift_reduce += 1;
        },
        (Some(term_prec), Some(prod_prec)) => {
            if term_prec.level == prod_prec.level {
                // Both terminal and production have the same level precedence, so we need to look
                // at the precedence kind.
                match (term_prec.kind, prod_prec.kind) {
                    (AssocKind::Left, AssocKind::Left) => {
                        // Left associativity is resolved in favour of the reduce (i.e. leave
                        // as-is).
                    },
                    (AssocKind::Right, AssocKind::Right) => {
                        // Right associativity is resolved in favour of the shift.
                        e.insert(Action::Shift(state_j));
                    },
                    (AssocKind::Nonassoc, AssocKind::Nonassoc) => {
                        // Nonassociativity leads to a run-time parsing error, so we need to remove
                        // the action entirely.
                        e.remove();
                    },
                    (_, _) => {
                        panic!("Not supported.");
                    }
                }
            } else if term_prec.level > prod_prec.level {
                // The terminal has higher level precedence, so resolve in favour of shift.
                e.insert(Action::Shift(state_j));
            }
            // If term_lev < prod_lev, then the production has higher level precedence and we keep
            // the reduce as-is.
        }
    }
    shift_reduce
}

#[cfg(test)]
mod test {
    use std::collections::HashSet;
    use StIdx;
    use super::{Action, StateTable, StateTableError, StateTableErrorKind};
    use cfgrammar::{Symbol, TIdx};
    use cfgrammar::yacc::{yacc_grm, YaccKind};
    use pager::pager_stategraph;

    #[test]
    fn test_statetable() {
        // Taken from p19 of www.cs.umd.edu/~mvz/cmsc430-s07/M10lr.pdf
        let grm = yacc_grm(YaccKind::Original, &"
            %start Expr
            %%
            Expr : Term '-' Expr | Term;
            Term : Factor '*' Term | Factor;
            Factor : 'id';
          ").unwrap();
        let sg = pager_stategraph(&grm);
        assert_eq!(sg.all_states_len(), 9);

        let s0 = StIdx::from(0 as u32);
        let s1 = sg.edge(s0, Symbol::Nonterm(grm.nonterm_idx("Expr").unwrap())).unwrap();
        let s2 = sg.edge(s0, Symbol::Nonterm(grm.nonterm_idx("Term").unwrap())).unwrap();
        let s3 = sg.edge(s0, Symbol::Nonterm(grm.nonterm_idx("Factor").unwrap())).unwrap();
        let s4 = sg.edge(s0, Symbol::Term(grm.term_idx("id").unwrap())).unwrap();
        let s5 = sg.edge(s2, Symbol::Term(grm.term_idx("-").unwrap())).unwrap();
        let s6 = sg.edge(s3, Symbol::Term(grm.term_idx("*").unwrap())).unwrap();
        let s7 = sg.edge(s5, Symbol::Nonterm(grm.nonterm_idx("Expr").unwrap())).unwrap();
        let s8 = sg.edge(s6, Symbol::Nonterm(grm.nonterm_idx("Term").unwrap())).unwrap();

        let st = StateTable::new(&grm, &sg).unwrap();

        // Actions
        assert_eq!(st.actions.len(), 15);
        let assert_reduce = |state_i: StIdx, term_i: TIdx, rule: &str, prod_off: usize| {
            let prod_i = grm.nonterm_to_prods(grm.nonterm_idx(rule).unwrap())[prod_off];
            assert_eq!(st.action(state_i, term_i).unwrap(), Action::Reduce(prod_i.into()));
        };

        assert_eq!(st.action(s0, grm.term_idx("id").unwrap()).unwrap(), Action::Shift(s4));
        assert_eq!(st.action(s1, grm.eof_term_idx()).unwrap(), Action::Accept);
        assert_eq!(st.final_state, s1);
        assert_eq!(st.action(s2, grm.term_idx("-").unwrap()).unwrap(), Action::Shift(s5));
        assert_reduce(s2, grm.eof_term_idx(), "Expr", 1);
        assert_reduce(s3, grm.term_idx("-").unwrap(), "Term", 1);
        assert_eq!(st.action(s3, grm.term_idx("*").unwrap()).unwrap(), Action::Shift(s6));
        assert_reduce(s3, grm.eof_term_idx(), "Term", 1);
        assert_reduce(s4, grm.term_idx("-").unwrap(), "Factor", 0);
        assert_reduce(s4, grm.term_idx("*").unwrap(), "Factor", 0);
        assert_reduce(s4, grm.eof_term_idx(), "Factor", 0);
        assert_eq!(st.action(s5, grm.term_idx("id").unwrap()).unwrap(), Action::Shift(s4));
        assert_eq!(st.action(s6, grm.term_idx("id").unwrap()).unwrap(), Action::Shift(s4));
        assert_reduce(s7, grm.eof_term_idx(), "Expr", 0);
        assert_reduce(s8, grm.term_idx("-").unwrap(), "Term", 0);
        assert_reduce(s8, grm.eof_term_idx(), "Term", 0);

        let mut s4_actions = HashSet::new();
        s4_actions.extend(&[grm.term_idx("-").unwrap(),
                            grm.term_idx("*").unwrap(),
                            grm.eof_term_idx()]);
        assert_eq!(st.state_actions(s4).collect::<HashSet<TIdx>>(), s4_actions);

        let s2_state_shifts = &[grm.term_idx("-").unwrap()]
                               .iter()
                               .cloned()
                               .collect::<HashSet<_>>();
        assert_eq!(st.state_shifts(s2).collect::<HashSet<_>>(), *s2_state_shifts);

        let s4_core_reduces = &[grm.nonterm_to_prods(grm.nonterm_idx("Factor").unwrap())[0]]
                              .iter()
                              .cloned()
                              .collect::<HashSet<_>>();
        assert_eq!(st.core_reduces(s4).collect::<HashSet<_>>(), *s4_core_reduces);

        // Gotos
        assert_eq!(st.gotos.len(), 8);
        assert_eq!(st.goto(s0, grm.nonterm_idx("Expr").unwrap()).unwrap(), s1);
        assert_eq!(st.goto(s0, grm.nonterm_idx("Term").unwrap()).unwrap(), s2);
        assert_eq!(st.goto(s0, grm.nonterm_idx("Factor").unwrap()).unwrap(), s3);
        assert_eq!(st.goto(s5, grm.nonterm_idx("Expr").unwrap()).unwrap(), s7);
        assert_eq!(st.goto(s5, grm.nonterm_idx("Term").unwrap()).unwrap(), s2);
        assert_eq!(st.goto(s5, grm.nonterm_idx("Factor").unwrap()).unwrap(), s3);
        assert_eq!(st.goto(s6, grm.nonterm_idx("Term").unwrap()).unwrap(), s8);
        assert_eq!(st.goto(s6, grm.nonterm_idx("Factor").unwrap()).unwrap(), s3);
    }

    #[test]
    fn test_default_reduce_reduce() {
        let grm = yacc_grm(YaccKind::Original, &"
            %start A
            %%
            A : B 'x' | C 'x' 'x';
            B : 'a';
            C : 'a';
          ").unwrap();
        let sg = pager_stategraph(&grm);
        let st = StateTable::new(&grm, &sg).unwrap();
        assert_eq!(st.actions.len(), 8);

        // We only extract the states necessary to test those rules affected by the reduce/reduce.
        let s0 = StIdx::from(0 as u32);
        let s4 = sg.edge(s0, Symbol::Term(grm.term_idx("a").unwrap())).unwrap();

        assert_eq!(st.action(s4, grm.term_idx("x").unwrap()).unwrap(),
                   Action::Reduce(grm.nonterm_to_prods(grm.nonterm_idx("B").unwrap())[0]));
    }

    #[test]
    fn test_default_shift_reduce() {
        let grm = yacc_grm(YaccKind::Original, &"
            %start Expr
            %%
            Expr : Expr '+' Expr
                 | Expr '*' Expr
                 | 'id' ;
          ").unwrap();
        let sg = pager_stategraph(&grm);
        let st = StateTable::new(&grm, &sg).unwrap();
        assert_eq!(st.actions.len(), 15);

        let s0 = StIdx::from(0 as u32);
        let s1 = sg.edge(s0, Symbol::Nonterm(grm.nonterm_idx("Expr").unwrap())).unwrap();
        let s3 = sg.edge(s1, Symbol::Term(grm.term_idx("+").unwrap())).unwrap();
        let s4 = sg.edge(s1, Symbol::Term(grm.term_idx("*").unwrap())).unwrap();
        let s5 = sg.edge(s4, Symbol::Nonterm(grm.nonterm_idx("Expr").unwrap())).unwrap();
        let s6 = sg.edge(s3, Symbol::Nonterm(grm.nonterm_idx("Expr").unwrap())).unwrap();

        assert_eq!(st.action(s5, grm.term_idx("+").unwrap()).unwrap(), Action::Shift(s3));
        assert_eq!(st.action(s5, grm.term_idx("*").unwrap()).unwrap(), Action::Shift(s4));

        assert_eq!(st.action(s6, grm.term_idx("+").unwrap()).unwrap(), Action::Shift(s3));
        assert_eq!(st.action(s6, grm.term_idx("*").unwrap()).unwrap(), Action::Shift(s4));
    }

    #[test]
    fn test_conflict_resolution() {
        // Example taken from p54 of Locally least-cost error repair in LR parsers, Carl Cerecke
        let grm = yacc_grm(YaccKind::Original, &"
            %start S
            %%
            S: A 'c' 'd'
             | B 'c' 'e';
            A: 'a';
            B: 'a'
             | 'b';
            A: 'b';
            ").unwrap();
        let sg = pager_stategraph(&grm);
        let st = StateTable::new(&grm, &sg).unwrap();
        let s0 = StIdx::from(0 as u32);
        let s1 = sg.edge(s0, Symbol::Term(grm.term_idx("a").unwrap())).unwrap();
        let s2 = sg.edge(s0, Symbol::Term(grm.term_idx("b").unwrap())).unwrap();

        assert_eq!(st.action(s1, grm.term_idx("c").unwrap()).unwrap(),
                   Action::Reduce(grm.nonterm_to_prods(grm.nonterm_idx("A").unwrap())[0]));
        assert_eq!(st.action(s2, grm.term_idx("c").unwrap()).unwrap(),
                   Action::Reduce(grm.nonterm_to_prods(grm.nonterm_idx("B").unwrap())[1]));
    }

    #[test]
    fn test_left_associativity() {
        let grm = yacc_grm(YaccKind::Original, &"
            %start Expr
            %left '+'
            %left '*'
            %%
            Expr : Expr '+' Expr
                 | Expr '*' Expr
                 | 'id' ;
          ").unwrap();
        let sg = pager_stategraph(&grm);
        let st = StateTable::new(&grm, &sg).unwrap();
        assert_eq!(st.actions.len(), 15);

        let s0 = StIdx::from(0 as u32);
        let s1 = sg.edge(s0, Symbol::Nonterm(grm.nonterm_idx("Expr").unwrap())).unwrap();
        let s3 = sg.edge(s1, Symbol::Term(grm.term_idx("+").unwrap())).unwrap();
        let s4 = sg.edge(s1, Symbol::Term(grm.term_idx("*").unwrap())).unwrap();
        let s5 = sg.edge(s4, Symbol::Nonterm(grm.nonterm_idx("Expr").unwrap())).unwrap();
        let s6 = sg.edge(s3, Symbol::Nonterm(grm.nonterm_idx("Expr").unwrap())).unwrap();

        assert_eq!(st.action(s5, grm.term_idx("+").unwrap()).unwrap(),
                   Action::Reduce(grm.nonterm_to_prods(grm.nonterm_idx("Expr").unwrap())[1]));
        assert_eq!(st.action(s5, grm.term_idx("*").unwrap()).unwrap(),
                   Action::Reduce(grm.nonterm_to_prods(grm.nonterm_idx("Expr").unwrap())[1]));
        assert_eq!(st.action(s5, grm.eof_term_idx()).unwrap(),
                   Action::Reduce(grm.nonterm_to_prods(grm.nonterm_idx("Expr").unwrap())[1]));

        assert_eq!(st.action(s6, grm.term_idx("+").unwrap()).unwrap(),
                   Action::Reduce(grm.nonterm_to_prods(grm.nonterm_idx("Expr").unwrap())[0]));
        assert_eq!(st.action(s6, grm.term_idx("*").unwrap()).unwrap(),
                   Action::Shift(s4));
        assert_eq!(st.action(s6, grm.eof_term_idx()).unwrap(),
                   Action::Reduce(grm.nonterm_to_prods(grm.nonterm_idx("Expr").unwrap())[0]));
    }

    #[test]
    fn test_left_right_associativity() {
        let grm = &yacc_grm(YaccKind::Original, &"
            %start Expr
            %right '='
            %left '+'
            %left '*'
            %%
            Expr : Expr '+' Expr
                 | Expr '*' Expr
                 | Expr '=' Expr
                 | 'id' ;
          ").unwrap();
        let sg = pager_stategraph(&grm);
        let st = StateTable::new(&grm, &sg).unwrap();
        assert_eq!(st.actions.len(), 24);

        let s0 = StIdx::from(0 as u32);
        let s1 = sg.edge(s0, Symbol::Nonterm(grm.nonterm_idx("Expr").unwrap())).unwrap();
        let s3 = sg.edge(s1, Symbol::Term(grm.term_idx("+").unwrap())).unwrap();
        let s4 = sg.edge(s1, Symbol::Term(grm.term_idx("*").unwrap())).unwrap();
        let s5 = sg.edge(s1, Symbol::Term(grm.term_idx("=").unwrap())).unwrap();
        let s6 = sg.edge(s5, Symbol::Nonterm(grm.nonterm_idx("Expr").unwrap())).unwrap();
        let s7 = sg.edge(s4, Symbol::Nonterm(grm.nonterm_idx("Expr").unwrap())).unwrap();
        let s8 = sg.edge(s3, Symbol::Nonterm(grm.nonterm_idx("Expr").unwrap())).unwrap();

        assert_eq!(st.action(s6, grm.term_idx("+").unwrap()).unwrap(),
                   Action::Shift(s3));
        assert_eq!(st.action(s6, grm.term_idx("*").unwrap()).unwrap(),
                   Action::Shift(s4));
        assert_eq!(st.action(s6, grm.term_idx("=").unwrap()).unwrap(),
                   Action::Shift(s5));
        assert_eq!(st.action(s6, grm.eof_term_idx()).unwrap(),
                   Action::Reduce(grm.nonterm_to_prods(grm.nonterm_idx("Expr").unwrap())[2]));

        assert_eq!(st.action(s7, grm.term_idx("+").unwrap()).unwrap(),
                   Action::Reduce(grm.nonterm_to_prods(grm.nonterm_idx("Expr").unwrap())[1]));
        assert_eq!(st.action(s7, grm.term_idx("*").unwrap()).unwrap(),
                   Action::Reduce(grm.nonterm_to_prods(grm.nonterm_idx("Expr").unwrap())[1]));
        assert_eq!(st.action(s7, grm.term_idx("=").unwrap()).unwrap(),
                   Action::Reduce(grm.nonterm_to_prods(grm.nonterm_idx("Expr").unwrap())[1]));
        assert_eq!(st.action(s7, grm.eof_term_idx()).unwrap(),
                   Action::Reduce(grm.nonterm_to_prods(grm.nonterm_idx("Expr").unwrap())[1]));

        assert_eq!(st.action(s8, grm.term_idx("+").unwrap()).unwrap(),
                   Action::Reduce(grm.nonterm_to_prods(grm.nonterm_idx("Expr").unwrap())[0]));
        assert_eq!(st.action(s8, grm.term_idx("*").unwrap()).unwrap(),
                   Action::Shift(s4));
        assert_eq!(st.action(s8, grm.term_idx("=").unwrap()).unwrap(),
                   Action::Reduce(grm.nonterm_to_prods(grm.nonterm_idx("Expr").unwrap())[0]));
        assert_eq!(st.action(s8, grm.eof_term_idx()).unwrap(),
                   Action::Reduce(grm.nonterm_to_prods(grm.nonterm_idx("Expr").unwrap())[0]));
    }

    #[test]
    fn test_left_right_nonassoc_associativity() {
        let grm = yacc_grm(YaccKind::Original, &"
            %start Expr
            %right '='
            %left '+'
            %left '*'
            %nonassoc '~'
            %%
            Expr : Expr '+' Expr
                 | Expr '*' Expr
                 | Expr '=' Expr
                 | Expr '~' Expr
                 | 'id' ;
          ").unwrap();
        let sg = pager_stategraph(&grm);
        let st = StateTable::new(&grm, &sg).unwrap();
        assert_eq!(st.actions.len(), 34);

        let s0 = StIdx::from(0 as u32);
        let s1 = sg.edge(s0, Symbol::Nonterm(grm.nonterm_idx("Expr").unwrap())).unwrap();
        let s3 = sg.edge(s1, Symbol::Term(grm.term_idx("+").unwrap())).unwrap();
        let s4 = sg.edge(s1, Symbol::Term(grm.term_idx("*").unwrap())).unwrap();
        let s5 = sg.edge(s1, Symbol::Term(grm.term_idx("=").unwrap())).unwrap();
        let s6 = sg.edge(s1, Symbol::Term(grm.term_idx("~").unwrap())).unwrap();
        let s7 = sg.edge(s6, Symbol::Nonterm(grm.nonterm_idx("Expr").unwrap())).unwrap();
        let s8 = sg.edge(s5, Symbol::Nonterm(grm.nonterm_idx("Expr").unwrap())).unwrap();
        let s9 = sg.edge(s4, Symbol::Nonterm(grm.nonterm_idx("Expr").unwrap())).unwrap();
        let s10 = sg.edge(s3, Symbol::Nonterm(grm.nonterm_idx("Expr").unwrap())).unwrap();

        assert_eq!(st.action(s7, grm.term_idx("+").unwrap()).unwrap(),
                   Action::Reduce(grm.nonterm_to_prods(grm.nonterm_idx("Expr").unwrap())[3]));
        assert_eq!(st.action(s7, grm.term_idx("*").unwrap()).unwrap(),
                   Action::Reduce(grm.nonterm_to_prods(grm.nonterm_idx("Expr").unwrap())[3]));
        assert_eq!(st.action(s7, grm.term_idx("=").unwrap()).unwrap(),
                   Action::Reduce(grm.nonterm_to_prods(grm.nonterm_idx("Expr").unwrap())[3]));
        assert_eq!(st.action(s7, grm.eof_term_idx()).unwrap(),
                   Action::Reduce(grm.nonterm_to_prods(grm.nonterm_idx("Expr").unwrap())[3]));

        assert_eq!(st.action(s8, grm.term_idx("+").unwrap()).unwrap(),
                   Action::Shift(s3));
        assert_eq!(st.action(s8, grm.term_idx("*").unwrap()).unwrap(),
                   Action::Shift(s4));
        assert_eq!(st.action(s8, grm.term_idx("=").unwrap()).unwrap(),
                   Action::Shift(s5));
        assert_eq!(st.action(s8, grm.term_idx("~").unwrap()).unwrap(),
                   Action::Shift(s6));
        assert_eq!(st.action(s8, grm.eof_term_idx()).unwrap(),
                   Action::Reduce(grm.nonterm_to_prods(grm.nonterm_idx("Expr").unwrap())[2]));

        assert_eq!(st.action(s9, grm.term_idx("+").unwrap()).unwrap(),
                   Action::Reduce(grm.nonterm_to_prods(grm.nonterm_idx("Expr").unwrap())[1]));
        assert_eq!(st.action(s9, grm.term_idx("*").unwrap()).unwrap(),
                   Action::Reduce(grm.nonterm_to_prods(grm.nonterm_idx("Expr").unwrap())[1]));
        assert_eq!(st.action(s9, grm.term_idx("=").unwrap()).unwrap(),
                   Action::Reduce(grm.nonterm_to_prods(grm.nonterm_idx("Expr").unwrap())[1]));
        assert_eq!(st.action(s9, grm.term_idx("~").unwrap()).unwrap(),
                   Action::Shift(s6));
        assert_eq!(st.action(s9, grm.eof_term_idx()).unwrap(),
                   Action::Reduce(grm.nonterm_to_prods(grm.nonterm_idx("Expr").unwrap())[1]));

        assert_eq!(st.action(s10, grm.term_idx("+").unwrap()).unwrap(),
                   Action::Reduce(grm.nonterm_to_prods(grm.nonterm_idx("Expr").unwrap())[0]));
        assert_eq!(st.action(s10, grm.term_idx("*").unwrap()).unwrap(),
                   Action::Shift(s4));
        assert_eq!(st.action(s10, grm.term_idx("=").unwrap()).unwrap(),
                   Action::Reduce(grm.nonterm_to_prods(grm.nonterm_idx("Expr").unwrap())[0]));
        assert_eq!(st.action(s10, grm.term_idx("~").unwrap()).unwrap(),
                   Action::Shift(s6));
        assert_eq!(st.action(s10, grm.eof_term_idx()).unwrap(),
                   Action::Reduce(grm.nonterm_to_prods(grm.nonterm_idx("Expr").unwrap())[0]));
    }

    #[test]
    fn accept_reduce_conflict() {
        let grm = yacc_grm(YaccKind::Original, &"
%start D
%%
D : D;
          ").unwrap();
        let sg = pager_stategraph(&grm);
        match StateTable::new(&grm, &sg) {
            Ok(_) => panic!("Infinitely recursive rule let through"),
            Err(StateTableError{kind: StateTableErrorKind::AcceptReduceConflict, prod_idx})
                if prod_idx == (1 as u32).into() => (),
            Err(e) => panic!("Incorrect error returned {}", e)
        }
    }
}
