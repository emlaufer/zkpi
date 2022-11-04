//! Implements functionality to export a theorem/proof to the zero-knowledge
//! prover.

use crate::term::{
    self, BindingData, BindingType, Context, Evaluator, Inductive, Term, TermData, Theorem,
};
use hashconsing::hash_coll::HConMap;
use log::{debug, warn};
use rand::prelude::*;
use std::cmp::{max, min};
use std::collections::BTreeSet;
use std::collections::{HashMap, HashSet};
use std::io::Write;
use std::num::Wrapping;

mod named_ir;
mod sim;

const EXPR_NULL: usize = 0;
const EXPR_VAR: usize = 1;
const EXPR_SORT: usize = 2;
const EXPR_APP: usize = 3;
const EXPR_LAM: usize = 4;
const EXPR_PI: usize = 5;
const EXPR_AX: usize = 6;

const EXPR_IND: usize = 7;
const EXPR_IND_CTOR: usize = 8;
const EXPR_IND_REC: usize = 9;

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct ExpTerm {
    kind: usize,
    name: usize, // TODO: can we compress?
    left: usize,
    right: usize,

    top_level_func: usize,
    argc: usize, // TODO:
                 // minimum name bound in this term
                 // if it is less than the maximum bound name in the current proof step,
                 // we must alpha rename
                 // Terms that don't bind names keep this as usize::MAX
                 //min_binding: usize,
}

impl ExpTerm {
    pub fn new(kind: usize, name: usize, left: usize, right: usize) -> ExpTerm {
        ExpTerm {
            kind,
            name,
            left,
            right,
            top_level_func: 0,
            argc: 0,
            //min_binding,
        }
    }

    pub fn bound(name: usize) -> ExpTerm {
        ExpTerm::new(EXPR_VAR, name, 0, 0)
    }

    // TODO: remove binding
    pub fn sort(level: usize) -> ExpTerm {
        ExpTerm::new(EXPR_SORT, level, 0, 0)
    }

    pub fn lam(name: usize, domain: usize, body: usize) -> ExpTerm {
        ExpTerm::new(EXPR_LAM, name, domain, body)
    }

    pub fn pi(name: usize, domain: usize, body: usize) -> ExpTerm {
        ExpTerm::new(EXPR_PI, name, domain, body)
    }

    pub fn app(f: usize, e: usize, top_level_func: usize) -> ExpTerm {
        let mut res = ExpTerm::new(EXPR_APP, 0, f, e);
        res.top_level_func = top_level_func;
        res
    }

    pub fn ax(idx: usize, dedup: usize) -> ExpTerm {
        // TODO: remove dedup from final version
        ExpTerm::new(EXPR_AX, 0, idx, dedup)
    }

    pub fn ind(idx: usize) -> ExpTerm {
        ExpTerm::new(EXPR_IND, 0, idx, 0)
    }

    pub fn ind_ctor(ind_idx: usize, ctor_idx: usize) -> ExpTerm {
        ExpTerm::new(EXPR_IND_CTOR, 0, ind_idx, ctor_idx)
    }

    pub fn ind_rec(ind_idx: usize, motive_sort: usize) -> ExpTerm {
        ExpTerm::new(EXPR_IND_REC, 0, ind_idx, motive_sort)
    }
}

const MAX_RULES: usize = 20;
#[derive(Debug, Clone)]
struct ExpInd {
    ty: usize,
    num_params: usize,

    rules: [usize; MAX_RULES],
    rule_nnrs: [usize; MAX_RULES],
    rule_nrs: [usize; MAX_RULES],
    num_rules: usize,
    //elims: [usize; 5],
    rec_body: usize,
    //elim_body: usize,
    elim_argc: usize,
}

impl ExpInd {}

const RULE_NULL: usize = 0;

// evaluation rules
const RULE_EVAL_ID: usize = 1;
const RULE_EVAL_VAR: usize = 2;
const RULE_EVAL_SORT: usize = 3; // TODO: unused
const RULE_EVAL_APP: usize = 4;
const RULE_EVAL_APP_LAM: usize = 5;
const RULE_EVAL_APP_PI: usize = 6;
const RULE_EVAL_LAM: usize = 7;
const RULE_EVAL_PI: usize = 8;
const RULE_EVAL_AX: usize = 9;

const RULE_TYPE_VAR: usize = 10;
const RULE_TYPE_SORT: usize = 11;
const RULE_TYPE_APP: usize = 12;
const RULE_TYPE_LAM: usize = 13;
const RULE_TYPE_PI: usize = 14;
const RULE_TYPE_AX: usize = 15;

const RULE_LIFT: usize = 16;

const RULE_PROOF_IRREL: usize = 17;
const RULE_EVAL_TYPE: usize = 18;

const RULE_APPLY_ELIM: usize = 19;
const RULE_GET_ARG: usize = 20;

const RULE_APPLY_ELIM_EVAL: usize = 21;

const RULE_TYPE_IND: usize = 22;
const RULE_TYPE_IND_CTOR: usize = 23;
const RULE_TYPE_IND_REC: usize = 24;
const RULE_IND_PREFIX: usize = 25;

//const RULE_ALPHA: usize = 16;
//const RULE_UNLIFT: usize = 17;

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
struct ExpRule {
    rule: usize,
    ctx_idx: usize,
    max_binding: usize,
    parent0: usize,
    parent1: usize,
    parent2: usize,
    parent3: usize,
    parent0_quot: usize,
    parent1_quot: usize,
    parent2_quot: usize,
    parent3_quot: usize,
    input_term_idx: usize,
    result_term_idx: usize,
}

impl ExpRule {
    // TODO:
    pub fn eval_id(term: usize, ctx_idx: usize, max_binding: usize) -> ExpRule {
        ExpRule {
            rule: RULE_EVAL_ID,
            ctx_idx,
            max_binding,
            parent0: 0,
            parent1: 0,
            parent2: 0,
            parent3: 0,
            parent0_quot: HashList::EMPTY,
            parent1_quot: HashList::EMPTY,
            parent2_quot: HashList::EMPTY,
            parent3_quot: HashList::EMPTY,
            input_term_idx: term,
            result_term_idx: term,
        }
    }

    pub fn eval_var(
        input: usize,
        result: usize,
        context: usize,
        max_binding: usize,
        parent0: usize,
        ctx_rem: usize,
    ) -> ExpRule {
        ExpRule {
            rule: RULE_EVAL_VAR,
            ctx_idx: context,
            max_binding,
            parent0,
            parent1: 0,
            parent2: 0,
            parent3: 0,
            parent0_quot: ctx_rem, // TODO: this goes against convention: is remainder for ctx lookup of key and value
            parent1_quot: HashList::EMPTY,
            parent2_quot: HashList::EMPTY,
            parent3_quot: HashList::EMPTY,
            input_term_idx: input,
            result_term_idx: result,
        }
    }

    pub fn eval_app(
        input: usize,
        result: usize,
        context: usize,
        parent0: usize,
        parent0_quot: usize,
        parent1: usize,
        parent1_quot: usize,
        max_binding: usize,
    ) -> ExpRule {
        ExpRule {
            rule: RULE_EVAL_APP,
            ctx_idx: context,
            max_binding,
            parent0,
            parent1,
            parent2: 0,
            parent3: 0,
            parent0_quot,
            parent1_quot,
            parent2_quot: HashList::EMPTY,
            parent3_quot: HashList::EMPTY,
            input_term_idx: input,
            result_term_idx: result,
        }
    }

    pub fn eval_app_lam(
        input: usize,
        result: usize,
        context: usize,
        parent0: usize,
        parent0_quot: usize,
        parent1: usize,
        parent1_quot: usize,
        parent2: usize,
        parent3: usize,
        max_binding: usize,
        // no parent2 quot because it equals parent0_quot with the new value...
    ) -> ExpRule {
        ExpRule {
            rule: RULE_EVAL_APP_LAM,
            ctx_idx: context,
            max_binding,
            parent0,
            parent1,
            parent2,
            parent3,
            parent0_quot,
            parent1_quot,
            parent2_quot: HashList::EMPTY,
            parent3_quot: HashList::EMPTY,
            input_term_idx: input,
            result_term_idx: result,
        }
    }

    pub fn eval_lam(
        input: usize,
        result: usize,
        context: usize,
        parent0: usize,
        parent0_quot: usize,
        max_binding: usize,
    ) -> ExpRule {
        ExpRule {
            rule: RULE_EVAL_LAM,
            ctx_idx: context,
            max_binding,
            parent0,
            parent1: 0,
            parent2: 0,
            parent3: 0,
            parent0_quot,
            parent1_quot: HashList::EMPTY,
            parent2_quot: HashList::EMPTY,
            parent3_quot: HashList::EMPTY,
            input_term_idx: input,
            result_term_idx: result,
        }
    }

    pub fn eval_pi(
        input: usize,
        result: usize,
        context: usize,
        parent0: usize,
        parent0_quot: usize,
        parent1: usize,
        parent1_quot: usize,
        max_binding: usize,
    ) -> ExpRule {
        ExpRule {
            rule: RULE_EVAL_PI,
            ctx_idx: context,
            max_binding,
            parent0,
            parent1,
            parent2: 0,
            parent3: 0,
            parent0_quot,
            parent1_quot,
            parent2_quot: HashList::EMPTY,
            parent3_quot: HashList::EMPTY,
            input_term_idx: input,
            result_term_idx: result,
        }
    }

    pub fn ty_var(
        input: usize,
        result: usize,
        context: usize,
        max_binding: usize,
        parent0: usize,
        ctx_rem: usize,
    ) -> ExpRule {
        ExpRule {
            rule: RULE_TYPE_VAR,
            ctx_idx: context,
            max_binding,
            parent0,
            parent1: 0,
            parent2: 0,
            parent3: 0,
            parent0_quot: ctx_rem, // TODO: this goes against convention: is remainder for ctx lookup of key and value
            parent1_quot: HashList::EMPTY,
            parent2_quot: HashList::EMPTY,
            parent3_quot: HashList::EMPTY,
            input_term_idx: input,
            result_term_idx: result,
        }
    }

    // dont care about max binding because no more possible bindings...
    pub fn ty_sort(input: usize, result: usize) -> ExpRule {
        ExpRule {
            rule: RULE_TYPE_SORT,
            ctx_idx: HashList::EMPTY,
            max_binding: 0,
            parent0: 0,
            parent1: 0,
            parent2: 0,
            parent3: 0,
            parent0_quot: HashList::EMPTY,
            parent1_quot: HashList::EMPTY,
            parent2_quot: HashList::EMPTY,
            parent3_quot: HashList::EMPTY,
            input_term_idx: input,
            result_term_idx: result,
        }
    }

    pub fn ty_lam(
        input: usize,
        result: usize,
        context: usize,
        parent0: usize,
        parent0_quot: usize,
        max_binding: usize,
    ) -> ExpRule {
        ExpRule {
            rule: RULE_TYPE_LAM,
            ctx_idx: context,
            max_binding,
            parent0,
            parent1: 0,
            parent2: 0,
            parent3: 0,
            parent0_quot,
            parent1_quot: HashList::EMPTY,
            parent2_quot: HashList::EMPTY,
            parent3_quot: HashList::EMPTY,
            input_term_idx: input,
            result_term_idx: result,
        }
    }

    pub fn ty_pi(
        input: usize,
        result: usize,
        context: usize,
        parent0: usize,
        parent0_quot: usize,
        parent1: usize,
        parent1_quot: usize,
        parent2: usize,
        parent2_quot: usize,
        max_binding: usize,
    ) -> ExpRule {
        ExpRule {
            rule: RULE_TYPE_PI,
            ctx_idx: context,
            max_binding,
            parent0,
            parent1,
            parent2,
            parent3: 0,
            parent0_quot,
            parent1_quot,
            parent2_quot,
            parent3_quot: HashList::EMPTY,
            input_term_idx: input,
            result_term_idx: result,
        }
    }

    pub fn ty_app(
        input: usize,
        result: usize,
        context: usize,
        parent0: usize,
        parent0_quot: usize,
        parent1: usize,
        parent1_quot: usize,
        parent2: usize,
        parent2_quot: usize,
        parent3: usize,
        max_binding: usize,
    ) -> ExpRule {
        ExpRule {
            rule: RULE_TYPE_APP,
            ctx_idx: context,
            max_binding,
            parent0,
            parent1,
            parent2,
            parent3,
            parent0_quot,
            parent1_quot,
            parent2_quot,
            parent3_quot: HashList::EMPTY,
            input_term_idx: input,
            result_term_idx: result,
        }
    }

    pub fn ty_ax(input: usize, result: usize, max_binding: usize, parent0: usize) -> ExpRule {
        ExpRule {
            rule: RULE_TYPE_AX,
            ctx_idx: HashList::EMPTY,
            max_binding,
            parent0,
            parent1: 0,
            parent2: 0,
            parent3: 0,
            parent0_quot: HashList::EMPTY,
            parent1_quot: HashList::EMPTY,
            parent2_quot: HashList::EMPTY,
            parent3_quot: HashList::EMPTY,
            input_term_idx: input,
            result_term_idx: result,
        }
    }

    pub fn lift(
        input: usize,
        result: usize,
        max_binding: usize,
        min_binding_seen: usize,
        parent0: usize,
        parent1: usize,
    ) -> ExpRule {
        ExpRule {
            rule: RULE_LIFT,
            ctx_idx: HashList::EMPTY,
            max_binding,
            parent0,
            parent1,
            parent2: min_binding_seen,
            parent3: 0,
            parent0_quot: HashList::EMPTY,
            parent1_quot: HashList::EMPTY,
            parent2_quot: HashList::EMPTY,
            parent3_quot: HashList::EMPTY,
            input_term_idx: input,
            result_term_idx: result,
        }
    }

    pub fn proof_irrel(
        input: usize,
        result: usize,
        context: usize,
        max_binding: usize,
        parent0: usize,
        parent1: usize,
        parent2: usize,
    ) -> ExpRule {
        ExpRule {
            rule: RULE_PROOF_IRREL,
            ctx_idx: context,
            max_binding,
            parent0,
            parent1,
            parent2,
            parent3: 0,
            parent0_quot: HashList::EMPTY,
            parent1_quot: HashList::EMPTY,
            parent2_quot: HashList::EMPTY,
            parent3_quot: HashList::EMPTY,
            input_term_idx: input,
            result_term_idx: result,
        }
    }

    pub fn eval_ty(
        input: usize,
        result: usize,
        context: usize,
        max_binding: usize,
        parent0: usize,
        parent1: usize,
    ) -> ExpRule {
        ExpRule {
            rule: RULE_EVAL_TYPE,
            ctx_idx: context,
            max_binding,
            parent0,
            parent1,
            parent2: 0,
            parent3: 0,
            parent0_quot: HashList::EMPTY,
            parent1_quot: HashList::EMPTY,
            parent2_quot: HashList::EMPTY,
            parent3_quot: HashList::EMPTY,
            input_term_idx: input,
            result_term_idx: result,
        }
    }

    pub fn get_arg(input: usize, result: usize, count: usize, parent0: usize) -> ExpRule {
        ExpRule {
            rule: RULE_GET_ARG,
            ctx_idx: count,
            max_binding: 0,
            parent0,
            parent1: 0,
            parent2: 0,
            parent3: 0,
            parent0_quot: 0,
            parent1_quot: 0,
            parent2_quot: 0,
            parent3_quot: 0,
            input_term_idx: input,
            result_term_idx: result,
        }
    }

    pub fn apply_elim(
        input: usize,
        result: usize,
        rec: usize,
        e_i: usize,
        context: usize,
        num_nonrecs: usize,
        num_recs: usize,
        parent0: usize,
    ) -> ExpRule {
        ExpRule {
            rule: RULE_APPLY_ELIM,
            ctx_idx: context,
            max_binding: 0, //TODO: fxi
            parent0,
            parent1: 0,
            parent2: num_nonrecs,
            parent3: num_recs,
            parent0_quot: rec,
            parent1_quot: e_i,
            parent2_quot: 0,
            parent3_quot: 0,
            input_term_idx: input,
            result_term_idx: result,
        }
    }

    pub fn apply_elim_eval(
        input: usize,
        result: usize,
        rec: usize,
        e_i: usize,
        num_nonrecs: usize,
        num_recs: usize,
        context: usize,
        max_binding: usize,
        parent0: usize,
        parent1: usize,
    ) -> ExpRule {
        ExpRule {
            rule: RULE_APPLY_ELIM_EVAL,
            ctx_idx: context,
            max_binding,
            parent0,
            parent1,
            parent2: num_nonrecs,
            parent3: num_recs,
            parent0_quot: rec,
            parent1_quot: e_i,
            parent2_quot: 0,
            parent3_quot: 0,
            input_term_idx: input,
            result_term_idx: result,
        }
    }

    pub fn ty_ind(input: usize, result: usize, max_binding: usize, parent0: usize) -> ExpRule {
        ExpRule {
            rule: RULE_TYPE_IND,
            ctx_idx: HashList::EMPTY,
            max_binding,
            parent0,
            parent1: 0,
            parent2: 0,
            parent3: 0,
            parent0_quot: 0,
            parent1_quot: 0,
            parent2_quot: 0,
            parent3_quot: 0,
            input_term_idx: input,
            result_term_idx: result,
        }
    }

    pub fn ty_ind_ctor(input: usize, result: usize, max_binding: usize, parent0: usize) -> ExpRule {
        ExpRule {
            rule: RULE_TYPE_IND_CTOR,
            ctx_idx: HashList::EMPTY,
            max_binding,
            parent0,
            parent1: 0,
            parent2: 0,
            parent3: 0,
            parent0_quot: 0,
            parent1_quot: 0,
            parent2_quot: 0,
            parent3_quot: 0,
            input_term_idx: input,
            result_term_idx: result,
        }
    }

    pub fn ty_ind_rec(
        input: usize,
        result: usize,
        max_binding: usize,
        parent0: usize,
        parent1: usize,
    ) -> ExpRule {
        ExpRule {
            rule: RULE_TYPE_IND_REC,
            ctx_idx: HashList::EMPTY,
            max_binding,
            parent0,
            parent1,
            parent2: 0,
            parent3: 0,
            parent0_quot: 0,
            parent1_quot: 0,
            parent2_quot: 0,
            parent3_quot: 0,
            input_term_idx: input,
            result_term_idx: result,
        }
    }

    pub fn ind_pref(input: usize, result: usize, n: usize, elim: usize, parent0: usize) -> ExpRule {
        ExpRule {
            rule: RULE_IND_PREFIX,
            ctx_idx: HashList::EMPTY,
            max_binding: 0,
            parent0,
            parent1: 0,
            parent2: 0,
            parent3: 0,
            parent0_quot: n,
            parent1_quot: elim,
            parent2_quot: 0,
            parent3_quot: 0,
            input_term_idx: input,
            result_term_idx: result,
        }
    }

    //pub fn alpha(term: usize, result: usize, parent0: usize, parent0_quoti
}

#[derive(Debug, Clone)]
struct HashList {
    alpha: usize,
    beta: usize,
    nodes: Vec<HashNode>,

    // map from hashes to hash nodes...
    node_mapping: HashMap<usize, usize>,
    max_names: HashMap<usize, usize>,
    //set_mapping: HashMap<BTreeSet<usize>, usize>,
}

// TODO: permute, etc....
impl HashList {
    // TODO: is this fine?
    const EMPTY: usize = usize::MAX;

    fn new() -> HashList {
        println!("empty is: {}", Self::EMPTY);
        let mut max_names = HashMap::new();
        max_names.insert(HashList::EMPTY, 0);
        HashList {
            alpha: rand::random::<usize>(),
            beta: rand::random::<usize>(),
            nodes: Vec::new(),
            node_mapping: HashMap::new(),
            max_names,
        }
    }

    pub fn add(&mut self, list: usize, key: usize, value: usize) -> usize {
        if self.contains(list, key, value) {
            return list;
        }
        println!(
            "adding ({}, {}) to zk_context: {}",
            key,
            value,
            self.to_string(list)
        );

        let prev_hash = if list != HashList::EMPTY {
            let list_head = &self.nodes[list];
            list_head.hash
        } else {
            1
        };
        let expected_hash = (self.hash(key, value) * Wrapping(prev_hash)).0;

        if let Some(cached) = self.node_mapping.get(&expected_hash) {
            return *cached;
        }

        let node = HashNode {
            key,
            value,

            hash: expected_hash,
            prev_hash,
            prev: list,
        };

        //assert!(key >= *self.max_names.get(&list).unwrap());

        self.nodes.push(node);
        self.node_mapping
            .insert(expected_hash, self.nodes.len() - 1);
        self.max_names.insert(self.nodes.len() - 1, key + 1);
        self.nodes.len() - 1
    }

    // TODO unused
    pub fn fresh_name(&self, list: usize) -> usize {
        *self.max_names.get(&list).unwrap()
    }

    pub fn hash(&self, key: usize, value: usize) -> Wrapping<usize> {
        Wrapping(self.alpha) - Wrapping(value) - Wrapping(self.beta) * Wrapping(key)
    }

    // TODO: rewrite this to be better
    pub fn contains(&self, list: usize, key: usize, value: usize) -> bool {
        //println!("checking if ({}, {}) is in {}", key, value, list);
        if list == HashList::EMPTY {
            return false;
        }

        let list_head = &self.nodes[list];
        //println!(
        //    "list hash: {:?}, this hash: {:?}",
        //    list_head.hash,
        //    self.hash(key, value)
        //);
        let rem = Wrapping(list_head.hash) % (self.hash(key, value));
        println!("got: {:?}", rem);
        rem.0 == 0
    }

    pub fn contains_hash(&self, list: usize, kv_hash: usize, remainder: usize) -> bool {
        if list == HashList::EMPTY {
            return false;
        }

        let list_hash = self.nodes[list].hash;

        let remainder_hash = if remainder == HashList::EMPTY {
            1
        } else {
            self.nodes[remainder].hash
        };
        //println!(
        //    "list hash: {:?}, this hash: {:?}",
        //    list_head.hash,
        //    self.hash(key, value)
        //);
        Wrapping(list_hash) - Wrapping(remainder_hash) * Wrapping(kv_hash) == Wrapping(0)
    }

    /// check if the passed in list is a subset, given the passed in remainder
    pub fn subset(&self, list: usize, subset: usize, remainder: usize) -> bool {
        let list_hash = if list == HashList::EMPTY {
            1
        } else {
            self.nodes[list].hash
        };

        let subset_hash = if subset == HashList::EMPTY {
            1
        } else {
            self.nodes[subset].hash
        };

        let remainder_hash = if remainder == HashList::EMPTY {
            1
        } else {
            self.nodes[remainder].hash
        };

        Wrapping(list_hash) - Wrapping(remainder_hash) * Wrapping(subset_hash) == Wrapping(0)
    }

    // TODO:
    /// splits a list into a subset, adding the remainder to the list and outputing
    /// its index
    /// TODO: keep referential indices as well...e.g. Bound(4) -> Bound(3) -> Sort(1)
    pub fn split(&mut self, list: usize, subset: HashSet<usize>) -> (usize, usize) {
        if subset.is_empty() {
            return (HashList::EMPTY, list);
        }

        let mut list = list;
        let mut subset_list = HashList::EMPTY;
        let mut quot_list = HashList::EMPTY;
        let mut subset = subset;
        while list != HashList::EMPTY {
            let key = self.nodes[list].key;
            let value = self.nodes[list].value;
            if subset.contains(&key) {
                subset_list = self.add(subset_list, key, value);
                subset.remove(&key);
            } else {
                quot_list = self.add(quot_list, key, value);
            }

            list = self.nodes[list].prev;
        }

        //if !subset.is_empty() {
        //    panic!("subset wasn't contained in original list!");
        //}

        (subset_list, quot_list)
    }

    pub fn remove(&mut self, list: usize, key: usize, value: usize) -> usize {
        println!(
            "removing: ({}, {}) from {}",
            key,
            value,
            self.to_string(list)
        );
        let mut list = list;
        let mut subset_list = HashList::EMPTY;
        while list != HashList::EMPTY {
            let l_key = self.nodes[list].key;
            let l_value = self.nodes[list].value;
            if l_key != key || l_value != value {
                subset_list = self.add(subset_list, l_key, l_value);
            } else if l_key == key && l_value != value {
                panic!("keys aren't equal!");
            }

            list = self.nodes[list].prev;
        }

        subset_list
    }

    pub fn equals(&self, l1: usize, l2: usize) -> bool {
        match (l1, l2) {
            (HashList::EMPTY, HashList::EMPTY) => true,
            (HashList::EMPTY, _) | (_, HashList::EMPTY) => false,
            (l1, l2) => self.nodes[l1].hash == self.nodes[l2].hash,
        }
    }

    pub fn check_optimality(&self) {
        // TODO:
        // Basically just ensure there aren't any duplicated sets
    }

    pub fn to_string(&self, list: usize) -> String {
        let mut res = "[".to_owned();
        let mut list = list;
        while list != HashList::EMPTY {
            res = res + &format!("({}, {}),", self.nodes[list].key, self.nodes[list].value);
            list = self.nodes[list].prev;
        }
        res += "]";
        res
    }

    //    pub fn keys_split(&self, list: usize, keys: HashSet<usize>) -> (usize, usize) {
    //        if list == HashList::EMPTY {
    //            assert!(keys.empty());
    //            return (HashList::EMPTY, HashList::EMPTY);
    //        }
    //
    //        let mut list = list;
    //        // TODO: this is wasteful...we don't care about ordering here...
    //        let mut subset = HashList::EMPTY;
    //        let mut quot = HashList::EMPTY;
    //
    //        while list != HashList::EMPTY {
    //
    //        }
    //        let list_node = &self.nodes[list];
    //
    //        while list_node.
    //    }

    ///// TODO: membership

    // permute the list such that `key` is in front
    //fn permute(&mut self, list: usize, key: usize) -> usize {
    //    if list == HashList::EMPTY {
    //        panic!("cannot permute empty list!");
    //    }

    //    // look up the key node
    //    let mut node = self.nodes[list];
    //    let mut head = vec![];
    //    loop {
    //        if node.key == key {
    //            break;
    //        }

    //        if node.prev == HashList::EMPTY {
    //            panic!("Couldn't find key {} in permute!", key);
    //        }

    //        head.push(node);
    //        node = self.nodes[node.prev];
    //    }

    //    let mut tail = node.prev;
    //    for node in head.reverse() {
    //        tail = self.push(tail, node.key, node.value);
    //    }

    //    self.push(tail, node.key, node.value);
    //}
}

#[derive(Debug, Clone)]
struct HashNode {
    key: usize,
    value: usize,
    hash: usize,

    // stash the value of the prev_hash to reduce lookups
    prev_hash: usize,
    prev: usize,
}

#[derive(Debug, Clone)]
pub struct ZkInput {
    rules: Vec<ExpRule>,
    terms: Vec<ExpTerm>,
    public_terms: Vec<ExpTerm>,
    axioms_end: usize,
    expected_type: usize,
    proving_rule: usize,

    inductives: Vec<ExpInd>,

    contexts: HashList,
}

impl ZkInput {
    fn new() -> ZkInput {
        ZkInput {
            rules: Vec::new(),
            terms: Vec::new(),
            public_terms: Vec::new(),
            axioms_end: 0,
            expected_type: 0,
            proving_rule: 0,

            inductives: Vec::new(),

            contexts: HashList::new(),
        }
    }
}

/// For now, just takes a single theorem
pub struct Exporter {
    eval: Evaluator,
    zk_input: ZkInput,

    inductives: HashMap<String, Inductive>,

    axiom_mapping: HashMap<String, (usize, usize)>,
    ax_test: HashMap<usize, usize>,
    axiom_rev_mapping: HashMap<(usize, usize), String>,

    // Name -> Inductive idx
    inductive_mapping: HashMap<String, usize>,
    // (IndName, CtorName) -> Rule idx
    inductive_rule_mapping: HashMap<(String, String), usize>,
    ind_rev_map: HashMap<usize, String>,

    //inductive_elim_mapping: HashMap<String, usize>,
    term_cache: HashMap<(Term, usize), usize>,
    zk_term_cache: HashMap<ExpTerm, usize>,
    zk_rule_cache: HashMap<ExpRule, usize>,

    zk_term_free_bindings: HashMap<usize, HashSet<usize>>,
}

impl Exporter {
    fn new() -> Exporter {
        Exporter {
            eval: Evaluator::new::<String, _>(&[], HashMap::new()),
            zk_input: ZkInput::new(),

            inductives: HashMap::new(),

            axiom_mapping: HashMap::new(),
            ax_test: HashMap::new(),
            axiom_rev_mapping: HashMap::new(),

            // TODO
            inductive_mapping: HashMap::new(),
            inductive_rule_mapping: HashMap::new(),
            ind_rev_map: HashMap::new(),

            term_cache: HashMap::new(),
            zk_term_cache: HashMap::new(),
            zk_rule_cache: HashMap::new(),

            zk_term_free_bindings: HashMap::new(),
        }
    }

    pub fn with_axioms(
        expected_type: Term,
        axioms: HashMap<String, Term>,
        inductives: HashMap<String, Inductive>,
    ) -> Exporter {
        let mut exp = Exporter::new();

        exp.inductives = inductives;

        for (name, term) in &axioms {
            exp.add_axiom_term(name.to_string(), term.clone(), &axioms);
        }

        //println!("adding inductives...");
        ////for (name, ind) in &inductives {
        ////    exp.add_inductive(ind);
        ////}
        //println!("done");

        exp.zk_input.axioms_end = exp.zk_input.terms.len();

        let term = exp.export_term(expected_type, 0, None);

        for t in &exp.zk_input.terms {
            exp.zk_input.public_terms.push(t.clone());
        }

        exp.zk_input.expected_type = term;
        exp
    }

    fn add_inductive(&mut self, inductive: &Inductive) {
        println!("exporting ty for ind {}", inductive.name);
        let ind_type = self.export_term(inductive.ty.clone(), 0, None);
        let ind = ExpInd {
            ty: ind_type,
            num_params: inductive.num_params,
            rules: [0; MAX_RULES],
            rule_nnrs: [0; MAX_RULES],
            rule_nrs: [0; MAX_RULES],
            num_rules: 0,
            rec_body: 0,
            elim_argc: 0,
        };
        let ind_idx = self.add_zk_ind(ind);
        self.inductive_mapping
            .insert(inductive.name.clone(), ind_idx);
        self.ind_rev_map.insert(ind_idx, inductive.name.clone());

        for i in 0..inductive.rules.len() {
            println!(
                "exporting rule {} for ind {}",
                inductive.rules[i].name, inductive.name
            );
            // TODO: need to add inductive for proper type...
            self.zk_input.inductives[ind_idx].rules[i] =
                self.export_term(inductive.rules[i].ty.clone(), 0, None);
            self.zk_input.inductives[ind_idx].rule_nnrs[i] =
                inductive.num_nonrecursive_args_for_rule(i);
            self.zk_input.inductives[ind_idx].rule_nrs[i] =
                inductive.num_recursive_args_for_rule(i);

            self.inductive_rule_mapping
                .insert((inductive.name.clone(), inductive.rules[i].name.clone()), i);
        }

        // TODO:
        let rec_body = &inductive.elim_body;
        println!("exporting rec");

        // add "bindings" for ind params and motive...
        let rec_zk_body = self.export_term(rec_body.clone(), inductive.num_params + 1, None);
        let mut_zk_ind = self.get_zk_ind_mut(ind_idx);
        mut_zk_ind.rec_body = rec_zk_body;
        mut_zk_ind.elim_argc = rec_body.params().len() + inductive.num_params + 1;
    }

    fn new_with_eval(eval: Evaluator) -> Exporter {
        Exporter {
            eval,
            zk_input: ZkInput::new(),

            inductives: HashMap::new(),

            axiom_mapping: HashMap::new(),
            ax_test: HashMap::new(),
            axiom_rev_mapping: HashMap::new(),

            // TODO
            inductive_mapping: HashMap::new(),
            inductive_rule_mapping: HashMap::new(),
            ind_rev_map: HashMap::new(),

            term_cache: HashMap::new(),
            zk_term_cache: HashMap::new(),
            zk_rule_cache: HashMap::new(),

            zk_term_free_bindings: HashMap::new(),
        }
    }

    // TODO: add exp again
    pub fn simulate(theorem: Theorem) -> Result<(), String> {
        let mut context = Context::new();
        let mut eval = Evaluator::new(&theorem.axioms, theorem.inductives.clone());
        let mut axioms = theorem.axioms;

        // TODO: fix
        //for (name, inductive) in theorem.inductives {
        //    //println!("inserting inductive: {}", name);
        //    axioms.insert(name, inductive.ty);
        //    for rule in inductive.rules {
        //        axioms.insert(rule.name, rule.ty);
        //    }
        //}

        //let mut exporter = Exporter::new_with_eval(eval);
        //println!("axioms: {:?}", axioms);
        let simplified_ty = eval.eval(theorem.ty.clone()).unwrap();
        let mut exporter = Exporter::with_axioms(simplified_ty, axioms, theorem.inductives);

        //println!("exp_axioms: {:?}", exporter.axiom_mapping);
        let simplified_val = eval.eval(theorem.val.clone()).unwrap();
        let simplified_ty = eval.eval(theorem.ty.clone()).unwrap();
        println!("proving: {:?} :: {:?}", simplified_val, simplified_ty);
        let rule = exporter.export_ty_term(simplified_val)?;
        let result_type = exporter.get_zk_rule(rule).result_term_idx;

        if result_type != exporter.zk_input.expected_type {
            println!(
                "attempting to unify final types {} and {}",
                term_to_string(
                    result_type,
                    &exporter.zk_input.terms,
                    &exporter.axiom_rev_mapping,
                    &exporter.ind_rev_map
                ),
                term_to_string(
                    exporter.zk_input.expected_type,
                    &exporter.zk_input.terms,
                    &exporter.axiom_rev_mapping,
                    &exporter.ind_rev_map
                )
            );

            let rule = exporter.export_unify(rule, exporter.zk_input.expected_type)?;
            exporter.zk_input.proving_rule = rule;
        } else {
            exporter.zk_input.proving_rule = rule;
        }

        // remove this later.. check for now...
        sim::simulate(
            exporter.zk_input.clone(),
            true,
            &exporter.axiom_rev_mapping,
            &exporter.ind_rev_map,
        );

        Ok(())
    }

    fn export_ind_pref(
        &mut self,
        input_idx: usize,  // this is the rec
        result_idx: usize, // this is the inductive type
        n: usize,
        elim: usize,
    ) -> Result<usize, String> {
        let rule = if n == 0 {
            ExpRule::ind_pref(input_idx, result_idx, n, elim, 0)
        } else {
            let rec = self.get_zk_term(input_idx);
            let ind_ty = self.get_zk_term(result_idx);

            assert!(rec.kind == EXPR_PI && ind_ty.kind == EXPR_PI);
            assert!(rec.left == ind_ty.left);

            let parent = self.export_ind_pref(rec.right, ind_ty.right, n - 1, elim)?;
            ExpRule::ind_pref(input_idx, result_idx, n, elim, parent)
        };

        let rule_idx = self.add_zk_rule(rule);
        Ok(rule_idx)
    }

    // TODO: this isn't used anywhere??????
    fn export_apply_elim_eval(
        &mut self,
        input_idx: usize,
        zk_context: usize,
        context: &mut HashMap<usize, usize>,
        max_binding: usize,
        rec_idx: usize,
        elim_idx: usize,
        nonrec_params: usize,
        rec_params: usize,
    ) -> Result<usize, String> {
        println!("begin eval elim");
        let apply_elim_rule =
            self.export_apply_elim(input_idx, rec_idx, elim_idx, nonrec_params, rec_params)?;
        let res = self.get_zk_rule(apply_elim_rule).result_term_idx;
        println!(
            "trace eval elim (max binding: {}): {} => {}",
            max_binding,
            term_to_string(
                input_idx,
                &self.zk_input.terms,
                &self.axiom_rev_mapping,
                &self.ind_rev_map
            ),
            term_to_string(
                res,
                &self.zk_input.terms,
                &self.axiom_rev_mapping,
                &self.ind_rev_map
            )
        );

        let eval_rule = self.export_eval(res, zk_context, context, max_binding);
        let eval_res_idx = self.get_zk_rule(eval_rule).result_term_idx;

        let rule = ExpRule::apply_elim_eval(
            input_idx,
            eval_res_idx,
            rec_idx,
            elim_idx,
            nonrec_params,
            rec_params,
            zk_context,
            max_binding,
            apply_elim_rule,
            eval_rule,
        );
        Ok(self.add_zk_rule(rule))
    }

    fn export_apply_elim(
        &mut self,
        input_idx: usize,
        rec_idx: usize,
        elim_idx: usize,
        nonrec_params: usize,
        rec_params: usize,
    ) -> Result<usize, String> {
        let input = self.get_zk_term(input_idx).clone();

        // TODO: remove eval from this entirly...means no context which means
        //       nice compression....

        //          f.tlf == ind_i
        // --------------------------------                 (apply_base)
        // elim_apply 0 0 e_i elim f => e_i
        if nonrec_params == 0 && rec_params == 0 {
            let result_idx = elim_idx;
            let rule = ExpRule::apply_elim(
                input_idx,
                result_idx,
                rec_idx,
                elim_idx,
                HashList::EMPTY,
                0,
                0,
                0,
            );
            Ok(self.add_zk_rule(rule))
        //  elim_apply (nnr-1) 0 e_i rec f => f'
        // --------------------------------------           (apply_nonrec)
        //  elim_apply nnr 0 e_i (f e) => (f' e)
        } else if rec_params == 0 {
            assert!(input.kind == EXPR_APP);
            let f = input.left;
            let e = input.right;
            let parent0_idx =
                self.export_apply_elim(f, rec_idx, elim_idx, nonrec_params - 1, rec_params)?;
            let fp = self.get_zk_rule(parent0_idx).result_term_idx;
            let fp_tlf = self.get_zk_term(fp).top_level_func;
            let result_term = ExpTerm::app(fp, e, fp_tlf);
            let result_idx = self.add_zk_term(result_term);

            // let parent1_idx =
            //     self.export_eval(app_fp_e_idx, HashList::EMPTY, &mut HashMap::new(), 0);
            //let result_idx = self.get_zk_rule(parent1_idx).result_term_idx;

            let rule = ExpRule::apply_elim(
                input_idx,
                result_idx,
                rec_idx,
                elim_idx,
                HashList::EMPTY,
                nonrec_params,
                rec_params,
                parent0_idx,
            );
            Ok(self.add_zk_rule(rule))

        // elim_apply nnr (nr-1) e_i rec f => f'
        // ----------------------------------------------    (apply_rec)
        //  elim_apply nnr nr e_i (f e) => (f' (rec e))
        } else {
            assert!(input.kind == EXPR_APP);

            let f = input.left;
            let e = input.right;
            let parent0_idx =
                self.export_apply_elim(f, rec_idx, elim_idx, nonrec_params, rec_params - 1)?;
            let fp = self.get_zk_rule(parent0_idx).result_term_idx;
            let fp_tlf = self.get_zk_term(fp).top_level_func;

            // TODO: this is probably wrong
            let app_rec_e = ExpTerm::app(rec_idx, e, rec_idx);
            let app_rec_e_idx = self.add_zk_term(app_rec_e);

            let app_fp_rec = ExpTerm::app(fp, app_rec_e_idx, fp_tlf);
            let result_idx = self.add_zk_term(app_fp_rec);

            let rule = ExpRule::apply_elim(
                input_idx,
                result_idx,
                rec_idx,
                elim_idx,
                HashList::EMPTY,
                nonrec_params,
                rec_params,
                parent0_idx,
            );
            Ok(self.add_zk_rule(rule))
        }
    }

    fn export_get_arg(&mut self, input_idx: usize, arg_c: usize) -> Result<usize, String> {
        let input = self.get_zk_term(input_idx).clone();

        assert!(input.kind == EXPR_APP);

        if arg_c == 0 {
            let result_idx = input.right;
            let rule = ExpRule::get_arg(input_idx, result_idx, 0, 0);
            Ok(self.add_zk_rule(rule))
        } else {
            let parent0 = self.export_get_arg(input.left, arg_c - 1)?;
            let result_idx = self.get_zk_rule(parent0).result_term_idx;
            let rule = ExpRule::get_arg(input_idx, result_idx, arg_c, parent0);
            Ok(self.add_zk_rule(rule))
        }
    }

    // TODO: move below
    // TODO: Inefficient. Better would be to walk up existing tree and do repair
    //       where we need
    fn export_unify(&mut self, rule_idx: usize, expected_type: usize) -> Result<usize, String> {
        let rule = self.get_zk_rule(rule_idx).clone();

        let eval_rule = self.export_unify_helper(
            rule.result_term_idx,
            expected_type,
            HashList::EMPTY,
            &mut HashMap::new(),
            0,
        )?;

        let ty_rule = ExpRule::eval_ty(
            rule.input_term_idx,
            expected_type,
            HashList::EMPTY,
            0,
            rule_idx,
            eval_rule,
        );

        Ok(self.add_zk_rule(ty_rule))
    }

    // TODO: add two things here:
    //      1. Eta expation
    //      2. Recursion elimination
    //          - TBH this version of recursion elim could be good...e.g. do it
    //              lazily when we have a problem
    fn export_unify_helper(
        &mut self,
        result_type: usize,
        expected_type: usize,
        zk_context: usize,
        context: &mut HashMap<usize, usize>,
        max_binding: usize,
    ) -> Result<usize, String> {
        let result = self.get_zk_term(result_type).clone();
        let expected = self.get_zk_term(expected_type).clone();

        if result_type == expected_type {
            let rule = ExpRule::eval_id(result_type, zk_context, max_binding);
            return Ok(self.add_zk_rule(rule));
        }

        let rule = match (result.kind, expected.kind) {
            (EXPR_PI, EXPR_PI) => {
                let res_dom = result.left;
                let exp_dom = expected.left;
                //let (domain_subs, domain_quot) = self.split_zk_context(zk_context, res_dom);

                let domain_rule = if res_dom != exp_dom {
                    self.export_unify_helper(res_dom, exp_dom, zk_context, context, max_binding)?
                } else {
                    let rule = ExpRule::eval_id(res_dom, zk_context, max_binding);
                    self.add_zk_rule(rule)
                };

                let res_bod = result.right;
                let exp_bod = expected.right;
                context.insert(result.name, exp_dom);
                let new_context = self.zk_context_insert(zk_context, result.name, exp_dom);
                // TODO: need a union of contexts to split...
                //let (body_subs, body_quot) = self.split_zk_context(new_context, res_bod);

                let body_rule = if res_bod != exp_bod {
                    self.export_unify_helper(
                        res_bod,
                        exp_bod,
                        new_context,
                        context,
                        max_binding + 1,
                    )?
                } else {
                    let rule = ExpRule::eval_id(res_bod, zk_context, max_binding);
                    self.add_zk_rule(rule)
                };

                ExpRule::eval_pi(
                    result_type,
                    expected_type,
                    zk_context,
                    domain_rule,
                    HashList::EMPTY,
                    body_rule,
                    HashList::EMPTY,
                    max_binding,
                )
            }
            (EXPR_LAM, EXPR_LAM) => {
                panic!("cannot unify lam! not a type!")
            }
            (EXPR_APP, EXPR_APP) => {
                let res_f = result.left;
                let exp_f = expected.left;
                //let (f_subs, f_quot) = self.split_zk_context(zk_context, res_f);

                let res_e = result.right;
                let exp_e = expected.right;
                //let (e_subs, e_quot) = self.split_zk_context(zk_context, res_e);

                let f_rule = if res_f != exp_f {
                    // recurse
                    self.export_unify_helper(res_f, exp_f, zk_context, context, max_binding)?
                } else {
                    let rule = ExpRule::eval_id(res_f, zk_context, max_binding);
                    self.add_zk_rule(rule)
                };

                let e_rule = if res_e != exp_e {
                    // recurse
                    self.export_unify_helper(res_e, exp_e, zk_context, context, max_binding)?
                } else {
                    let rule = ExpRule::eval_id(res_e, zk_context, max_binding);
                    self.add_zk_rule(rule)
                };

                ExpRule::eval_app(
                    result_type,
                    expected_type,
                    zk_context,
                    f_rule,
                    HashList::EMPTY,
                    e_rule,
                    HashList::EMPTY,
                    max_binding,
                )
                // make the rule
            }
            _ => {
                // attempt proof_irrel unification
                println!(
                    "attempting to unify {} and {}",
                    term_to_string(
                        result_type,
                        &self.zk_input.terms,
                        &self.axiom_rev_mapping,
                        &self.ind_rev_map
                    ),
                    term_to_string(
                        expected_type,
                        &self.zk_input.terms,
                        &self.axiom_rev_mapping,
                        &self.ind_rev_map
                    )
                );
                println!("ctx: {:?}", context);
                println!("zk ctx: {}", self.zk_input.contexts.to_string(zk_context));

                let res_ty_rule = self.export_ty(result_type, zk_context, context, max_binding)?;
                let exp_ty_rule =
                    self.export_ty(expected_type, zk_context, context, max_binding)?;
                let res_ty_idx = self.get_zk_rule(res_ty_rule).result_term_idx;
                let exp_ty_idx = self.get_zk_rule(exp_ty_rule).result_term_idx;

                let ty_ty_rule = self.export_ty(res_ty_idx, zk_context, context, max_binding)?;
                let ty_ty_idx = self.get_zk_rule(ty_ty_rule).result_term_idx;
                let ty_ty_term = self.get_zk_term(ty_ty_idx);

                if !(res_ty_idx == exp_ty_idx
                    && ty_ty_term.kind == EXPR_SORT
                    && ty_ty_term.name == 0)
                {
                    return Err(format!(
                        "Failed to unify terms {} and {}",
                        term_to_string(
                            result_type,
                            &self.zk_input.terms,
                            &self.axiom_rev_mapping,
                            &self.ind_rev_map
                        ),
                        term_to_string(
                            expected_type,
                            &self.zk_input.terms,
                            &self.axiom_rev_mapping,
                            &self.ind_rev_map
                        ),
                    ));
                }
                ExpRule::proof_irrel(
                    result_type,
                    expected_type,
                    zk_context,
                    max_binding,
                    res_ty_rule,
                    exp_ty_rule,
                    ty_ty_rule,
                )
            }
        };

        Ok(self.add_zk_rule(rule))
    }

    fn add_axiom_term(&mut self, name: String, term: Term, axioms: &HashMap<String, Term>) {
        let term = self.export_term(term, 0, Some(axioms));

        if !self.axiom_mapping.contains_key(&name) {
            let new_tag = if let Some(tag) = self.ax_test.get(&term) {
                tag + 1
            } else {
                0
            };
            self.axiom_mapping.insert(name.clone(), (term, new_tag));
            self.axiom_rev_mapping.insert((term, new_tag), name);
            self.ax_test.insert(term, new_tag);
        }
    }

    pub fn export_eval_term(&mut self, input: Term) -> usize {
        let term = self.export_term(input, 0, None);
        self.export_eval(term, HashList::EMPTY, &mut HashMap::new(), 0)
    }

    pub fn export_ty_term(&mut self, input: Term) -> Result<usize, String> {
        let term = self.export_term(input, 0, None);
        self.export_ty(term, HashList::EMPTY, &mut HashMap::new(), 0)
    }

    // OKKKK LETS DO IT.....
    // This basically functionally acts as a lift...
    // We only increment all variables that are greater than the
    // the minimum bound variable inside the term...
    // This is because of our convention that free variables in a term
    // must be less than minimum binding in a term
    //pub fn export_alpha_term(&mut self, term_idx: usize, by: usize, min_binding: usize) -> usize {
    //    let term = self.get_zk_term(term_idx);

    //    match term {
    //        EXPR_VAR => {}
    //    }
    //}

    // TODO: must make sure that terms always increase the binding...e.g.
    //       you can never have a valid term such that a free variable is
    //       larger than an binding
    //   e => e'  e =alpha=> a  e' =alpha=> a'
    // ---------------------------------------
    //             a => a'
    //pub fn export_alpha(
    //    &mut self,
    //    input_idx: usize,
    //    result_idx: usize,
    //    zk_context: usize,
    //    context: &mut HashMap<usize, usize>,
    //    max_binding: usize,
    //) -> usize {
    //    let input = self.get_zk_term(input_idx).clone();
    //    let result = self.get_zk_term(result_idx).clone();

    //    // debug assert: should only rename terms that clash
    //    assert!(input.min_binding < max_binding || result.min_binding < max_binding);

    //    // Steps:
    //    // 1. Create renamed input term
    //    // 2. Create renamed result term
    //    // 3. TODO: this works for both eval and types...just ensure that the
    //    //          result rule is the same gottem
    //}
    //

    // DeBruijn levels...
    // On subst -> lift proof
    // On app -> unlift proof
    // alpha ... todo: basicallly:
    //  - relaxed debruijn levels -> no renaming on unlift unless necessary
    //
    //  Partial Evaluation:
    //      - I BELEIVE it is okay...need to prove it to myself better.
    //      - Proof relies on the fact that it becomes impossible to rebind
    //          the term to another binder...it will always remain some
    //          floating free term which is unallowed in final proof types.
    //      - If its not okay, here is the solution I believe:
    //          1. type -> panic..easy
    //          2. eval ->
    //              - Just ensure the minimum binding inside the resultant term is
    //                greater than the current level?

    // TODO: add id compression...basically find terms that eval to same and compress..
    /// max name that has been bound already
    /// all new names must be >= max name to prevent collisions.
    /// May be reset using an alpha step.
    /// TODO: terms carry a max_binding and contexts carry a min_bininding
    ///       any substitution requires that the min_binding <= max_binding (which is unused)
    ///
    pub fn export_eval(
        &mut self,
        input_idx: usize,
        zk_context: usize,
        context: &mut HashMap<usize, usize>,
        max_binding: usize,
    ) -> usize {
        //let input_idx = self.add_zk_term(input.clone());
        //
        let input = self.get_zk_term(input_idx).clone();
        //let (subset_ctx, quotient_ctx) = self.(input_idx, zk_context);

        // TODO: use eval function ... but not today
        //let result = self.eval.eval_with_context(input.clone(), &mut context

        println!(
            "start eval: {}",
            term_to_string(
                input_idx,
                &self.zk_input.terms,
                &self.axiom_rev_mapping,
                &self.ind_rev_map
            )
        );
        //println!(
        //    "exp_eval: {}, PI TERM IS: {}",
        //    max_binding,
        //    term_to_string(input_idx, &self.zk_input.terms, &self.axiom_rev_mapping)
        //);
        let zk_rule = match input.kind {
            // TODO: make sure that we use levels in the circuit, but indicies out here...
            EXPR_VAR => {
                // lift here...
                let level = input.name;
                //println!(
                //    "Export eval var: {:?}, zk_context: {:?}, actual: {:?}",
                //    term_to_string(input_idx, &self.zk_input.terms, &self.axiom_rev_mapping),
                //    self.zk_input.contexts.to_string(zk_context),
                //    context
                //);
                //println!("evaling var... got level {:?}", level);
                //println!("current context {:?}", context);
                // we look up the index in the zk_context...
                if let Some(result_idx) = context.get(&level) {
                    let lifted_rule = self.export_lift(*result_idx, max_binding, usize::MAX);
                    let lifted_idx = self.get_zk_rule(lifted_rule).result_term_idx;
                    //println!(
                    //    "CHECK THIS: {} == {}",
                    //    self.get_zk_rule(lifted_rule).input_term_idx,
                    //    *result_idx
                    //);
                    let ctx_rem =
                        self.zk_input
                            .contexts
                            .remove(zk_context, input.name, *result_idx);
                    ExpRule::eval_var(
                        input_idx,
                        lifted_idx,
                        zk_context,
                        max_binding,
                        lifted_rule,
                        ctx_rem,
                    )
                } else {
                    ExpRule::eval_id(input_idx, zk_context, max_binding)
                }
            }
            EXPR_SORT => {
                //println!("eval sort");
                ExpRule::eval_id(input_idx, zk_context, max_binding)
            }
            EXPR_APP => {
                //println!(
                //    "eval app: {} |- {:?} => ??",
                //    self.zk_input.contexts.to_string(zk_context),
                //    term_to_string(input_idx, &self.zk_input.terms, &self.axiom_rev_mapping),
                //    //to_term(result_idx, &self.zk_input.terms, &self.axiom_rev_mapping)
                //);

                let f = input.left;
                let e = input.right;

                let (f_subs, f_quot) = self.split_zk_context(zk_context, f, context);
                let f_rule = self.export_eval(f, f_subs, context, max_binding);

                let (e_subs, e_quot) = self.split_zk_context(zk_context, e, context);
                let e_rule = self.export_eval(e, e_subs, context, max_binding);

                let f_result = self.zk_input.rules[f_rule].result_term_idx;
                let e_result = self.zk_input.rules[e_rule].result_term_idx;

                let f_term = self.get_zk_term(f_result);
                if f_term.kind == EXPR_LAM {
                    let name = f_term.name;
                    assert!(name == max_binding);
                    //println!("name is {:?}", name);
                    let body = f_term.right;
                    context.insert(name, e_result);
                    let new_context = self.zk_context_insert(f_subs, name, e_result);
                    let value_rule = self.export_eval(body, new_context, context, max_binding + 1);
                    //let value_idx = self.export_eval(
                    context.remove(&name);

                    let value_idx = self.get_zk_rule(value_rule).result_term_idx;

                    let lift_rule = self.export_lift(value_idx, max_binding, usize::MAX);
                    let zk_result_idx = self.get_zk_rule(lift_rule).result_term_idx;

                    // TODO: unlifting proof for bound variables
                    ExpRule::eval_app_lam(
                        input_idx,
                        zk_result_idx,
                        zk_context,
                        f_rule,
                        f_quot,
                        e_rule,
                        e_quot,
                        value_rule,
                        lift_rule,
                        max_binding,
                    )
                } else {
                    let e_term = self.get_zk_term(e_result);
                    //let min_binding = min(f_term.min_binding, e_term.min_binding);
                    let zk_result = ExpTerm::app(f_result, e_result, f_term.top_level_func);
                    let result_idx = self.add_zk_term(zk_result);

                    //APP lambda or pi
                    ExpRule::eval_app(
                        input_idx,
                        result_idx,
                        zk_context,
                        f_rule,
                        f_quot,
                        e_rule,
                        e_quot,
                        max_binding,
                    )
                }
            }
            EXPR_LAM => {
                //println!("eval lam");

                let name = input.name;
                assert_eq!(name, max_binding);

                let domain = input.left;
                let body = input.right;

                let (body_subs, body_quot) = self.split_zk_context(zk_context, body, context);
                let body_rule = self.export_eval(body, body_subs, context, max_binding + 1);
                let body_result = self.get_zk_rule(body_rule).result_term_idx;
                let body_term = self.get_zk_term(body_result);
                //let min_name_used = body_term.min_binding;

                // TODO: is this right?
                let zk_result = ExpTerm::lam(name, domain, body_result);
                let result_idx = self.add_zk_term(zk_result);

                ExpRule::eval_lam(
                    input_idx,
                    result_idx,
                    zk_context,
                    body_rule,
                    body_quot,
                    max_binding, // TODO: need to check this stuff
                )
            }
            EXPR_PI => {
                //println!("eval pi");

                println!(
                    "max_binding: {}, PI TERM IS: {}",
                    max_binding,
                    term_to_string(
                        input_idx,
                        &self.zk_input.terms,
                        &self.axiom_rev_mapping,
                        &self.ind_rev_map
                    )
                );
                let name = input.name;
                assert!(name == max_binding);
                let domain = input.left;
                let body = input.right;

                let (domain_subs, domain_quot) = self.split_zk_context(zk_context, domain, context);
                let domain_rule = self.export_eval(domain, domain_subs, context, max_binding);
                let domain_result = self.get_zk_rule(domain_rule).result_term_idx;

                println!(
                    "domain done: {}",
                    term_to_string(
                        input_idx,
                        &self.zk_input.terms,
                        &self.axiom_rev_mapping,
                        &self.ind_rev_map
                    )
                );

                let (body_subs, body_quot) = self.split_zk_context(zk_context, body, context);
                let body_rule = self.export_eval(body, body_subs, context, max_binding + 1);
                let body_result = self.get_zk_rule(body_rule).result_term_idx;

                println!(
                    "body done: {}",
                    term_to_string(
                        input_idx,
                        &self.zk_input.terms,
                        &self.axiom_rev_mapping,
                        &self.ind_rev_map
                    )
                );

                // TODO: naming correct?
                let zk_result = ExpTerm::pi(name, domain_result, body_result);
                let result_idx = self.add_zk_term(zk_result);

                ExpRule::eval_pi(
                    input_idx,
                    result_idx,
                    zk_context,
                    domain_rule,
                    domain_quot,
                    body_rule,
                    body_quot,
                    max_binding,
                )
            }
            EXPR_AXIOM => ExpRule::eval_id(input_idx, zk_context, max_binding),
            _ => {
                unimplemented!()
            }
        };
        println!(
            "trace eval (max binding: {}): {} => {}",
            max_binding,
            term_to_string(
                input_idx,
                &self.zk_input.terms,
                &self.axiom_rev_mapping,
                &self.ind_rev_map
            ),
            term_to_string(
                zk_rule.result_term_idx,
                &self.zk_input.terms,
                &self.axiom_rev_mapping,
                &self.ind_rev_map
            )
        );

        self.add_zk_rule(zk_rule)
    }

    pub fn export_ty(
        &mut self,
        input_idx: usize,
        zk_context: usize,
        context: &mut HashMap<usize, usize>,
        max_binding: usize,
        //expected_idx: usize,
    ) -> Result<usize, String> {
        let input = self.get_zk_term(input_idx).clone();
        //let expected = self.get_zk_term(expected_idx).clone();
        println!(
            "trace ty: {}",
            term_to_string(
                input_idx,
                &self.zk_input.terms,
                &self.axiom_rev_mapping,
                &self.ind_rev_map
            )
        );

        //println!(
        //    "exp ty: {}, PI TERM IS: {}",
        //    max_binding,
        //    term_to_string(input_idx, &self.zk_input.terms, &self.axiom_rev_mapping)
        //);
        let zk_rule = match input.kind {
            // TODO: make sure that we use levels in the circuit, but indicies out here...
            EXPR_VAR => {
                let level = input.name;
                //println!("evaling var... got level {:?}", level);
                //println!("current context {:?}", context);
                // we look up the index in the zk_context...
                if let Some(result_idx) = context.get(&level) {
                    let lifted_rule = self.export_lift(*result_idx, max_binding, usize::MAX);
                    let lifted_idx = self.get_zk_rule(lifted_rule).result_term_idx;

                    //assert!(lifted_idx == expected_idx);
                    //println!(
                    //    "CHECK THIS: {} == {}",
                    //    self.get_zk_rule(lifted_rule).input_term_idx,
                    //    *result_idx
                    //);
                    let ctx_rem =
                        self.zk_input
                            .contexts
                            .remove(zk_context, input.name, *result_idx);
                    println!(
                        "EXPR_VAR TYPING got ctx: {}, remainder: {}",
                        self.zk_input.contexts.to_string(zk_context),
                        self.zk_input.contexts.to_string(ctx_rem)
                    );
                    ExpRule::ty_var(
                        input_idx,
                        lifted_idx,
                        zk_context,
                        max_binding,
                        lifted_rule,
                        ctx_rem,
                    )
                } else {
                    return Err(format!("Unbound var {}", level));
                }
            }
            EXPR_SORT => {
                let zk_result = ExpTerm::sort(input.name + 1);
                let result_idx = self.add_zk_term(zk_result);
                //assert!(result_idx == expected_idx);
                ExpRule::ty_sort(input_idx, result_idx)
            }
            // ============================================================================
            //
            // (C, l) |- f :: (pi x:A.B)  (C, l) |- a :: A   a => a'  (a':C, 0) |- B => B'  (C, 0) |- unlift(B', B'')
            // ---------------------------------------------------------------------------------------
            //                  (C, l) |- (f a) :: B''
            //
            // ============================================================================
            EXPR_APP => {
                //assert!(expected.kind == EXPR_APP);

                let f = input.left;
                let e = input.right;

                //println!(
                //    "zk_context: {:?}",
                //    self.zk_input.contexts.to_string(zk_context)
                //);
                let (f_subs, f_quot) = self.split_zk_context(zk_context, f, context);
                let f_rule = self.export_ty(f, f_subs, context, max_binding)?;
                let f_result = self.get_zk_rule(f_rule).result_term_idx;
                //println!(
                //    "f_result: {} (idx: {})",
                //    term_to_string(f_result, &self.zk_input.terms, &self.axiom_rev_mapping),
                //    self.get_zk_rule(f_rule).result_term_idx
                //);

                let (e_subs, e_quot) = self.split_zk_context(zk_context, e, context);
                println!(
                    "e_subs: {:?}, e_quot: {:?}",
                    self.zk_input.contexts.to_string(e_subs),
                    self.zk_input.contexts.to_string(e_quot)
                );
                let e_rule = self.export_ty(e, e_subs, context, max_binding)?;
                let e_result = self.get_zk_rule(e_rule).result_term_idx;

                //println!(
                //    "e_result: {} (idx: {})",
                //    term_to_string(e_result, &self.zk_input.terms, &self.axiom_rev_mapping),
                //    self.get_zk_rule(e_rule).result_term_idx
                //);

                let f_ty = self.get_zk_term(f_result);
                println!(
                    "input: {}, output: {}",
                    term_to_string(
                        f,
                        &self.zk_input.terms,
                        &self.axiom_rev_mapping,
                        &self.ind_rev_map
                    ),
                    term_to_string(
                        f_result,
                        &self.zk_input.terms,
                        &self.axiom_rev_mapping,
                        &self.ind_rev_map
                    )
                );
                assert!(f_ty.kind == EXPR_PI);
                let name = f_ty.name;
                let domain_ty = f_ty.left;
                let body_ty = f_ty.right;

                // if the types aren't equal...attempt to unify
                let e_rule = if domain_ty != e_result {
                    println!(
                        "I AM HERE: {}, self {}",
                        self.zk_input.contexts.to_string(zk_context),
                        term_to_string(
                            input_idx,
                            &self.zk_input.terms,
                            &self.axiom_rev_mapping,
                            &self.ind_rev_map
                        )
                    );
                    println!(
                        "Trying to unify {} and {} for type checking (raw {:?} and {:?})",
                        term_to_string(
                            e_result,
                            &self.zk_input.terms,
                            &self.axiom_rev_mapping,
                            &self.ind_rev_map
                        ),
                        term_to_string(
                            domain_ty,
                            &self.zk_input.terms,
                            &self.axiom_rev_mapping,
                            &self.ind_rev_map
                        ),
                        self.zk_input.terms[e_result],
                        self.zk_input.terms[domain_ty],
                    );
                    let eval_rule = self.export_unify_helper(
                        e_result,
                        domain_ty,
                        zk_context,
                        context,
                        max_binding,
                    )?;
                    let ty_rule = ExpRule::eval_ty(e, domain_ty, e_subs, 0, e_rule, eval_rule);
                    self.add_zk_rule(ty_rule)
                } else {
                    e_rule
                };

                // TODO: this is wrong...
                let mut eval_context = HashMap::new();
                eval_context.insert(name, e);
                let eval_zk_context = self.zk_context_insert(HashList::EMPTY, name, e);
                //let (body_subs, body_quot) = self.split_zk_context(zk_context, body_ty);
                //println!(
                //    "Exporting body for: {:?} (max_binding: {})",
                //    term_to_string(input_idx, &self.zk_input.terms, &self.axiom_rev_mapping),
                //    max_binding
                //);
                let body_rule =
                    self.export_eval(body_ty, eval_zk_context, &mut eval_context, max_binding + 1);
                let body_result = self.get_zk_rule(body_rule).result_term_idx;

                let unlift_rule = self.export_lift(body_result, max_binding, usize::MAX);
                let unlift_result = self.get_zk_rule(unlift_rule).result_term_idx;

                //assert!(unlift_result == expected_idx);
                //println!(
                //    "Exporting: {} |- {:?} :: {:?} (max_binding: {})",
                //    self.zk_input.contexts.to_string(zk_context),
                //    term_to_string(input_idx, &self.zk_input.terms, &self.axiom_rev_mapping),
                //    term_to_string(unlift_result, &self.zk_input.terms, &self.axiom_rev_mapping),
                //    max_binding
                //);
                // TODO: unlift the result!
                ExpRule::ty_app(
                    input_idx,
                    unlift_result,
                    zk_context,
                    f_rule,
                    f_quot,
                    e_rule,
                    e_quot,
                    body_rule,
                    zk_context,
                    unlift_rule,
                    max_binding,
                )
            }
            EXPR_LAM => {
                //assert!(expected.kind == EXPR_PI);

                let name = input.name;
                let domain = input.left;
                let body = input.right;

                // TODO: domain_qout etc..
                let mut eval_context = HashMap::new();
                //let (domain_subs, domain_quot) = self.split_zk_context(zk_context, domain);
                let domain_rule =
                    self.export_eval(domain, HashList::EMPTY, &mut eval_context, max_binding);
                let domain_result = self.get_zk_rule(domain_rule).result_term_idx;

                context.insert(name, domain_result);
                let new_context = self.zk_context_insert(zk_context, name, domain_result);
                let (body_subs, body_quot) = self.split_zk_context(new_context, body, context);
                let body_rule = self.export_ty(body, body_subs, context, max_binding + 1)?;
                let body_result = self.get_zk_rule(body_rule).result_term_idx;
                context.remove(&name);

                let zk_result = ExpTerm::pi(max_binding, domain_result, body_result);
                let result_idx = self.add_zk_term(zk_result);

                //assert!(result_idx == expected_idx);
                ExpRule::ty_lam(
                    input_idx,
                    result_idx,
                    zk_context,
                    body_rule,
                    body_quot,
                    max_binding,
                )
            }
            EXPR_PI => {
                //assert!(expected.kind == EXPR_PI);

                let name = input.name;
                let domain = input.left;
                let body = input.right;

                let domain_eval_rule =
                    self.export_eval(domain, HashList::EMPTY, &mut HashMap::new(), max_binding);
                let domain_eval_result = self.get_zk_rule(domain_eval_rule).result_term_idx;

                let (domain_subs, domain_quot) =
                    self.split_zk_context(zk_context, domain_eval_result, context);
                let domain_ty_rule = self.export_ty(domain, domain_subs, context, max_binding)?;
                let domain_result = self.get_zk_rule(domain_ty_rule).result_term_idx;

                // TODO: some weirdness with subset here...
                context.insert(name, domain_eval_result);
                let new_context = self.zk_context_insert(zk_context, name, domain_eval_result);
                let (body_subs, body_quot) = self.split_zk_context(new_context, body, context);
                let body_ty_rule = self.export_ty(body, body_subs, context, max_binding + 1)?;
                let body_result = self.get_zk_rule(body_ty_rule).result_term_idx;
                context.remove(&name);

                let domain_ty = self.get_zk_term(domain_result);
                let body_ty = self.get_zk_term(body_result);

                let zk_result = ExpTerm::sort(term::imax(domain_ty.name, body_ty.name));
                let result_idx = self.add_zk_term(zk_result);

                //assert!(result_idx == expected_idx);
                ExpRule::ty_pi(
                    input_idx,
                    result_idx,
                    zk_context,
                    domain_eval_rule,
                    zk_context,
                    domain_ty_rule,
                    domain_quot,
                    body_ty_rule,
                    body_quot,
                    max_binding,
                )
            }
            EXPR_AX => {
                let lift_rule = self.export_lift(input.left, max_binding, usize::MAX);
                let lift_res = self.get_zk_rule(lift_rule).result_term_idx;

                //assert_eq!(
                //    lift_res,
                //    expected_idx,
                //    "Expected {}, Got {}",
                //    term_to_string(lift_res, &self.zk_input.terms, &self.axiom_rev_mapping),
                //    term_to_string(expected_idx, &self.zk_input.terms, &self.axiom_rev_mapping)
                //);
                ExpRule::ty_ax(input_idx, lift_res, max_binding, lift_rule)
            }
            EXPR_IND => {
                let ind = self.get_zk_ind(input.left).clone();
                let lift_rule = self.export_lift(ind.ty, max_binding, usize::MAX);
                let lift_res = self.get_zk_rule(lift_rule).result_term_idx;

                ExpRule::ty_ind(input_idx, lift_res, max_binding, lift_rule)
            }
            EXPR_IND_CTOR => {
                let ind = self.get_zk_ind(input.left).clone();
                let rule_ty = ind.rules[input.right];
                let lift_rule = self.export_lift(rule_ty, max_binding, usize::MAX);
                let lift_res = self.get_zk_rule(lift_rule).result_term_idx;

                ExpRule::ty_ind_ctor(input_idx, lift_res, max_binding, lift_rule)
            }
            EXPR_IND_REC => {
                let zk_ind = self.get_zk_ind(input.left).clone();
                let motive_sort = input.right;

                let ind_name = self.ind_rev_map.get(&input.left).unwrap();
                let ind = self.inductives.get(ind_name).unwrap().clone();

                let num_type_params = ind.num_params;

                let motive_term = ind.generate_motive(input.right);
                let motive_zk_term = self.export_term(motive_term, num_type_params, None);
                let rec_body = zk_ind.rec_body;

                // TODO: check name
                let mut rec_term = ExpTerm::pi(num_type_params, motive_zk_term, rec_body);
                let mut rec_idx = self.add_zk_term(rec_term);

                for (i, ty) in ind.ty.params()[..num_type_params].iter().enumerate().rev() {
                    let ty_idx = self.export_term(ty.clone(), i, None);
                    rec_term = ExpTerm::pi(i, ty_idx, rec_idx);
                    rec_idx = self.add_zk_term(rec_term);
                }

                println!(
                    "-------------- rec term: {}",
                    term_to_string(
                        rec_idx,
                        &self.zk_input.terms,
                        &self.axiom_rev_mapping,
                        &self.ind_rev_map
                    )
                );
                let ind_ty_idx = self.export_term(ind.ty, 0, None);

                let pref_rule =
                    self.export_ind_pref(rec_idx, ind_ty_idx, num_type_params, rec_body)?;

                // create lift rule
                let lift_rule = self.export_lift(rec_idx, max_binding, usize::MAX);
                let lift_res = self.get_zk_rule(lift_rule).result_term_idx;

                // TODO: fix...
                ExpRule::ty_ind_rec(input_idx, lift_res, max_binding, pref_rule, lift_rule)

                // TODO: fix
                /*//ExpRule::ty_ind(input_idx, 0, 0, 0)

                // append type params to the front

                // gross...make better later...

                let motive_term = ind.generate_motive(input.right);
                let motive_zk_term = self.export_term(motive_term, 0, None);
                let rec_body = zk_ind.elim_body;

                for i in ind.num_params {

                }
                let rec_term = ExpTerm::pi(max_binding, motive_zk_term, rec_body);
                let rec_idx = self.add_zk_term(rec_term);

                println!(
                    "rec term: {}",
                    term_to_string(
                        rec_idx,
                        &self.zk_input.terms,
                        &self.axiom_rev_mapping,
                        &self.ind_rev_map
                    )
                );
                // create motive...

                let lift_rule = self.export_lift(rec_idx, max_binding, usize::MAX);
                let lift_res = self.get_zk_rule(lift_rule).result_term_idx;

                ExpRule::ty_ind_rec(input_idx, lift_res, max_binding, lift_rule)*/
            }
            _ => {
                unimplemented!()
            }
        };

        Ok(self.add_zk_rule(zk_rule))
    }

    pub fn export_lift(
        &mut self,
        input_idx: usize,
        max_binding: usize,
        min_binding_seen: usize,
    ) -> usize {
        let input = self.get_zk_term(input_idx).clone();

        let zk_rule = match input.kind {
            EXPR_VAR => {
                if input.name >= min_binding_seen {
                    let result = ExpTerm::bound(input.name + max_binding - min_binding_seen);
                    let result_idx = self.add_zk_term(result);
                    ExpRule::lift(input_idx, result_idx, max_binding, min_binding_seen, 0, 0)
                } else {
                    ExpRule::lift(input_idx, input_idx, max_binding, min_binding_seen, 0, 0)
                }
            }
            EXPR_SORT => ExpRule::lift(input_idx, input_idx, max_binding, min_binding_seen, 0, 0),
            EXPR_LAM => {
                let new_min_binding = min(input.name, min_binding_seen);

                let body_idx = self.export_lift(input.right, max_binding, new_min_binding);
                let body_result = self.get_zk_rule(body_idx).result_term_idx;

                // TODO: remove this later
                let domain_idx = self.export_lift(input.left, max_binding, new_min_binding);
                let domain_result = self.get_zk_rule(domain_idx).result_term_idx;

                let result = ExpTerm::lam(
                    input.name + max_binding - new_min_binding,
                    domain_result,
                    body_result,
                );
                let result_idx = self.add_zk_term(result);

                ExpRule::lift(
                    input_idx,
                    result_idx,
                    max_binding,
                    min_binding_seen,
                    body_idx,
                    0,
                )
            }
            EXPR_PI => {
                let new_min_binding = min(input.name, min_binding_seen);

                let domain_idx = self.export_lift(input.left, max_binding, min_binding_seen);
                let domain_result = self.get_zk_rule(domain_idx).result_term_idx;

                let body_idx = self.export_lift(input.right, max_binding, new_min_binding);
                let body_result = self.get_zk_rule(body_idx).result_term_idx;

                // Domain doesn't matter ... we don't use it in real proofs
                let result = ExpTerm::pi(
                    input.name + max_binding - new_min_binding,
                    domain_result,
                    body_result,
                );
                let result_idx = self.add_zk_term(result);

                ExpRule::lift(
                    input_idx,
                    result_idx,
                    max_binding,
                    min_binding_seen,
                    body_idx,
                    domain_idx,
                )
            }
            EXPR_APP => {
                let f_idx = self.export_lift(input.left, max_binding, min_binding_seen);
                let f_result = self.get_zk_rule(f_idx).result_term_idx;
                let f_term = self.get_zk_term(f_result).clone();

                let e_idx = self.export_lift(input.right, max_binding, min_binding_seen);
                let e_result = self.get_zk_rule(e_idx).result_term_idx;

                let result = ExpTerm::app(f_result, e_result, f_term.top_level_func);
                let result_idx = self.add_zk_term(result);

                ExpRule::lift(
                    input_idx,
                    result_idx,
                    max_binding,
                    min_binding_seen,
                    e_idx,
                    f_idx,
                )
            }
            EXPR_AX => ExpRule::lift(input_idx, input_idx, max_binding, min_binding_seen, 0, 0),
            EXPR_IND => ExpRule::lift(input_idx, input_idx, max_binding, min_binding_seen, 0, 0),
            EXPR_IND_CTOR => {
                ExpRule::lift(input_idx, input_idx, max_binding, min_binding_seen, 0, 0)
            }
            EXPR_IND_REC => {
                ExpRule::lift(input_idx, input_idx, max_binding, min_binding_seen, 0, 0)
            }
            _ => panic!("Unknown expr kind!"),
        };

        println!(
            "trace lift (max binding: {}): {} => {}",
            max_binding,
            term_to_string(
                input_idx,
                &self.zk_input.terms,
                &self.axiom_rev_mapping,
                &self.ind_rev_map
            ),
            term_to_string(
                zk_rule.result_term_idx,
                &self.zk_input.terms,
                &self.axiom_rev_mapping,
                &self.ind_rev_map
            )
        );

        self.add_zk_rule(zk_rule)
    }

    //pub fn export_proof_irrel(
    //    &mut self,
    //    input_idx: usize,
    //    expected_idx: usize,
    //    zk_context: usize,
    //    context: &mut HashMap<usize, usize>,
    //    max_binding: usize,
    //) -> Option<usize> {
    //    let input = self.get_zk_term(input_idx).clone();
    //    let expected = self.get_zk_term(expected_idx).clone();

    //    if input_idx == expected_idx {
    //        return None;
    //    }

    //    let inp_ty_rule = self.export_ty(input_idx, zk_context, context, max_binding);
    //    let inp_ty = self.get_zk_rule(inp_ty_rule).result_term_idx;
    //    let exp_ty_rule = self.export_ty(expected_idx, zk_context, context, max_binding);
    //    let exp_ty = self.get_zk_rule(exp_ty_rule).result_term_idx;
    //    let ty_ty_rule = self.export_ty(inp_ty, zk_context, context, max_binding);
    //    let ty_ty = self.get_zk_rule(ty_ty_rule).result_term_idx;
    //    let ty_ty_term = self.get_zk_term(ty_ty);

    //    assert!(inp_ty == exp_ty);
    //    assert!(ty_ty_term.kind == EXPR_SORT && ty_ty_term.name == 0);

    //    let rule = ExpRule::proof_irrel(
    //        input_idx,
    //        expected_idx,
    //        zk_context,
    //        max_binding,
    //        inp_ty_rule,
    //        exp_ty_rule,
    //        ty_ty_rule,
    //    );
    //    let rule_idx = self.add_zk_rule(rule);

    //    Some(rule_idx)
    //}

    pub fn add_zk_term(&mut self, zk_term: ExpTerm) -> usize {
        if let Some(index) = self.zk_term_cache.get(&zk_term) {
            return *index;
        }

        let mut free_bindings = HashSet::new();
        match zk_term.kind {
            EXPR_VAR => {
                free_bindings.insert(zk_term.name);
            }
            EXPR_LAM => {
                free_bindings = self
                    .zk_term_free_bindings
                    .get(&zk_term.right)
                    .unwrap()
                    .clone();
                free_bindings = free_bindings
                    .union(self.zk_term_free_bindings.get(&zk_term.left).unwrap())
                    .cloned()
                    .collect();
                free_bindings.remove(&zk_term.name);
            }
            EXPR_PI => {
                free_bindings = self
                    .zk_term_free_bindings
                    .get(&zk_term.right)
                    .unwrap()
                    .clone();
                free_bindings = free_bindings
                    .union(self.zk_term_free_bindings.get(&zk_term.left).unwrap())
                    .cloned()
                    .collect();
                free_bindings.remove(&zk_term.name);
            }
            EXPR_APP => {
                free_bindings = self
                    .zk_term_free_bindings
                    .get(&zk_term.right)
                    .unwrap()
                    .clone();
                free_bindings = free_bindings
                    .union(self.zk_term_free_bindings.get(&zk_term.left).unwrap())
                    .cloned()
                    .collect();
            }
            _ => {}
        }

        let mut zk_term = zk_term;
        let index = self.zk_input.terms.len();

        // dont include top level func for caching...
        self.zk_term_cache.insert(zk_term.clone(), index);

        // fixup top_level_func for non app terms.
        if zk_term.kind != EXPR_APP {
            zk_term.top_level_func = index;
        }

        // push the new zk term and return index
        self.zk_input.terms.push(zk_term.clone());

        self.zk_term_free_bindings.insert(index, free_bindings);
        index
    }

    fn add_zk_rule(&mut self, zk_rule: ExpRule) -> usize {
        if let Some(index) = self.zk_rule_cache.get(&zk_rule) {
            return *index;
        }

        // push the new zk term and return index
        self.zk_input.rules.push(zk_rule.clone());
        let index = self.zk_input.rules.len() - 1;
        self.zk_rule_cache.insert(zk_rule.clone(), index);
        index
    }

    fn add_zk_ind(&mut self, zk_ind: ExpInd) -> usize {
        self.zk_input.inductives.push(zk_ind.clone());
        let index = self.zk_input.inductives.len() - 1;
        index
    }

    fn get_zk_ind(&mut self, index: usize) -> &ExpInd {
        &self.zk_input.inductives[index]
    }

    fn get_zk_ind_mut(&mut self, index: usize) -> &mut ExpInd {
        &mut self.zk_input.inductives[index]
    }

    fn get_zk_term(&self, index: usize) -> &ExpTerm {
        &self.zk_input.terms[index]
    }

    fn get_zk_rule(&self, index: usize) -> &ExpRule {
        &self.zk_input.rules[index]
    }

    fn zk_context_insert(&mut self, zk_context: usize, key: usize, value: usize) -> usize {
        self.zk_input.contexts.add(zk_context, key, value)
    }

    fn split_zk_context(
        &mut self,
        zk_context: usize,
        term: usize,
        context: &mut HashMap<usize, usize>,
    ) -> (usize, usize) {
        let mut subset = self.zk_term_free_bindings.get(&term).unwrap().clone();
        for bound in subset.clone() {
            if let Some(val) = context.get(&bound) {
                let pointers = self.zk_term_free_bindings.get(&val).unwrap();
                subset = subset.union(pointers).cloned().collect();
            }
        }

        //println!(
        //    "free bindings for {:?}: {:?}",
        //    term_to_string(term, &self.zk_input.terms, &self.axiom_rev_mapping),
        //    self.zk_term_free_bindings.get(&term).unwrap().clone(),
        //);
        self.zk_input.contexts.split(zk_context, subset)
    }

    pub fn export_term(
        &mut self,
        term: Term,
        num_bindings: usize,
        axioms: Option<&HashMap<String, Term>>,
    ) -> usize {
        if let Some(index) = self.term_cache.get(&(term.clone(), num_bindings)) {
            return *index;
        }

        let zk_term = match &*term {
            // convert debruijn index to debruijn level...
            // TODO: need more sophisticated names...todo
            TermData::Bound(index) => {
                let db_level = num_bindings - *index - 1;
                ExpTerm::bound(db_level)
            }
            TermData::Sort(level) => ExpTerm::sort(*level),
            TermData::Binding(BindingData { ty, domain, body }) => {
                let body_idx = self.export_term(body.clone(), num_bindings + 1, axioms);
                let domain_idx = self.export_term(domain.clone(), num_bindings, axioms);
                match ty {
                    // TODO: names
                    BindingType::Lam => ExpTerm::lam(num_bindings, domain_idx, body_idx),
                    BindingType::Pi => ExpTerm::pi(num_bindings, domain_idx, body_idx),
                }
            }
            TermData::App(f, e) => {
                let f_idx = self.export_term(f.clone(), num_bindings, axioms);
                let f_term = self.get_zk_term(f_idx).clone();
                let e_idx = self.export_term(e.clone(), num_bindings, axioms);

                ExpTerm::app(f_idx, e_idx, f_term.top_level_func)
            }
            TermData::Axiom(name) => {
                // TODO: inductives and inductive rules....
                if let Some((ax, tag)) = self.axiom_mapping.get(name) {
                    ExpTerm::ax(*ax, *tag)
                } else {
                    if let Some(axioms_map) = axioms {
                        let term = axioms_map
                            .get(name)
                            .expect(&format!("Couldn't find axiom named: {}", name));
                        self.add_axiom_term(name.to_string(), term.clone(), axioms_map);
                        //let zk_term = self.export_term(term.clone(), 0, axioms);
                        let (ax, tag) = *self.axiom_mapping.get(name).unwrap();
                        ExpTerm::ax(ax, tag)
                    } else {
                        panic!("Couldn't fine axioms named: {}", name);
                    }
                }
            }
            TermData::Ind(name) => {
                let ind_idx = self.get_or_export_ind(name);
                ExpTerm::ind(ind_idx)
            }
            TermData::IndCtor(ind_name, ctor_name) => {
                let ind_idx = self.get_or_export_ind(ind_name);
                if let Some(ctor_idx) = self
                    .inductive_rule_mapping
                    .get(&(ind_name.to_string(), ctor_name.to_string()))
                {
                    ExpTerm::ind_ctor(ind_idx, *ctor_idx)
                } else {
                    println!("ind mapping: {:?}", self.inductive_rule_mapping);
                    panic!(
                        "Couldn't find ctor {} for inductive {}",
                        ctor_name, ind_name
                    );
                }
            }
            TermData::IndRec(ind_name, motive_sort) => {
                let ind_idx = self.get_or_export_ind(ind_name);
                ExpTerm::ind_rec(ind_idx, *motive_sort)
            }
            _ => {
                unimplemented!()
            }
        };

        self.add_zk_term(zk_term)
    }

    pub fn get_or_export_ind(&mut self, name: &str) -> usize {
        if let Some(ind_idx) = self.inductive_mapping.get(name) {
            return *ind_idx;
        } else {
            // TODO: remove useless clone
            let ind = self
                .inductives
                .get(name)
                .expect(&format!(
                    "Couldn't find ind named {}\n Got: {:?}",
                    name, self.inductives
                ))
                .clone();
            self.add_inductive(&ind);
            *self.inductive_mapping.get(name).unwrap()
        }
    }

    //// TODO: definintional equality
    //// TODO: prop proof irrelevance
    ////
    //pub fn export_eval(
    //    &mut self,
    //    input: Term,
    //    zk_context: usize,
    //    context: &mut Context,
    //    name_mapping: &mut Vec<usize>,
    //) -> (usize, Term) {
    //    // if we have a rule from the same input term and same context, then just use the cached version
    //    //if let Some((rule, res)) = self.eval_cache.get(&(input.clone(), zk_context)) {
    //    //    return (*rule, res.clone());
    //    //}

    //    let input_idx = self.export_term(input.clone(), name_mapping);

    //    let (rule, res) = match &*input {
    //        // lookup the name of the index
    //        //TermData::Bound(index) => {
    //        //    if let Some(bound_term) = context.get_bound(*index) {
    //        //        //let res = crate::term::lift(bound_term, *index as isize + 1);
    //        //        let result_idx = self.export_term(bound_term.clone(), name_mapping);
    //        //        (
    //        //            ExpRule::eval_var(input_idx, result_idx, zk_context),
    //        //            term::lift(bound_term, *index as isize + 1),
    //        //        )
    //        //    } else {
    //        //        (ExpRule::eval_id(input_idx), input.clone())
    //        //    }
    //        //}
    //        TermData::Sort(level) => (ExpRule::eval_id(input_idx), input.clone()),
    //        // ============================================================================
    //        //      C |- e => v
    //        // ---------------------------------
    //        //  C |- \x -> e => \x -> v
    //        // ============================================================================
    //        TermData::Binding(BindingData {
    //            ty: BindingType::Lam,
    //            domain,
    //            body,
    //        }) => {
    //            let (parent0, body_value) =
    //                self.export_eval(body.clone(), zk_context, context, name_mapping);
    //            let body_idx = self.export_term(body.clone(), name_mapping);
    //            //let body_value_idx = self.export_term(body_value);
    //            let result = term::lam(domain.clone(), body_value);
    //            let result_idx = self.export_term(result.clone(), name_mapping);

    //            (
    //                ExpRule::eval_lam(input_idx, result_idx, zk_context, parent0),
    //                result,
    //            )
    //        }
    //        //// ============================================================================
    //        ////  p => t           p' => t'
    //        //// ---------------------------------
    //        ////  pi x: p -> p' => pi x: t -> t'
    //        ////
    //        //// ============================================================================
    //        //TermData::Binding(BindingData {
    //        //    ty: BindingType::Pi,
    //        //    domain,
    //        //    body,
    //        //}) => {
    //        //    // TODO: Okay to not add to context because it isn't bound?
    //        //    let (parent0, domain_value) =
    //        //        self.export_eval(domain.clone(), zk_context, context, name_mapping);
    //        //    let (parent1, body_value) =
    //        //        self.export_eval(body.clone(), zk_context, context, name_mapping);

    //        //    let result = term::pi(domain_value.clone(), body_value.clone());
    //        //    let result_idx = self.export_term(result.clone(), name_mapping);

    //        //    (
    //        //        ExpRule::eval_pi(input_idx, result_idx, zk_context, parent0, parent1),
    //        //        result,
    //        //    )
    //        //}
    //        //// ============================================================================
    //        //// e => n   e' => v'
    //        //// ---------------------------------
    //        ////  e e' => n v'
    //        //// ============================================================================
    //        //TermData::App(f, e) => {
    //        //    let (parent0, f_value) =
    //        //        self.export_eval(f.clone(), zk_context, context, name_mapping);
    //        //    let (parent1, e_value) =
    //        //        self.export_eval(e.clone(), zk_context, context, name_mapping);
    //        //    let e_value_idx = self.export_term(e_value.clone(), name_mapping);

    //        //    match &*f_value {
    //        //        // TODO: reduce to two parents
    //        //        // C: f => \ -> e   e => e'  e:C, v => v'
    //        //        // ---------------------------------------------
    //        //        //                C: f e => vp
    //        //        TermData::Binding(BindingData {
    //        //            ty: BindingType::Lam,
    //        //            domain: _,
    //        //            body,
    //        //        }) => {
    //        //            context.push(e_value.clone());

    //        //            //let name = self.fresh_name();
    //        //            //println!("fresh name is: {}", name);
    //        //            //name_mapping.push(name);
    //        //            //
    //        //            // TODO: Lambdas now need to keep track of the names that they use, as well
    //        //            //       as the number of
    //        //            let new_zk_context = self.contexts.add(zk_context, name, e_value_idx);
    //        //            assert_ne!(new_zk_context, zk_context);

    //        //            let (parent2, v_value) =
    //        //                self.export_eval(body.clone(), new_zk_context, context, name_mapping);
    //        //            let v_value_idx = self.export_term(v_value.clone(), name_mapping);
    //        //            context.pop();
    //        //            name_mapping.pop();

    //        //            (
    //        //                ExpRule::eval_app_lam(
    //        //                    input_idx,
    //        //                    v_value_idx,
    //        //                    zk_context,
    //        //                    parent0,
    //        //                    parent1,
    //        //                    parent2,
    //        //                ),
    //        //                term::lift(v_value, -1),
    //        //            )
    //        //        }
    //        //        _ => {
    //        //            let res = term::app(f_value, e_value);
    //        //            let res_idx = self.export_term(res.clone(), name_mapping);

    //        //            (
    //        //                ExpRule::eval_app(input_idx, res_idx, zk_context, parent0, parent1),
    //        //                res,
    //        //            )
    //        //        }
    //        //    }
    //        //}
    //        _ => {
    //            unimplemented!()
    //        }
    //    };

    //    let out_idx = self.rules.len();
    //    self.rules.push(rule);
    //    //self.term_mapping.insert(term, out_idx);
    //    (out_idx, res)
    //}

    // TODO: maybe a better way to do names is to see how common each term is, then do names based
    // on that...
    //pub fn export_term(&mut self, term: Term, names: &mut Vec<usize>) -> usize {
    //    if let Some(idx) = self.term_mapping.get(&term) {
    //        println!(
    //            "cached {:?} as {:?} (which is {:?})",
    //            term, idx, self.terms[*idx]
    //        );
    //        return *idx;
    //    }

    //    let exp_term = match &*term {
    //        // TODO...
    //        //TermData::Bound(index) => {
    //        //    let name = names[*index];
    //        //    println!("name is: {}", name);
    //        //    ExpTerm::new(EXPR_VAR, name, 0)
    //        //}
    //        TermData::Sort(level) => ExpTerm::new(EXPR_SORT, 0, *level, 0),
    //        TermData::Binding(BindingData { ty, domain, body }) => {
    //            // TODO: better compression using name mapping
    //            let name = self.fresh_name();
    //            names.push(name);
    //            let domain_idx = self.export_term(domain.clone(), names);
    //            let body_idx = self.export_term(body.clone(), names);

    //            let term_kind = match ty {
    //                BindingType::Lam => EXPR_LAM,
    //                BindingType::Pi => EXPR_PI,
    //            };

    //            let res = ExpTerm::new(term_kind, 0, domain_idx, body_idx);
    //            names.pop();
    //            res
    //        }
    //        TermData::App(f, e) => {
    //            let f_idx = self.export_term(f.clone(), names);
    //            let e_idx = self.export_term(e.clone(), names);

    //            ExpTerm::new(EXPR_APP, 0, f_idx, e_idx)
    //        }
    //        TermData::Axiom(name) => {
    //            unimplemented!()
    //        }
    //        _ => {
    //            unimplemented!()
    //        }
    //    };

    //    let out_idx = self.terms.len();
    //    self.terms.push(exp_term);
    //    self.term_mapping.insert(term, out_idx);
    //    out_idx
    //}
}

pub fn term_to_string(
    term_idx: usize,
    terms: &[ExpTerm],
    axioms_rev_map: &HashMap<(usize, usize), String>,
    ind_rev_map: &HashMap<usize, String>,
) -> String {
    let term = &terms[term_idx];
    match term.kind {
        EXPR_VAR => format!("Bound({})", term.name),
        EXPR_SORT => format!("Sort({})", term.name),
        EXPR_LAM => {
            let domain = term_to_string(term.left, terms, axioms_rev_map, ind_rev_map);
            let body = term_to_string(term.right, terms, axioms_rev_map, ind_rev_map);
            format!("Lam({} : {}, {})", term.name, domain, body)
        }
        EXPR_PI => {
            let domain = term_to_string(term.left, terms, axioms_rev_map, ind_rev_map);
            let body = term_to_string(term.right, terms, axioms_rev_map, ind_rev_map);
            format!("Π ({} : {}, {})", term.name, domain, body)
        }
        EXPR_APP => {
            let f = term_to_string(term.left, terms, axioms_rev_map, ind_rev_map);
            let e = term_to_string(term.right, terms, axioms_rev_map, ind_rev_map);
            format!("App({}, {})", f, e)
        }
        EXPR_AX => format!(
            "Axiom({})",
            (axioms_rev_map.get(&(term.left, term.right)).unwrap())
        ),
        EXPR_IND => format!("Ind({})", ind_rev_map.get(&term.left).unwrap()),
        EXPR_IND_CTOR => format!(
            "IndCtor({}.{})",
            ind_rev_map.get(&term.left).unwrap(),
            term.right
        ),
        EXPR_IND_REC => format!(
            "IndRec({}, {})",
            ind_rev_map.get(&term.left).unwrap(),
            term.right
        ),
        _ => unimplemented!(),
    }
}

pub fn to_term(
    term_idx: usize,
    terms: &[ExpTerm],
    axioms_rev_map: &HashMap<(usize, usize), String>,
) -> Term {
    let term = &terms[term_idx];
    match term.kind {
        EXPR_VAR => term::bound(term.name),
        EXPR_SORT => term::sort(term.name),
        EXPR_LAM => {
            let body = to_term(term.right, terms, axioms_rev_map);
            term::lam(term::sort(0), body)
        }
        EXPR_PI => {
            let domain = to_term(term.left, terms, axioms_rev_map);
            let body = to_term(term.right, terms, axioms_rev_map);
            term::pi(domain, body)
        }
        EXPR_APP => {
            let f = to_term(term.left, terms, axioms_rev_map);
            let e = to_term(term.right, terms, axioms_rev_map);
            term::app(f, e)
        }
        EXPR_AX => term::axiom(axioms_rev_map.get(&(term.left, term.right)).unwrap()),
        _ => unimplemented!(),
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::term::*;
    use sim::simulate;

    fn run_eval_test(input: Term, output: Term) {
        let mut exp = Exporter::new();
        let rule = exp.export_eval_term(input);
        //assert_eq!(res, output);

        simulate(exp.zk_input.clone(), true, &exp.axiom_rev_mapping);

        let res = exp.export_term(output, 0, None);
        let actual_res = exp.get_zk_rule(rule).result_term_idx;
        println!(
            "GOT TERM: {:?}",
            to_term(actual_res, &exp.zk_input.terms, &exp.axiom_rev_mapping)
        );
        assert_eq!(res, actual_res);
    }

    fn run_fail_eval_test(input: Term, output: Term) {
        let mut exp = Exporter::new();
        let rule = exp.export_eval_term(input);

        let wrong_output_idx = exp.export_term(output, 0, None);
        exp.zk_input.rules[rule].result_term_idx = wrong_output_idx;

        simulate(exp.zk_input, true, &exp.axiom_rev_mapping);
    }

    #[test]
    fn eval_sort() {
        run_eval_test(sort(0), sort(0));
    }

    #[test]
    #[should_panic]
    fn eval_sort_fail() {
        run_eval_test(sort(0), sort(1));
    }

    #[test]
    fn eval_lam() {
        let input = lam(sort(0), sort(0));
        run_eval_test(input.clone(), input);
    }

    #[test]
    #[should_panic]
    fn eval_lam_fail() {
        run_fail_eval_test(lam(sort(0), sort(0)), lam(sort(0), sort(1)));
    }

    #[test]
    fn eval_pi() {
        let input = pi(sort(0), sort(0));
        run_eval_test(input.clone(), input);
    }

    #[test]
    fn eval_nested() {
        let input = pi(sort(0), app(lam(sort(2), bound(0)), sort(1)));
        let res = pi(sort(0), sort(1));
        run_eval_test(input.clone(), res);
    }

    #[test]
    fn eval_nested_lam() {
        let input = lam(
            sort(0),
            app(lam(pi(sort(0), sort(0)), bound(0)), lam(sort(0), bound(0))),
        );
        let res = lam(sort(0), lam(sort(0), bound(0)));
        run_eval_test(input.clone(), res);
    }

    #[test]
    fn successive_apps() {
        let input = app(
            app(lam(pi(sort(0), sort(0)), bound(0)), lam(sort(0), bound(0))),
            sort(1),
        );
        let res = sort(1);
        run_eval_test(input, res);
    }

    #[test]
    #[should_panic]
    fn eval_lam_nonlam_fail() {
        run_fail_eval_test(lam(sort(0), sort(0)), sort(0));
    }

    #[test]
    fn eval_app() {
        let input = app(sort(0), sort(1));
        run_eval_test(input.clone(), input);
    }

    #[test]
    #[should_panic(expected = "assertion failed: result_term.kind == EXPR_APP")]
    fn eval_app_fail() {
        run_fail_eval_test(app(sort(0), sort(1)), sort(0));
    }

    #[test]
    fn eval_app_lam() {
        run_eval_test(app(lam(sort(1), sort(2)), sort(0)), sort(2));
    }

    #[test]
    #[should_panic(expected = "assertion failed: parent3.result_term_idx == node.result_term_idx")]
    fn eval_app_lam_fail() {
        run_fail_eval_test(app(lam(sort(1), sort(2)), sort(0)), sort(1));
    }

    #[test]
    fn eval_app_lam_bound() {
        run_eval_test(app(lam(sort(1), bound(0)), sort(0)), sort(0));
    }

    #[test]
    fn eval_app_lam_bound_subsets() {
        // TODO: cannot actually run this because we don't do lifting/unlifting and our names are
        // wrong LOL
        //run_eval_test(
        //    app(lam(sort(1), lam(sort(1), bound(0))), sort(0)),
        //    lam(sort(1), bound(1)),
        //);
    }

    #[test]
    fn eval_app_renaming() {
        // TODO: fix
        //    run_eval_test(
        //        app(
        //            lam(pi(sort(0), sort(0)), app(bound(0), bound(0))),
        //            lam(pi(sort(0), sort(0)), bound(0)),
        //        ),
        //        lam(sort(0), bound(0)),
        //    );
    }

    // TODO:
    //#[test]
    //fn eval_app_lam_bound_fail() {
    //    let mut exp = Exporter::new();
    //    let (rule, res) = exp.export_eval(
    //        app(lam(sort(2), bound(0)), sort(1)),
    //        HashList::EMPTY,
    //        &mut Context::new(),
    //        &mut Vec::new(),
    //    );

    //    // craft fake proof
    //    let wrong_output_idx = exp.export_term(sort(0), &mut Vec::new());
    //    exp.rules[rule].result_term_idx = wrong_output_idx;

    //    let parent2 = exp.rules[rule].parent2;
    //    exp.rules[parent2].result_term_idx = wrong_output_idx;

    //    let zk_input = exp.to_zk_input();
    //    simulate(zk_input);
    //}
    //
    //#[test]
    //fn eval_bound() {
    //    let mut exp = Exporter::new();
    //    let s0 = exp.export_term(sort(0), &mut Vec::new());
    //    let zk_context = exp.contexts.add(HashList::EMPTY, 0, s0);
    //    let mut context = Context::new();
    //    context.push(sort(0));
    //    println!("ctx: {:?}", exp.contexts.nodes[0]);
    //    let (rule, res) = exp.export_eval(bound(0), zk_context, &mut context, &mut vec![0]);
    //    println!("rule: {:?} {:?}", exp.rules[rule], res);
    //    simulate(exp.to_zk_input());
    //}

    //#[test]
    //#[should_panic(
    //    expected = "assertion failed: contexts.contains(node.ctx_idx, input_term.left, node.result_term_idx)"
    //)]
    //fn fail_eval_bound() {
    //    let mut exp = Exporter::new();
    //    let s0 = exp.export_term(sort(0), &mut Vec::new());
    //    let zk_context = exp.contexts.add(HashList::EMPTY, 0, s0);
    //    let mut context = Context::new();
    //    context.push(sort(1));
    //    let (rule, res) = exp.export_eval(bound(0), zk_context, &mut context, &mut vec![0]);
    //    println!("rule: {:?} {:?}", exp.rules[rule], res);
    //    simulate(exp.to_zk_input());
    //}

    //#[test]
    //fn eval_app_lam_
    //
    fn run_ty_test(input: Term, output: Term) {
        let mut exp = Exporter::new();
        let rule = exp.export_ty_term(input).unwrap();
        //assert_eq!(res, output);

        simulate(exp.zk_input.clone(), true, &exp.axiom_rev_mapping);

        let res = exp.export_term(output, 0, None);
        let actual_res = exp.get_zk_rule(rule).result_term_idx;
        println!(
            "GOT TERM: {:?}",
            to_term(actual_res, &exp.zk_input.terms, &exp.axiom_rev_mapping)
        );
        assert_eq!(res, actual_res);
    }

    #[test]
    fn type_sort() {
        run_ty_test(sort(0), sort(1));
    }

    #[test]
    fn type_lam() {
        run_ty_test(lam(sort(0), sort(0)), pi(sort(0), sort(1)));
    }

    #[test]
    fn type_lam_bound() {
        run_ty_test(lam(sort(0), bound(0)), pi(sort(0), sort(0)));
    }

    #[test]
    fn type_pi() {
        run_ty_test(pi(sort(0), sort(0)), sort(1));
    }

    #[test]
    fn type_app() {
        run_ty_test(app(lam(sort(1), bound(0)), sort(0)), sort(1))
    }

    fn run_ty_axioms(input: Term, output: Term, axioms: HashMap<String, Term>) {
        //let mut exp = Exporter::with_axioms(axioms);
        //let rule = exp.export_ty_term(input);
        ////assert_eq!(res, output);

        //// TODO: wtf
        //println!(
        //    "input: {:?}",
        //    to_term(
        //        exp.get_zk_rule(rule).input_term_idx,
        //        &exp.zk_input.terms,
        //        &exp.axiom_rev_mapping
        //    )
        //);
        //simulate(exp.zk_input.clone(), &exp.axiom_rev_mapping);

        //let res = exp.export_term(output, 0, None);
        //let actual_res = exp.get_zk_rule(rule).result_term_idx;
        //println!(
        //    "GOT TERM: {:?}",
        //    to_term(actual_res, &exp.zk_input.terms, &exp.axiom_rev_mapping)
        //);
        //assert_eq!(res, actual_res);
    }

    #[test]
    fn type_sort_axioms() {
        let mut axioms = HashMap::new();
        axioms.insert("and".to_owned(), pi(sort(0), pi(sort(0), sort(0))));
        run_ty_axioms(axiom("and"), pi(sort(0), pi(sort(0), sort(0))), axioms);
    }

    #[test]
    fn type_props() {
        let axioms: HashMap<String, Term> = HashMap::from([
            ("p", sort(0)),
            ("q", sort(0)),
            ("or", pi(sort(0), pi(sort(0), sort(0)))),
            (
                "or.inr",
                pi(
                    sort(0),
                    pi(
                        sort(0),
                        pi(bound(0), app(app(axiom("or"), bound(2)), bound(1))),
                    ),
                ),
            ),
        ])
        .iter()
        .map(|(k, v)| (k.to_string(), v.clone()))
        .collect();

        println!("axioms: {:?}", axioms);

        //run_ty_axioms(
        //    axiom("or"),
        //    pi(sort(0), pi(sort(0), sort(0))),
        //    axioms.clone(),
        //);
        ////run_ty_axioms(axiom("or.inr"), sort(0), axioms);
        //run_ty_axioms(app(axiom("or.inr"), axiom("p")), sort(0), axioms);
    }

    #[test]
    fn type_naming() {
        let axioms: HashMap<String, Term> = HashMap::from([
            ("p", sort(0)),
            ("q", sort(0)),
            ("or", pi(sort(0), pi(sort(0), sort(0)))),
            (
                "or.inr",
                pi(
                    sort(0),
                    pi(
                        sort(0),
                        pi(bound(0), app(app(axiom("or"), bound(2)), bound(1))),
                    ),
                ),
            ),
        ])
        .iter()
        .map(|(k, v)| (k.to_string(), v.clone()))
        .collect();

        run_ty_axioms(
            lam(
                sort(0),
                lam(sort(0), app(app(axiom("or.inr"), bound(0)), bound(1))),
            ),
            sort(0),
            axioms,
        );
    }

    #[test]
    fn ty_ax_lift() {
        //let axioms: HashMap<String, Term> = HashMap::from([(
        //    "or.inr",
        //    pi(
        //        sort(0),
        //        pi(sort(0), pi(bound(0), app(app(sort(0), bound(2)), bound(1)))),
        //    ),
        //)])
        //.iter()
        //.map(|(k, v)| (k.to_string(), v.clone()))
        //.collect();

        //let mut exp = Exporter::with_axioms(axioms.clone());

        //let term = axiom("or.inr");
        //let zk_term = exp.export_term(term, 0, None);
        //let res = exp.export_ty(zk_term, HashList::EMPTY, &mut HashMap::new(), 0);
        //let rule = exp.get_zk_rule(res);

        //assert_eq!("Π (0 : Sort(0), Π (1 : Sort(0), Π (2 : Bound(1), App(App(Sort(0), Bound(0)), Bound(1)))))",
        //    term_to_string(
        //        rule.result_term_idx,
        //        &exp.zk_input.terms,
        //        &exp.axiom_rev_mapping
        //    ));

        //let res = exp.export_ty(zk_term, HashList::EMPTY, &mut HashMap::new(), 3);
        //let rule = exp.get_zk_rule(res);

        //assert_eq!("Π (3 : Sort(0), Π (4 : Sort(0), Π (5 : Bound(4), App(App(Sort(0), Bound(3)), Bound(4)))))",
        //    term_to_string(
        //        rule.result_term_idx,
        //        &exp.zk_input.terms,
        //        &exp.axiom_rev_mapping
        //    ));

        //simulate(exp.zk_input, &exp.axiom_rev_mapping);
    }

    fn ty_ax_more() {
        // todo
    }

    #[test]
    fn basic_lift() {
        let mut exp = Exporter::new();
        let term = pi(sort(0), pi(sort(0), bound(0)));
        let zk_term = exp.export_term(term, 3, None);

        assert_eq!(
            "Π (3 : Sort(0), Π (4 : Sort(0), Bound(4)))",
            term_to_string(zk_term, &exp.zk_input.terms, &HashMap::new())
        );

        let lift_rule = exp.export_lift(zk_term, 5, usize::MAX);
        let lift_res = exp.get_zk_rule(lift_rule).result_term_idx;
        assert_eq!(
            "Π (5 : Sort(0), Π (6 : Sort(0), Bound(6)))",
            term_to_string(lift_res, &exp.zk_input.terms, &HashMap::new())
        );

        let unlift_rule = exp.export_lift(zk_term, 1, usize::MAX);
        let unlift_res = exp.get_zk_rule(unlift_rule).result_term_idx;
        assert_eq!(
            "Π (1 : Sort(0), Π (2 : Sort(0), Bound(2)))",
            term_to_string(unlift_res, &exp.zk_input.terms, &HashMap::new())
        );

        simulate(exp.zk_input, true, &HashMap::new());
    }

    #[test]
    fn free_lift() {
        let mut exp = Exporter::new();
        let term = pi(sort(0), pi(sort(0), bound(4)));
        let zk_term = exp.export_term(term, 3, None);

        assert_eq!(
            "Π (3 : Sort(0), Π (4 : Sort(0), Bound(0)))",
            term_to_string(zk_term, &exp.zk_input.terms, &HashMap::new())
        );

        let lift_rule = exp.export_lift(zk_term, 5, usize::MAX);
        let lift_res = exp.get_zk_rule(lift_rule).result_term_idx;
        assert_eq!(
            "Π (5 : Sort(0), Π (6 : Sort(0), Bound(0)))",
            term_to_string(lift_res, &exp.zk_input.terms, &HashMap::new())
        );

        let unlift_rule = exp.export_lift(zk_term, 1, usize::MAX);
        let unlift_res = exp.get_zk_rule(unlift_rule).result_term_idx;
        assert_eq!(
            "Π (1 : Sort(0), Π (2 : Sort(0), Bound(0)))",
            term_to_string(unlift_res, &exp.zk_input.terms, &HashMap::new())
        );

        simulate(exp.zk_input, true, &HashMap::new());
    }

    #[test]
    fn get_arg() {
        let mut exp = Exporter::new();

        let term = app(sort(0), sort(1));
        let zk_term = exp.export_term(term, 0, None);

        let get_arg_rule = exp.export_get_arg(zk_term, 0).unwrap();
        let get_arg_res = exp.get_zk_rule(get_arg_rule).result_term_idx;

        assert_eq!(
            "Sort(1)",
            term_to_string(get_arg_res, &exp.zk_input.terms, &HashMap::new())
        );

        simulate(exp.zk_input.clone(), false, &HashMap::new());

        let term = app(
            app(app(app(app(sort(0), sort(1)), sort(2)), sort(3)), sort(4)),
            sort(5),
        );
        let zk_term = exp.export_term(term, 0, None);

        let get_arg_rule = exp.export_get_arg(zk_term, 2).unwrap();
        let get_arg_res = exp.get_zk_rule(get_arg_rule).result_term_idx;
        assert_eq!(
            "Sort(3)",
            term_to_string(get_arg_res, &exp.zk_input.terms, &HashMap::new())
        );
        simulate(exp.zk_input.clone(), false, &HashMap::new());
    }

    #[test]
    fn apply_elim() {
        let mut exp = Exporter::new();

        let rec = sort(0);
        let elim = sort(1);
        let term = app(sort(2), sort(3));
        let zk_rec = exp.export_term(rec, 0, None);
        let zk_elim = exp.export_term(elim, 0, None);
        let zk_term = exp.export_term(term, 0, None);

        let apply_elim_norec = exp
            .export_apply_elim(zk_term, zk_rec, zk_elim, 1, 0)
            .unwrap();
        let apply_elim_res = exp.get_zk_rule(apply_elim_norec).result_term_idx;

        assert_eq!(
            "App(Sort(1), Sort(3))",
            term_to_string(apply_elim_res, &exp.zk_input.terms, &HashMap::new())
        );

        simulate(exp.zk_input.clone(), false, &HashMap::new());

        let term = app(
            app(app(app(app(sort(2), sort(3)), sort(4)), sort(5)), sort(6)),
            sort(7),
        );
        let zk_term = exp.export_term(term, 0, None);

        let apply_elim_rec = exp
            .export_apply_elim(zk_term, zk_rec, zk_elim, 2, 3)
            .unwrap();
        let apply_elim_res = exp.get_zk_rule(apply_elim_rec).result_term_idx;
        assert_eq!(
            "App(App(App(App(App(Sort(1), Sort(3)), Sort(4)), App(Sort(0), Sort(5))), App(Sort(0), Sort(6))), App(Sort(0), Sort(7)))",
            term_to_string(apply_elim_res, &exp.zk_input.terms, &HashMap::new())
        );
        simulate(exp.zk_input.clone(), false, &HashMap::new());
    }

    #[test]
    fn apply_elim_eval() {
        let mut exp = Exporter::new();

        let rec = sort(0);
        let elim = lam(sort(3), sort(5));
        let term = app(sort(2), sort(3));
        let zk_rec = exp.export_term(rec, 0, None);
        let zk_elim = exp.export_term(elim, 0, None);
        let zk_term = exp.export_term(term, 0, None);

        let apply_elim_norec = exp
            .export_apply_elim_eval(
                zk_term,
                HashList::EMPTY,
                &mut HashMap::new(),
                0,
                zk_rec,
                zk_elim,
                1,
                0,
            )
            .unwrap();
        let apply_elim_res = exp.get_zk_rule(apply_elim_norec).result_term_idx;

        assert_eq!(
            "Sort(5)",
            term_to_string(apply_elim_res, &exp.zk_input.terms, &HashMap::new())
        );

        simulate(exp.zk_input.clone(), false, &HashMap::new());
    }

    // TODO: add some fail tests for shadowing / not actually replacing vars
}
