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

use once_cell::sync::Lazy;

mod sim;

static mut LIFT_COUNTS_MAP: Lazy<HashMap<usize, usize>> = Lazy::new(|| HashMap::new());
static mut SEEN_TY_TERMS: Lazy<HashSet<usize>> = Lazy::new(|| HashSet::new());

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

// Lean4 extensions
const EXPR_PROJ: usize = 10;
const EXPR_PROJ_PLACEHOLDER: usize = 11;

const EMPTY_CONTEXT_IDX: usize = 0;

fn kind_to_string(kind: usize) -> &'static str {
    match kind {
        0 => "NULL",
        1 => "VAR",
        2 => "SORT",
        3 => "APP",
        4 => "LAM",
        5 => "PI",
        6 => "AX",
        7 => "IND",
        8 => "IND_CTOR",
        9 => "IND_REC",
        10 => "PROJ",
        11 => "PROJ_PLACEHOLDER",
        _ => "UNKNOWN",
    }
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct ExpTerm {
    kind: usize,
    name: usize, // TODO: can we compress?
    left: usize,
    right: usize,

    ind: usize,
    ind_ctor: usize,

    top_level_func: usize,
    argc: usize, // TODO:
    // minimum name bound in this term
    // if it is less than the maximum bound name in the current proof step,
    // we must alpha rename
    // Terms that don't bind names keep this as usize::MAX
    //min_binding: usize,
    ax: usize,

    // index for proj...
    index: usize,
}

impl ExpTerm {
    const MAX_BINDING: usize = 127;

    pub fn new(
        kind: usize,
        name: usize,
        left: usize,
        right: usize,
        ind: usize,
        ind_ctor: usize,
        ax: usize,
    ) -> ExpTerm {
        ExpTerm {
            kind,
            name,
            left,
            right,
            ind,
            ind_ctor,
            top_level_func: 0,
            argc: 0,
            ax,
            index: 0,
            //min_binding,
        }
    }

    pub fn bound(name: usize) -> ExpTerm {
        ExpTerm::new(EXPR_VAR, name, 0, 0, 0, 0, 0)
    }

    // TODO: remove binding
    pub fn sort(level: usize) -> ExpTerm {
        ExpTerm::new(EXPR_SORT, level, 0, 0, 0, 0, 0)
    }

    pub fn lam(name: usize, domain: usize, body: usize) -> ExpTerm {
        ExpTerm::new(EXPR_LAM, name, domain, body, 0, 0, 0)
    }

    pub fn pi(name: usize, domain: usize, body: usize) -> ExpTerm {
        ExpTerm::new(EXPR_PI, name, domain, body, 0, 0, 0)
    }

    pub fn app(f: usize, e: usize, top_level_func: usize, exporter: &Exporter) -> ExpTerm {
        let mut res = ExpTerm::new(EXPR_APP, 0, f, e, 0, 0, 0);
        let f_term = exporter.get_zk_term(f);
        if f_term.kind == EXPR_APP {
            res.top_level_func = f_term.top_level_func;
        } else {
            res.top_level_func = f;
        }
        res.argc = exporter.get_zk_term(f).argc + 1;
        res
    }

    pub fn ax(idx: usize, dedup: usize) -> ExpTerm {
        // TODO: remove dedup from final version
        ExpTerm::new(EXPR_AX, 0, 0, dedup, 0, 0, idx)
    }

    pub fn ind(idx: usize) -> ExpTerm {
        ExpTerm::new(EXPR_IND, 0, 0, 0, idx, 0, 0)
    }

    pub fn ind_ctor(ind_idx: usize, ctor_idx: usize) -> ExpTerm {
        ExpTerm::new(EXPR_IND_CTOR, 0, 0, 0, ind_idx, ctor_idx, 0)
    }

    pub fn ind_rec(ind_idx: usize, motive_sort: usize) -> ExpTerm {
        // TODO: technically this could cause errors if motive_sort > num_rules
        ExpTerm::new(EXPR_IND_REC, 0, 0, 0, ind_idx, motive_sort, 0)
    }

    pub fn proj(index: usize, e: usize) -> ExpTerm {
        // TODO: technically this could cause errors if motive_sort > num_rules
        let mut res = ExpTerm::new(EXPR_PROJ, 0, e, 0, 0, 0, 0);
        res.index = index;
        res
    }

    pub fn proj_placeholder(inductive: usize) -> ExpTerm {
        // TODO: technically this could cause errors if motive_sort > num_rules
        let mut res = ExpTerm::new(EXPR_PROJ_PLACEHOLDER, 0, 0, 0, inductive, 0, 0);
        res
    }
}

const MAX_RULES: usize = 20;
#[derive(Debug, Clone)]
pub struct ExpInd {
    ty: usize,
    num_params: usize,

    rules: usize,
    rule_nnrs: usize,
    rule_nrs: usize,
    num_rules: usize,
    //elims: [usize; 5],
    rec_body: usize,
    //elim_body: usize,
    elim_argc: usize,
    projector: usize,
}

impl ExpInd {
    fn new() -> ExpInd {
        Self {
            ty: 0,
            num_params: 0,

            rules: 0,
            rule_nnrs: 0,
            rule_nrs: 0,
            num_rules: 0,
            //elims: [usize; 5],
            rec_body: 0,
            //elim_body: usize,
            elim_argc: 0,
            projector: 0,
        }
    }
}

const RULE_NULL: usize = 0;

// evaluation rules
const RULE_EVAL_ID: usize = 1;
const RULE_EVAL_VAR: usize = 2;
const RULE_EVAL_SORT: usize = 3; // TODO: unused
const RULE_EVAL_APP: usize = 4;
const RULE_EVAL_APP_LAM: usize = 5;
const RULE_EVAL_APP_LAM_SUB: usize = 28;
const RULE_EVAL_APP_PI: usize = 6;
const RULE_EVAL_LAM: usize = 7;
const RULE_EVAL_PI: usize = 8;
const RULE_EVAL_AX: usize = 9;

const RULE_TYPE_VAR: usize = 10;
const RULE_TYPE_SORT: usize = 11;
const RULE_TYPE_APP: usize = 12;
const RULE_TYPE_APP_SUB: usize = 30;
const RULE_TYPE_LAM: usize = 13;
const RULE_TYPE_PI: usize = 14;
const RULE_TYPE_PI_SUB: usize = 29;
const RULE_TYPE_AX: usize = 15;

const RULE_LIFT: usize = 16;

const RULE_PROOF_IRREL: usize = 17;
const RULE_PROOF_IRREL_SUB1: usize = 33;
const RULE_EVAL_TYPE: usize = 18;

const RULE_APPLY_ELIM: usize = 19;
const RULE_GET_ARG: usize = 20;

const RULE_APPLY_ELIM_EVAL: usize = 21;

const RULE_TYPE_IND: usize = 22;
const RULE_TYPE_IND_CTOR: usize = 23;
const RULE_TYPE_IND_REC: usize = 24;
const RULE_IND_PREFIX: usize = 25;

const RULE_EVAL_IND: usize = 26;
const RULE_EVAL_IND_SUB1: usize = 31;
const RULE_EVAL_IND_SUB2: usize = 32;
const RULE_EVAL_TRANSITIVE: usize = 27;

const RULE_EVAL_ETA: usize = 33;
const RULE_EVAL_ETA_SUB1: usize = 34;
const RULE_EVAL_ETA_SUB2: usize = 35;

// Lean4 extensions
const RULE_EVAL_PROJ: usize = 34;
const RULE_TYPE_PROJ: usize = 35;

const RULE_WALK_PROJ: usize = 36;
const RULE_CONSTR_PROJ: usize = 37;
const RULE_EVAL_PROJ_SIMPL: usize = 38;

const RULE_COLLECT_ARGS: usize = 40;

fn rule_to_string(rule: usize) -> &'static str {
    match rule {
        RULE_EVAL_ID => "RULE_EVAL_ID",
        RULE_EVAL_VAR => "RULE_EVAL_VAR",
        RULE_EVAL_SORT => "RULE_EVAL_SORT",
        RULE_EVAL_APP => "RULE_EVAL_APP",
        RULE_EVAL_APP_LAM => "RULE_EVAL_APP_LAM",
        RULE_EVAL_APP_LAM_SUB => "RULE_EVAL_APP_LAM_SUB",
        RULE_EVAL_APP_PI => "RULE_EVAL_APP_PI",
        RULE_EVAL_LAM => "RULE_EVAL_LAM",
        RULE_EVAL_PI => "RULE_EVAL_PI",
        RULE_EVAL_AX => "RULE_EVAL_AX",

        RULE_TYPE_VAR => "RULE_TYPE_VAR",
        RULE_TYPE_SORT => "RULE_TYPE_SORT",
        RULE_TYPE_APP => "RULE_TYPE_APP",
        RULE_TYPE_APP_SUB => "RULE_TYPE_APP_SUB",
        RULE_TYPE_LAM => "RULE_TYPE_LAM",
        RULE_TYPE_PI => "RULE_TYPE_PI",
        RULE_TYPE_PI_SUB => "RULE_TYPE_PI_SUB",
        RULE_TYPE_AX => "RULE_TYPE_AX",

        RULE_LIFT => "RULE_LIFT",

        RULE_PROOF_IRREL => "RULE_PROOF_IRREL",
        RULE_PROOF_IRREL_SUB1 => "RULE_PROOF_IRREL_SUB1",
        RULE_EVAL_TYPE => "RULE_EVAL_TYPE",

        RULE_APPLY_ELIM => "RULE_APPLY_ELIM",
        RULE_GET_ARG => "RULE_GET_ARG",

        RULE_APPLY_ELIM_EVAL => "RULE_APPLY_ELIM_EVAL",

        RULE_TYPE_IND => "RULE_TYPE_IND",
        RULE_TYPE_IND_CTOR => "RULE_TYPE_IND_CTOR",
        RULE_TYPE_IND_REC => "RULE_TYPE_IND_REC",
        RULE_IND_PREFIX => "RULE_IND_PREFIX",

        RULE_EVAL_IND => "RULE_EVAL_IND",
        RULE_EVAL_IND_SUB1 => "RULE_EVAL_IND_SUB1",
        RULE_EVAL_IND_SUB2 => "RULE_EVAL_IND_SUB2",
        RULE_EVAL_TRANSITIVE => "RULE_EVAL_TRANSITIVE",

        RULE_EVAL_ETA => "RULE_EVAL_ETA",
        RULE_EVAL_ETA_SUB1 => "RULE_EVAL_ETA_SUB1",
        RULE_EVAL_ETA_SUB2 => "RULE_EVAL_ETA_SUB2",

        RULE_EVAL_PROJ => "RULE_EVAL_PROJ",
        RULE_TYPE_PROJ => "RULE_TYPE_PROJ",

        RULE_WALK_PROJ => "RULE_WALK_PROJ",
        RULE_CONSTR_PROJ => "RULE_CONSTR_PROJ",
        RULE_EVAL_PROJ_SIMPL => "RULE_EVAL_PROJ_SIMPL",
        _ => "UNKNOWN",
    }
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct ExpLift {
    max_binding: usize,
    parent0: usize,
    parent1: usize,
    min_binding_seen: usize,
    input_term_idx: usize,
    result_term_idx: usize,
}

impl ExpLift {
    pub fn lift(
        input: usize,
        result: usize,
        max_binding: usize,
        min_binding_seen: usize,
        parent0: usize,
        parent1: usize,
    ) -> ExpLift {
        ExpLift {
            max_binding,
            parent0,
            parent1,
            min_binding_seen,
            input_term_idx: input,
            result_term_idx: result,
        }
    }
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct ExpRule {
    rule: usize,
    ctx_idx: usize,
    max_binding: usize,
    parent0: usize,
    parent1: usize,
    parent0_quot: usize,
    parent1_quot: usize,
    lift_rule: usize,
    input_term_idx: usize,
    result_term_idx: usize,
    extra: usize,
    extra2: usize,
    extra3: usize,
    extra4: usize,
    extra5: usize,
    extra6: usize,
    inductive: usize,
    ind_rule: usize,
    ind_ctor_quot: usize,
    ind_nnr_quot: usize,
    ind_nr_quot: usize,
}

impl ExpRule {
    pub fn new() -> ExpRule {
        Self {
            rule: 0,
            ctx_idx: 0,
            max_binding: 0,
            parent0: 0,
            parent1: 0,
            parent0_quot: 0,
            parent1_quot: 0,
            lift_rule: 0,
            input_term_idx: 0,
            result_term_idx: 0,
            extra: 0,
            extra2: 0,
            extra3: 0,
            extra4: 0,
            extra5: 0,
            extra6: 0,
            inductive: 0,
            ind_rule: 0,
            ind_ctor_quot: 0,
            ind_nnr_quot: 0,
            ind_nr_quot: 0,
        }
    }
    // TODO:
    pub fn eval_id(term: usize, ctx_idx: usize, max_binding: usize) -> ExpRule {
        ExpRule {
            rule: RULE_EVAL_ID,
            ctx_idx,
            max_binding,
            parent0: 0,
            parent1: 0,
            parent0_quot: HashList::EMPTY,
            parent1_quot: HashList::EMPTY,
            lift_rule: 0,
            input_term_idx: term,
            result_term_idx: term,
            extra: 0,
            extra2: 0,
            extra3: 0,
            extra4: 0,
            extra5: 0,
            extra6: 0,
            inductive: 0,
            ind_rule: 0,
            ind_ctor_quot: 0,
            ind_nnr_quot: 0,
            ind_nr_quot: 0,
        }
    }

    pub fn eval_var(
        input: usize,
        result: usize,
        context: usize,
        max_binding: usize,
        lift_rule: usize,
    ) -> ExpRule {
        ExpRule {
            rule: RULE_EVAL_VAR,
            ctx_idx: context,
            max_binding,
            parent0: 0,
            parent1: 0,
            parent0_quot: HashList::EMPTY, // TODO: this goes against convention: is remainder for ctx lookup of key and value
            parent1_quot: HashList::EMPTY,
            lift_rule,
            input_term_idx: input,
            result_term_idx: result,
            extra: 0,
            extra2: 0,
            extra3: 0,
            extra4: 0,
            extra5: 0,
            extra6: 0,
            inductive: 0,
            ind_rule: 0,
            ind_ctor_quot: 0,
            ind_nnr_quot: 0,
            ind_nr_quot: 0,
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
            parent0_quot,
            parent1_quot,
            lift_rule: 0,
            input_term_idx: input,
            result_term_idx: result,
            extra: 0,
            extra2: 0,
            extra3: 0,
            extra4: 0,
            extra5: 0,
            extra6: 0,
            inductive: 0,
            ind_rule: 0,
            ind_ctor_quot: 0,
            ind_nnr_quot: 0,
            ind_nr_quot: 0,
        }
    }

    pub fn eval_app_lam_p1(
        input: usize,
        result: usize,
        context: usize,
        parent0: usize,
        parent0_quot: usize,
        parent1: usize,
        parent1_quot: usize,
        lift_rule: usize,
        max_binding: usize,
        e: usize,
    ) -> ExpRule {
        ExpRule {
            rule: RULE_EVAL_APP_LAM_SUB,
            ctx_idx: context,
            max_binding,
            parent0,
            parent1,
            parent0_quot,
            parent1_quot,
            lift_rule,
            input_term_idx: input,
            result_term_idx: result,
            extra: e,
            extra2: 0,
            extra3: 0,
            extra4: 0,
            extra5: 0,
            extra6: 0,
            inductive: 0,
            ind_rule: 0,
            ind_ctor_quot: 0,
            ind_nnr_quot: 0,
            ind_nr_quot: 0,
        }
    }

    pub fn eval_app_lam_p2(
        input: usize,
        result: usize,
        context: usize,
        parent0: usize,
        parent0_quot: usize,
        parent1: usize, // thsi should be eval_app_lam_p1
        max_binding: usize,
    ) -> ExpRule {
        ExpRule {
            rule: RULE_EVAL_APP_LAM,
            ctx_idx: context,
            max_binding,
            parent0,
            parent1,
            parent0_quot,
            parent1_quot: HashList::EMPTY,
            lift_rule: 0,
            input_term_idx: input,
            result_term_idx: result,
            extra: 0,
            extra2: 0,
            extra3: 0,
            extra4: 0,
            extra5: 0,
            extra6: 0,
            inductive: 0,
            ind_rule: 0,
            ind_ctor_quot: 0,
            ind_nnr_quot: 0,
            ind_nr_quot: 0,
        }
    }

    //pub fn eval_lam(
    //    input: usize,
    //    result: usize,
    //    context: usize,
    //    parent0: usize,
    //    parent0_quot: usize,
    //    max_binding: usize,
    //) -> ExpRule {
    //    ExpRule {
    //        rule: RULE_EVAL_LAM,
    //        ctx_idx: context,
    //        max_binding,
    //        parent0,
    //        parent1: 0,
    //        parent0_quot,
    //        parent1_quot: HashList::EMPTY,
    //        input_term_idx: input,
    //        result_term_idx: result,
    //    }
    //}

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
            parent0_quot,
            parent1_quot,
            lift_rule: 0,
            input_term_idx: input,
            result_term_idx: result,
            extra: 0,
            extra2: 0,
            extra3: 0,
            extra4: 0,
            extra5: 0,
            extra6: 0,
            inductive: 0,
            ind_rule: 0,
            ind_ctor_quot: 0,
            ind_nnr_quot: 0,
            ind_nr_quot: 0,
        }
    }

    pub fn ty_var(
        input: usize,
        result: usize,
        context: usize,
        max_binding: usize,
        lift_rule: usize,
    ) -> ExpRule {
        ExpRule {
            rule: RULE_TYPE_VAR,
            ctx_idx: context,
            max_binding,
            parent0: 0,
            parent1: 0,
            parent0_quot: HashList::EMPTY, // TODO: this goes against convention: is remainder for ctx lookup of key and value
            parent1_quot: HashList::EMPTY,
            lift_rule,
            input_term_idx: input,
            result_term_idx: result,
            extra: 0,
            extra2: 0,
            extra3: 0,
            extra4: 0,
            extra5: 0,
            extra6: 0,
            inductive: 0,
            ind_rule: 0,
            ind_ctor_quot: 0,
            ind_nnr_quot: 0,
            ind_nr_quot: 0,
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
            parent0_quot: HashList::EMPTY,
            parent1_quot: HashList::EMPTY,
            lift_rule: 0,
            input_term_idx: input,
            result_term_idx: result,
            extra: 0,
            extra2: 0,
            extra3: 0,
            extra4: 0,
            extra5: 0,
            extra6: 0,
            inductive: 0,
            ind_rule: 0,
            ind_ctor_quot: 0,
            ind_nnr_quot: 0,
            ind_nr_quot: 0,
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
            parent0_quot,
            parent1_quot: HashList::EMPTY,
            lift_rule: 0,
            input_term_idx: input,
            result_term_idx: result,
            extra: 0,
            extra2: 0,
            extra3: 0,
            extra4: 0,
            extra5: 0,
            extra6: 0,
            inductive: 0,
            ind_rule: 0,
            ind_ctor_quot: 0,
            ind_nnr_quot: 0,
            ind_nr_quot: 0,
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
        max_binding: usize,
    ) -> ExpRule {
        ExpRule {
            rule: RULE_TYPE_PI,
            ctx_idx: context,
            max_binding,
            parent0,
            parent1,
            parent0_quot,
            parent1_quot,
            lift_rule: 0,
            input_term_idx: input,
            result_term_idx: result,
            extra: 0,
            extra2: 0,
            extra3: 0,
            extra4: 0,
            extra5: 0,
            extra6: 0,
            inductive: 0,
            ind_rule: 0,
            ind_ctor_quot: 0,
            ind_nnr_quot: 0,
            ind_nr_quot: 0,
        }
    }

    pub fn ty_pi_sub(
        input: usize,
        result: usize,
        context: usize,
        parent0: usize,
        parent0_quot: usize,
        parent1: usize,
        parent1_quot: usize,
        max_binding: usize,
        v: usize,
    ) -> ExpRule {
        ExpRule {
            rule: RULE_TYPE_PI_SUB,
            ctx_idx: context,
            max_binding,
            parent0,
            parent1,
            parent0_quot,
            parent1_quot,
            lift_rule: 0,
            input_term_idx: input,
            result_term_idx: result,
            extra: v,
            extra2: 0,
            extra3: 0,
            extra4: 0,
            extra5: 0,
            extra6: 0,
            inductive: 0,
            ind_rule: 0,
            ind_ctor_quot: 0,
            ind_nnr_quot: 0,
            ind_nr_quot: 0,
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
        lift_rule: usize,
        max_binding: usize,
    ) -> ExpRule {
        ExpRule {
            rule: RULE_TYPE_APP,
            ctx_idx: context,
            max_binding,
            parent0,
            parent1,
            parent0_quot,
            parent1_quot,
            lift_rule,
            input_term_idx: input,
            result_term_idx: result,
            extra: 0,
            extra2: 0,
            extra3: 0,
            extra4: 0,
            extra5: 0,
            extra6: 0,
            inductive: 0,
            ind_rule: 0,
            ind_ctor_quot: 0,
            ind_nnr_quot: 0,
            ind_nr_quot: 0,
        }
    }

    pub fn ty_app_sub(
        input: usize,
        result: usize,
        context: usize,
        parent0: usize,
        parent0_quot: usize,
        parent1: usize,
        parent1_quot: usize,
        max_binding: usize,
        a: usize,
    ) -> ExpRule {
        ExpRule {
            rule: RULE_TYPE_APP_SUB,
            ctx_idx: context,
            max_binding,
            parent0,
            parent1,
            parent0_quot,
            parent1_quot,
            lift_rule: 0,
            input_term_idx: input,
            result_term_idx: result,
            extra: a,
            extra2: 0,
            extra3: 0,
            extra4: 0,
            extra5: 0,
            extra6: 0,
            inductive: 0,
            ind_rule: 0,
            ind_ctor_quot: 0,
            ind_nnr_quot: 0,
            ind_nr_quot: 0,
        }
    }

    pub fn ty_ax(input: usize, result: usize, max_binding: usize, lift_rule: usize) -> ExpRule {
        ExpRule {
            rule: RULE_TYPE_AX,
            ctx_idx: HashList::EMPTY,
            max_binding,
            parent0: 0,
            parent1: 0,
            parent0_quot: HashList::EMPTY,
            parent1_quot: HashList::EMPTY,
            lift_rule,
            input_term_idx: input,
            result_term_idx: result,
            extra: 0,
            extra2: 0,
            extra3: 0,
            extra4: 0,
            extra5: 0,
            extra6: 0,
            inductive: 0,
            ind_rule: 0,
            ind_ctor_quot: 0,
            ind_nnr_quot: 0,
            ind_nr_quot: 0,
        }
    }

    pub fn proof_irrel(
        input: usize,
        result: usize,
        context: usize,
        max_binding: usize,
        parent0: usize,
        parent1: usize,
    ) -> ExpRule {
        ExpRule {
            rule: RULE_PROOF_IRREL,
            ctx_idx: context,
            max_binding,
            parent0,
            parent1,
            parent0_quot: HashList::EMPTY,
            parent1_quot: HashList::EMPTY,
            lift_rule: 0,
            input_term_idx: input,
            result_term_idx: result,
            extra: 0,
            extra2: 0,
            extra3: 0,
            extra4: 0,
            extra5: 0,
            extra6: 0,
            inductive: 0,
            ind_rule: 0,
            ind_ctor_quot: 0,
            ind_nnr_quot: 0,
            ind_nr_quot: 0,
        }
    }
    pub fn proof_irrel_sub1(
        input: usize,
        result: usize,
        context: usize,
        max_binding: usize,
        parent0: usize,
        parent1: usize,
        t: usize,
    ) -> ExpRule {
        ExpRule {
            rule: RULE_PROOF_IRREL_SUB1,
            ctx_idx: context,
            max_binding,
            parent0,
            parent1,
            parent0_quot: HashList::EMPTY,
            parent1_quot: HashList::EMPTY,
            lift_rule: 0,
            input_term_idx: input,
            result_term_idx: result,
            extra: t,
            extra2: 0,
            extra3: 0,
            extra4: 0,
            extra5: 0,
            extra6: 0,
            inductive: 0,
            ind_rule: 0,
            ind_ctor_quot: 0,
            ind_nnr_quot: 0,
            ind_nr_quot: 0,
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
            parent0_quot: HashList::EMPTY,
            parent1_quot: HashList::EMPTY,
            lift_rule: 0,
            input_term_idx: input,
            result_term_idx: result,
            extra: 0,
            extra2: 0,
            extra3: 0,
            extra4: 0,
            extra5: 0,
            extra6: 0,
            inductive: 0,
            ind_rule: 0,
            ind_ctor_quot: 0,
            ind_nnr_quot: 0,
            ind_nr_quot: 0,
        }
    }

    pub fn get_arg(input: usize, result: usize, count: usize, parent0: usize) -> ExpRule {
        ExpRule {
            rule: RULE_GET_ARG,
            ctx_idx: 0,
            max_binding: 0,
            parent0,
            parent1: 0,
            parent0_quot: 0,
            parent1_quot: 0,
            lift_rule: 0,
            input_term_idx: input,
            result_term_idx: result,
            extra: count,
            extra2: 0,
            extra3: 0,
            extra4: 0,
            extra5: 0,
            extra6: 0,
            inductive: 0,
            ind_rule: 0,
            ind_ctor_quot: 0,
            ind_nnr_quot: 0,
            ind_nr_quot: 0,
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
        apply_recs: usize,
        parent0: usize,
        orig_idx: usize,
    ) -> ExpRule {
        ExpRule {
            rule: RULE_APPLY_ELIM,
            ctx_idx: context,
            max_binding: 0, //TODO: fxi
            parent0,
            parent1: 0,
            parent0_quot: 0,
            parent1_quot: HashList::EMPTY,
            lift_rule: 0,
            input_term_idx: input,
            result_term_idx: result,
            extra: num_nonrecs,
            extra2: num_recs,
            extra3: rec,
            extra4: e_i,
            extra5: apply_recs,
            extra6: orig_idx,
            inductive: 0,
            ind_rule: 0,
            ind_ctor_quot: 0,
            ind_nnr_quot: 0,
            ind_nr_quot: 0,
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
            parent0_quot: 0,
            parent1_quot: HashList::EMPTY,
            lift_rule: 0,
            input_term_idx: input,
            result_term_idx: result,
            extra: num_nonrecs,
            extra2: num_recs,
            extra3: rec,
            extra4: e_i,
            extra5: 0,
            extra6: 0,
            inductive: 0,
            ind_rule: 0,
            ind_ctor_quot: 0,
            ind_nnr_quot: 0,
            ind_nr_quot: 0,
        }
    }

    pub fn ty_ind(input: usize, result: usize, max_binding: usize, lift_rule: usize) -> ExpRule {
        ExpRule {
            rule: RULE_TYPE_IND,
            ctx_idx: HashList::EMPTY,
            max_binding,
            parent0: 0,
            parent1: 0,
            parent0_quot: 0,
            parent1_quot: 0,
            lift_rule,
            input_term_idx: input,
            result_term_idx: result,
            extra: 0,
            extra2: 0,
            extra3: 0,
            extra4: 0,
            extra5: 0,
            extra6: 0,
            inductive: 0,
            ind_rule: 0,
            ind_ctor_quot: 0,
            ind_nnr_quot: 0,
            ind_nr_quot: 0,
        }
    }

    pub fn ty_ind_ctor(
        input: usize,
        result: usize,
        max_binding: usize,
        lift_rule: usize,
        ind_ctor_quot: usize,
    ) -> ExpRule {
        ExpRule {
            rule: RULE_TYPE_IND_CTOR,
            ctx_idx: HashList::EMPTY,
            max_binding,
            parent0: 0,
            parent1: 0,
            parent0_quot: 0,
            parent1_quot: 0,
            lift_rule,
            input_term_idx: input,
            result_term_idx: result,
            extra: 0,
            extra2: 0,
            extra3: 0,
            extra4: 0,
            extra5: 0,
            extra6: 0,
            inductive: 0,
            ind_rule: 0,
            ind_ctor_quot,
            ind_nnr_quot: 0,
            ind_nr_quot: 0,
        }
    }

    pub fn ty_ind_rec(
        input: usize,
        result: usize,
        max_binding: usize,
        parent0: usize,
        lift_rule: usize,
    ) -> ExpRule {
        ExpRule {
            rule: RULE_TYPE_IND_REC,
            ctx_idx: HashList::EMPTY,
            max_binding,
            parent0,
            parent1: 0,
            parent0_quot: 0,
            parent1_quot: 0,
            lift_rule,
            input_term_idx: input,
            result_term_idx: result,
            extra: 0,
            extra2: 0,
            extra3: 0,
            extra4: 0,
            extra5: 0,
            extra6: 0,
            inductive: 0,
            ind_rule: 0,
            ind_ctor_quot: 0,
            ind_nnr_quot: 0,
            ind_nr_quot: 0,
        }
    }

    pub fn ind_pref(input: usize, result: usize, n: usize, elim: usize, parent0: usize) -> ExpRule {
        ExpRule {
            rule: RULE_IND_PREFIX,
            ctx_idx: HashList::EMPTY,
            max_binding: 0,
            parent0,
            parent1: 0,
            parent0_quot: HashList::EMPTY,
            parent1_quot: HashList::EMPTY,
            lift_rule: 0,
            input_term_idx: input,
            result_term_idx: result,
            extra: n,
            extra2: elim,
            extra3: 0,
            extra4: 0,
            extra5: 0,
            extra6: 0,
            inductive: 0,
            ind_rule: 0,
            ind_ctor_quot: 0,
            ind_nnr_quot: 0,
            ind_nr_quot: 0,
        }
    }

    pub fn eval_ind(
        input: usize,
        result: usize,
        context: usize,
        max_binding: usize,
        inductive: usize,
        parent0: usize,
        parent1: usize,
    ) -> ExpRule {
        ExpRule {
            rule: RULE_EVAL_IND,
            ctx_idx: context,
            max_binding,
            parent0,
            parent1,
            parent0_quot: 0, // TODO: Fix
            parent1_quot: 0, // TODO: fix
            lift_rule: 0,
            input_term_idx: input,
            result_term_idx: result,
            extra: 0,
            extra2: 0,
            extra3: 0,
            extra4: 0,
            extra5: 0,
            extra6: 0,
            inductive,
            ind_rule: 0,
            ind_ctor_quot: 0,
            ind_nnr_quot: 0,
            ind_nr_quot: 0,
        }
    }

    pub fn eval_ind_sub1(
        input: usize,
        result: usize,
        context: usize,
        max_binding: usize,
        inductive: usize,
        ind_rule_idx: usize,
        parent0: usize,
        parent1: usize,
    ) -> ExpRule {
        ExpRule {
            rule: RULE_EVAL_IND_SUB1,
            ctx_idx: context,
            max_binding,
            parent0,
            parent1,
            parent0_quot: 0, // TODO: Fix
            parent1_quot: 0, // TODO: fix
            lift_rule: 0,
            input_term_idx: input,
            result_term_idx: result,
            extra: 0,
            extra2: 0,
            extra3: 0,
            extra4: 0,
            extra5: 0,
            extra6: 0,
            inductive,
            ind_rule: ind_rule_idx,
            ind_ctor_quot: 0,
            ind_nnr_quot: 0,
            ind_nr_quot: 0,
        }
    }

    pub fn eval_ind_sub2(
        input: usize,
        result: usize,
        context: usize,
        max_binding: usize,
        inductive: usize,
        ind_rule_idx: usize,
        ind_elim: usize,
        rec: usize,
        parent0: usize,
        parent1: usize,
        nnr_quot: usize,
        nr_quot: usize,
    ) -> ExpRule {
        ExpRule {
            rule: RULE_EVAL_IND_SUB2,
            ctx_idx: context,
            max_binding,
            parent0,
            parent1,
            parent0_quot: 0, // TODO: Fix
            parent1_quot: 0, // TODO: fix
            lift_rule: 0,
            input_term_idx: input,
            result_term_idx: result,
            extra: 0,
            extra2: ind_elim,
            extra3: rec,
            extra4: 0,
            extra5: 0,
            extra6: 0,
            inductive,
            ind_rule: ind_rule_idx,
            ind_ctor_quot: 0,
            ind_nnr_quot: nnr_quot,
            ind_nr_quot: nr_quot,
        }
    }

    pub fn eval_transitive(
        input: usize,
        result: usize,
        context: usize,
        max_binding: usize,
        parent0: usize,
        parent1: usize,
    ) -> ExpRule {
        ExpRule {
            rule: RULE_EVAL_TRANSITIVE,
            ctx_idx: context,
            max_binding,
            parent0,
            parent1,
            parent0_quot: 0, // TODO: Fix
            parent1_quot: 0, // TODO: fix
            lift_rule: 0,
            input_term_idx: input,
            result_term_idx: result,
            extra: 0,
            extra2: 0,
            extra3: 0,
            extra4: 0,
            extra5: 0,
            extra6: 0,
            inductive: 0,
            ind_rule: 0,
            ind_ctor_quot: 0,
            ind_nnr_quot: 0,
            ind_nr_quot: 0,
        }
    }

    fn eval_eta(
        input: usize,
        result: usize,
        context: usize,
        max_binding: usize,
        parent0: usize,
        parent1: usize,
    ) -> ExpRule {
        ExpRule {
            rule: RULE_EVAL_ETA,
            ctx_idx: context,
            max_binding,
            parent0,
            parent1,
            parent0_quot: 0, // TODO: Fix
            parent1_quot: 0, // TODO: fix
            lift_rule: 0,
            input_term_idx: input,
            result_term_idx: result,
            extra: 0,
            extra2: 0,
            extra3: 0,
            extra4: 0,
            extra5: 0,
            extra6: 0,
            inductive: 0,
            ind_rule: 0,
            ind_ctor_quot: 0,
            ind_nnr_quot: 0,
            ind_nr_quot: 0,
        }
    }

    fn eval_eta_sub1(
        input: usize,
        result: usize,
        context: usize,
        max_binding: usize,
        parent0: usize,
        b: usize,
    ) -> ExpRule {
        ExpRule {
            rule: RULE_EVAL_ETA_SUB1,
            ctx_idx: context,
            max_binding,
            parent0,
            parent1: 0,
            parent0_quot: 0, // TODO: Fix
            parent1_quot: 0, // TODO: fix
            lift_rule: 0,
            input_term_idx: input,
            result_term_idx: result,
            extra: b,
            extra2: 0,
            extra3: 0,
            extra4: 0,
            extra5: 0,
            extra6: 0,
            inductive: 0,
            ind_rule: 0,
            ind_ctor_quot: 0,
            ind_nnr_quot: 0,
            ind_nr_quot: 0,
        }
    }

    fn eval_eta_sub2(input: usize, result: usize, context: usize, max_binding: usize) -> ExpRule {
        ExpRule {
            rule: RULE_EVAL_ETA_SUB1,
            ctx_idx: context,
            max_binding,
            parent0: 0,
            parent1: 0,
            parent0_quot: 0, // TODO: Fix
            parent1_quot: 0, // TODO: fix
            lift_rule: 0,
            input_term_idx: input,
            result_term_idx: result,
            extra: 0,
            extra2: 0,
            extra3: 0,
            extra4: 0,
            extra5: 0,
            extra6: 0,
            inductive: 0,
            ind_rule: 0,
            ind_ctor_quot: 0,
            ind_nnr_quot: 0,
            ind_nr_quot: 0,
        }
    }

    pub fn eval_proj(
        input: usize,
        result: usize,
        context: usize,
        parent0: usize, // eval
        parent0_quot: usize,
        parent1: usize, // get arg
        inductive: usize,
        max_binding: usize,
    ) -> ExpRule {
        ExpRule {
            rule: RULE_EVAL_PROJ,
            ctx_idx: context,
            max_binding,
            parent0,
            parent0_quot,
            parent1,
            parent1_quot: 0,
            lift_rule: 0,
            input_term_idx: input,
            result_term_idx: result,
            extra: 0,
            extra2: 0,
            extra3: 0,
            extra4: 0,
            extra5: 0,
            extra6: 0,
            inductive,
            ind_rule: 0,
            ind_ctor_quot: 0,
            ind_nnr_quot: 0,
            ind_nr_quot: 0,
        }
    }

    pub fn ty_proj(
        input: usize,
        result: usize,
        context: usize,
        parent0: usize, // typing
        parent1: usize, // walk_proj
        max_binding: usize,
    ) -> ExpRule {
        ExpRule {
            rule: RULE_TYPE_PROJ,
            ctx_idx: context,
            max_binding,
            parent0,
            parent0_quot: 0,
            parent1,
            parent1_quot: 0,
            lift_rule: 0,
            input_term_idx: input,
            result_term_idx: result,
            extra: 0,
            extra2: 0,
            extra3: 0,
            extra4: 0,
            extra5: 0,
            extra6: 0,
            inductive: 0,
            ind_rule: 0,
            ind_ctor_quot: 0,
            ind_nnr_quot: 0,
            ind_nr_quot: 0,
        }
    }

    pub fn walk_proj(
        input: usize,
        result: usize,
        parent0: usize, // walk_proj
        inductive: usize,
        lift: usize,
        max_binding: usize,
    ) -> ExpRule {
        ExpRule {
            rule: RULE_WALK_PROJ,
            ctx_idx: HashList::EMPTY,
            max_binding,
            parent0,
            parent0_quot: 0,
            parent1: 0,
            parent1_quot: 0,
            lift_rule: lift,
            input_term_idx: input,
            result_term_idx: result,
            extra: 0,
            extra2: 0,
            extra3: 0,
            extra4: 0,
            extra5: 0,
            extra6: 0,
            inductive,
            ind_rule: 0,
            ind_ctor_quot: 0,
            ind_nnr_quot: 0,
            ind_nr_quot: 0,
        }
    }

    pub fn ctor_proj(
        input: usize,
        result: usize,
        context: usize,
        inductive: usize,
        parent0: usize,
        parent0_quot: usize,
        parent1: usize,
    ) -> ExpRule {
        ExpRule {
            rule: RULE_CONSTR_PROJ,
            ctx_idx: context,
            max_binding: 0,
            parent0,
            parent0_quot,
            parent1,
            parent1_quot: 0,
            lift_rule: 0,
            input_term_idx: input,
            result_term_idx: result,
            extra: 0,
            extra2: 0,
            extra3: 0,
            extra4: 0,
            extra5: 0,
            extra6: 0,
            inductive,
            ind_rule: 0,
            ind_ctor_quot: 0,
            ind_nnr_quot: 0,
            ind_nr_quot: 0,
        }
    }

    pub fn eval_proj_simpl(
        input: usize,
        result: usize,
        context: usize,
        parent0: usize,
        parent0_quot: usize,
        max_binding: usize,
    ) -> ExpRule {
        ExpRule {
            rule: RULE_EVAL_PROJ_SIMPL,
            ctx_idx: context,
            max_binding,
            parent0,
            parent0_quot,
            parent1: 0,
            parent1_quot: 0,
            lift_rule: 0,
            input_term_idx: input,
            result_term_idx: result,
            extra: 0,
            extra2: 0,
            extra3: 0,
            extra4: 0,
            extra5: 0,
            extra6: 0,
            inductive: 0,
            ind_rule: 0,
            ind_ctor_quot: 0,
            ind_nnr_quot: 0,
            ind_nr_quot: 0,
        }
    }
    //pub fn alpha(term: usize, result: usize, parent0: usize, parent0_quoti
}

#[derive(Debug, Clone)]
pub struct HashList {
    alpha: usize,
    beta: usize,
    pub nodes: Vec<HashNode>,

    // map from hashes to hash nodes...
    node_mapping: HashMap<usize, usize>,
    max_names: HashMap<usize, usize>,
    //set_mapping: HashMap<BTreeSet<usize>, usize>,
}

// TODO: permute, etc....
impl HashList {
    const EMPTY: usize = 0;

    fn new() -> HashList {
        let mut rng = rand::thread_rng();

        let alpha = rng.gen();
        let beta = rng.gen();
        let mut max_names = HashMap::new();
        max_names.insert(HashList::EMPTY, 0);
        HashList {
            alpha,
            beta,
            nodes: vec![HashNode::empty()],
            node_mapping: HashMap::new(),
            max_names,
        }
    }

    pub fn len(&self) -> usize {
        self.nodes.len()
    }

    pub fn add(&mut self, list: usize, key: usize, value: usize) -> usize {
        if self.contains(list, key, value) {
            return list;
        }

        let prev_hash = if !self.nodes[list].empty {
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
            prev: list,
            empty: false,
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
        if self.nodes[list].empty {
            return false;
        }

        let list_head = &self.nodes[list];
        let rem = Wrapping(list_head.hash) % (self.hash(key, value));
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
        Wrapping(list_hash) - Wrapping(remainder_hash) * Wrapping(kv_hash) == Wrapping(0)
    }

    /// check if the passed in list is a subset, given the passed in remainder
    pub fn subset(&self, list: usize, subset: usize, remainder: usize) -> bool {
        let list_hash = if self.nodes[list].empty {
            1
        } else {
            self.nodes[list].hash
        };

        let subset_hash = if self.nodes[subset].empty {
            1
        } else {
            self.nodes[subset].hash
        };

        let remainder_hash = if self.nodes[remainder].empty {
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
        while !self.nodes[list].empty {
            res = res + &format!("({}, {}),", self.nodes[list].key, self.nodes[list].value);
            list = self.nodes[list].prev;
        }
        res += "]";
        res
    }

    pub fn get(&mut self, list: usize, key: usize) -> (usize, usize) {
        let mut list = list;
        let mut quot_list = HashList::EMPTY;
        let mut ret = None;
        while list != HashList::EMPTY {
            let k = self.nodes[list].key;
            let v = self.nodes[list].value;

            if k == key {
                ret = Some(v);
            } else {
                quot_list = self.add(quot_list, k, v);
            }

            list = self.nodes[list].prev;
        }

        return (ret.unwrap(), quot_list);
    }
}

#[derive(Debug, Clone)]
pub struct HashNode {
    key: usize,
    value: usize,
    hash: usize,

    // stash the value of the prev_hash to reduce lookups
    prev: usize,
    empty: bool,
}

impl HashNode {
    fn empty() -> Self {
        // ENSURE Can never be used...
        Self {
            key: usize::MAX,
            value: usize::MAX,
            hash: 1,
            prev: 0,
            empty: true,
        }
    }
}

#[derive(Debug, Clone)]
pub struct ZkInput {
    pub rules: Vec<ExpRule>,
    pub lifts: Vec<ExpLift>,
    pub terms: Vec<ExpTerm>,
    pub public_terms: Vec<ExpTerm>,
    pub axioms: Vec<usize>,
    pub expected_type: usize,
    pub proving_rule: usize,

    pub inductives: Vec<ExpInd>,
    pub ind_rules: HashList,
    pub ind_nnrs: HashList,
    pub ind_nrs: HashList,

    pub contexts: HashList,
}

impl ZkInput {
    fn new() -> ZkInput {
        ZkInput {
            rules: Vec::new(),
            terms: Vec::new(),
            lifts: Vec::new(),
            public_terms: Vec::new(),
            axioms: Vec::new(),
            expected_type: 0,
            proving_rule: 0,

            inductives: Vec::new(),
            ind_rules: HashList::new(),
            ind_nnrs: HashList::new(),
            ind_nrs: HashList::new(),

            contexts: HashList::new(),
        }
    }

    fn compress(&mut self) {
        // TODOS:
        // 1. sweep unused lifts
        // 2. sweep unused terms
        // 3. sweep unused contexts
        //
        let id = ExpRule::eval_id(0, 0, 0);
        self.rules.push(id);
        let id_idx = self.rules.len() - 1;

        // find rules that can convert to id...
        let mut cnt = 0;
        let mut marked = vec![false; self.rules.len()];
        let mut idx_rewrite = vec![0; self.rules.len()];
        let mut rules_clone = self.rules.clone();
        for (i, rule) in self.rules.iter_mut().enumerate() {
            let parent0 = &rules_clone[rule.parent0];
            let parent1 = &rules_clone[rule.parent1];

            use sim::is_eval_rule;
            if is_eval_rule(parent0.rule) && parent0.input_term_idx == parent0.result_term_idx {
                rule.parent0 = id_idx;
                cnt += 1;
            }
            if is_eval_rule(parent1.rule) && parent1.input_term_idx == parent1.result_term_idx {
                rule.parent1 = id_idx;
                cnt += 1;
            }
            //if rule.input_term_idx == rule.result_term_idx && sim::is_eval_rule(rule.rule) {
            //    rule.rule = RULE_EVAL_ID;
            //    rule.parent0 = 0;
            //    rule.parent1 = 0;
            //    rule.lift_rule = 0;
            //    rule.ctx_idx = HashList::EMPTY;
            //    cnt += 1;
            //}
        }

        // walk rules tree, sweep unused rules
        let mut marked = vec![false; self.rules.len()];
        let mut stack = vec![self.proving_rule, 0];
        let mut lift_marked = vec![false; self.lifts.len()];
        let mut lift_stack = vec![0];
        let mut term_marked = vec![false; self.terms.len()];
        let mut term_stack = vec![0];

        while !stack.is_empty() {
            let idx = stack.pop().unwrap();

            if marked[idx] {
                continue;
            }

            marked[idx] = true;

            let rule = &self.rules[idx];
            if !marked[rule.parent0] {
                stack.push(rule.parent0);
            }
            if !marked[rule.parent1] {
                stack.push(rule.parent1);
            }

            lift_stack.push(rule.lift_rule);
            term_stack.push(rule.input_term_idx);
            term_stack.push(rule.result_term_idx);
        }

        while !lift_stack.is_empty() {
            let idx = lift_stack.pop().unwrap();
            if lift_marked[idx] {
                continue;
            }

            lift_marked[idx] = true;
            let lift = &self.lifts[idx];
            if !lift_marked[lift.parent0] {
                lift_stack.push(lift.parent0);
            }
            if !lift_marked[lift.parent1] {
                lift_stack.push(lift.parent1);
            }

            term_stack.push(lift.input_term_idx);
            term_stack.push(lift.result_term_idx);
        }

        while !term_stack.is_empty() {
            let idx = term_stack.pop().unwrap();
            if term_marked[idx] {
                continue;
            }

            term_marked[idx] = true;
            let term = &self.terms[idx];
            if !term_marked[term.left] {
                term_stack.push(term.left);
            }
            if !term_marked[term.right] {
                term_stack.push(term.right);
            }
        }

        let mut new_rules = Vec::new();
        let mut pivote = Vec::new();
        for (i, rule) in self.rules.iter().enumerate() {
            if marked[i] {
                new_rules.push(rule.clone());
            }
            pivote.push(new_rules.len() - 1);
        }
        for i in 0..new_rules.len() {
            new_rules[i].parent0 = pivote[new_rules[i].parent0];
            new_rules[i].parent1 = pivote[new_rules[i].parent1];
        }
        let proving_rule = pivote[self.proving_rule];

        let mut new_lifts = Vec::new();
        let mut pivote = Vec::new();
        for (i, rule) in self.lifts.iter().enumerate() {
            if lift_marked[i] {
                new_lifts.push(rule.clone());
            }
            pivote.push(new_lifts.len() - 1);
        }
        for i in 0..new_lifts.len() {
            new_lifts[i].parent0 = pivote[new_lifts[i].parent0];
            new_lifts[i].parent1 = pivote[new_lifts[i].parent1];
        }
        for i in 0..new_rules.len() {
            new_rules[i].lift_rule = pivote[new_rules[i].lift_rule];
        }

        let mut count = 0;
        let mut lifts = 0;
        let mut markedd = vec![false; new_lifts.len()];
        let mut stack = vec![];
        // analyze: rules with APP_LAM_SUB and parent APP_LAM_SUB
        for i in 0..new_rules.len() {
            let rule1 = &new_rules[i];
            let parent = &new_rules[rule1.parent0];
            let parent1 = &new_rules[rule1.parent1];
            if rule1.rule == RULE_TYPE_IND_REC
                || rule1.rule == RULE_TYPE_IND_CTOR
                || rule1.rule == RULE_TYPE_AX
            {
                count += 1;
                stack.push(rule1.lift_rule);
            }
        }
        while !stack.is_empty() {
            let idx = stack.pop().unwrap();
            markedd[idx] = true;
            let lift = &new_lifts[idx];
            if lift.parent0 != 0 && lift.parent0 != idx {
                stack.push(lift.parent0);
            }
            if lift.parent1 != 0 && lift.parent1 != idx {
                stack.push(lift.parent1);
            }
        }
        eprintln!("COUNT: {}", count);
        eprintln!(
            "LIFT COUNT: {}",
            markedd.iter().map(|b| *b as usize).sum::<usize>()
        );

        eprintln!("Compressed: {} to {}", self.rules.len(), new_rules.len());
        eprintln!("Compressed: {} to {}", self.lifts.len(), new_lifts.len());
        self.rules = new_rules;
        self.lifts = new_lifts;
        self.proving_rule = proving_rule;
    }

    fn serialize_sized(
        &self,
        proof_size: usize,
        num_terms: usize,
        context_size: usize,
        num_lifts: usize,
        num_inds: usize,
        num_pub_terms: usize,
        num_rules: usize,
        num_nnrs: usize,
        num_nrs: usize,
        num_axs: usize,
    ) -> String {
        let mut result = "(set_default_modulus 52435875175126190479447740508185965837690552500527637822603658699938581184513
(let (".to_string();

        let empty_rule = ExpRule::new();
        let empty_lift = ExpLift::lift(0, 0, 0, 0, 0, 0);
        let empty_term = ExpTerm::new(0, 0, 0, 0, 0, 0, 0);
        let empty_node = HashNode::empty();
        let empty_ind = ExpInd::new();

        for i in 0..proof_size {
            let rule = self.rules.get(i).unwrap_or(&empty_rule);
            result += &serialize_field("proof", Some(i), Some("rule"), rule.rule);
            result += &serialize_field("proof", Some(i), Some("ctx_idx"), rule.ctx_idx);
            result += &serialize_field("proof", Some(i), Some("max_binding"), rule.max_binding);
            result += &serialize_field("proof", Some(i), Some("parent0"), rule.parent0);
            result += &serialize_field("proof", Some(i), Some("parent1"), rule.parent1);
            result += &serialize_field("proof", Some(i), Some("parent0_quot"), rule.parent0_quot);
            result += &serialize_field("proof", Some(i), Some("parent1_quot"), rule.parent1_quot);
            result += &serialize_field("proof", Some(i), Some("lift_rule"), rule.lift_rule);
            result += &serialize_field(
                "proof",
                Some(i),
                Some("input_term_idx"),
                rule.input_term_idx,
            );
            result += &serialize_field(
                "proof",
                Some(i),
                Some("result_term_idx"),
                rule.result_term_idx,
            );
            result += &serialize_field("proof", Some(i), Some("extra"), rule.extra);
            result += &serialize_field("proof", Some(i), Some("extra2"), rule.extra2);
            result += &serialize_field("proof", Some(i), Some("extra3"), rule.extra3);
            result += &serialize_field("proof", Some(i), Some("extra4"), rule.extra4);
            result += &serialize_field("proof", Some(i), Some("extra5"), rule.extra5);
            result += &serialize_field("proof", Some(i), Some("extra6"), rule.extra6);
            result += &serialize_field("proof", Some(i), Some("inductive"), rule.inductive);
            result += &serialize_field("proof", Some(i), Some("ind_rule"), rule.ind_rule);
            result += &serialize_field("proof", Some(i), Some("ind_ctor_quot"), rule.ind_ctor_quot);
            result += &serialize_field("proof", Some(i), Some("ind_nnr_quot"), rule.ind_nnr_quot);
            result += &serialize_field("proof", Some(i), Some("ind_nr_quot"), rule.ind_nr_quot);
        }

        for i in 0..num_lifts {
            let lift = self.lifts.get(i).unwrap_or(&empty_lift);
            result += &serialize_field("lifts", Some(i), Some("max_binding"), lift.max_binding);
            result += &serialize_field("lifts", Some(i), Some("parent0"), lift.parent0);
            result += &serialize_field("lifts", Some(i), Some("parent1"), lift.parent1);
            result += &serialize_field(
                "lifts",
                Some(i),
                Some("min_binding_seen"),
                lift.min_binding_seen,
            );
            result += &serialize_field(
                "lifts",
                Some(i),
                Some("input_term_idx"),
                lift.input_term_idx,
            );
            result += &serialize_field(
                "lifts",
                Some(i),
                Some("result_term_idx"),
                lift.result_term_idx,
            );
        }

        for i in 0..num_terms {
            let term = self.terms.get(i).unwrap_or(&empty_term);
            result += &serialize_field("terms", Some(i), Some("kind"), term.kind);
            result += &serialize_field("terms", Some(i), Some("name"), term.name);
            result += &serialize_field("terms", Some(i), Some("left"), term.left);
            result += &serialize_field("terms", Some(i), Some("right"), term.right);
            result += &serialize_field(
                "terms",
                Some(i),
                Some("top_level_func"),
                term.top_level_func,
            );
            result += &serialize_field("terms", Some(i), Some("argc"), term.argc);
            result += &serialize_field("terms", Some(i), Some("ind"), term.ind);
            result += &serialize_field("terms", Some(i), Some("ind_ctor"), term.ind_ctor);
            result += &serialize_field("terms", Some(i), Some("ax"), term.ax);
            result += &serialize_field("terms", Some(i), Some("index"), term.index);
        }

        for i in 0..context_size {
            let node = self.contexts.nodes.get(i).unwrap_or(&empty_node);
            result += &serialize_field("contexts.nodes", Some(i), Some("key"), node.key);
            result += &serialize_field("contexts.nodes", Some(i), Some("value"), node.value);
            result += &serialize_field("contexts.nodes", Some(i), Some("prev"), node.prev);
            // these get set by the compiler...set to 0
            //result += &serialize_field("contexts.nodes", Some(i), Some("hash"), 0);
            result += &format!("(contexts.nodes.{}.empty {})\n", i, node.empty);
        }

        for i in 0..num_rules {
            let node = self.ind_rules.nodes.get(i).unwrap_or(&empty_node);
            result += &serialize_field("rules.nodes", Some(i), Some("key"), node.key);
            result += &serialize_field("rules.nodes", Some(i), Some("value"), node.value);
            result += &serialize_field("rules.nodes", Some(i), Some("prev"), node.prev);
            // these get set by the compiler...set to 0
            //result += &serialize_field("rules.nodes", Some(i), Some("hash"), 0);
            result += &format!("(rules.nodes.{}.empty {})\n", i, node.empty);
        }

        for i in 0..num_nnrs {
            let node = self.ind_nnrs.nodes.get(i).unwrap_or(&empty_node);
            result += &serialize_field("rule_nnrs.nodes", Some(i), Some("key"), node.key);
            result += &serialize_field("rule_nnrs.nodes", Some(i), Some("value"), node.value);
            result += &serialize_field("rule_nnrs.nodes", Some(i), Some("prev"), node.prev);
            // these get set by the compiler...set to 0
            //result += &serialize_field("rule_nnrs.nodes", Some(i), Some("hash"), 0);
            result += &format!("(rule_nnrs.nodes.{}.empty {})\n", i, node.empty);
        }

        for i in 0..num_nrs {
            let node = self.ind_nrs.nodes.get(i).unwrap_or(&empty_node);
            result += &serialize_field("rule_nrs.nodes", Some(i), Some("key"), node.key);
            result += &serialize_field("rule_nrs.nodes", Some(i), Some("value"), node.value);
            result += &serialize_field("rule_nrs.nodes", Some(i), Some("prev"), node.prev);
            // these get set by the compiler...set to 0
            result += &serialize_field("rule_nrs.nodes", Some(i), Some("hash"), 0);
            result += &format!("(rule_nrs.nodes.{}.empty {})\n", i, node.empty);
        }

        for i in 0..num_pub_terms {
            let term = self.public_terms.get(i).unwrap_or(&empty_term);
            result += &serialize_field("public_terms", Some(i), Some("kind"), term.kind);
            result += &serialize_field("public_terms", Some(i), Some("name"), term.name);
            result += &serialize_field("public_terms", Some(i), Some("left"), term.left);
            result += &serialize_field("public_terms", Some(i), Some("right"), term.right);
            result += &serialize_field(
                "public_terms",
                Some(i),
                Some("top_level_func"),
                term.top_level_func,
            );
            result += &serialize_field("public_terms", Some(i), Some("argc"), term.argc);
            result += &serialize_field("public_terms", Some(i), Some("ind"), term.ind);
            result += &serialize_field("public_terms", Some(i), Some("ind_ctor"), term.ind_ctor);
            result += &serialize_field("public_terms", Some(i), Some("ax"), term.ax);
            result += &serialize_field("public_terms", Some(i), Some("index"), term.index);
        }

        for i in 0..num_inds {
            let ind = self.inductives.get(i).unwrap_or(&empty_ind);
            result += &serialize_field("inductives", Some(i), Some("ty"), ind.ty);
            result += &serialize_field("inductives", Some(i), Some("num_params"), ind.num_params);
            result += &serialize_field("inductives", Some(i), Some("rules"), ind.rules);
            result += &serialize_field("inductives", Some(i), Some("rule_nnrs"), ind.rule_nnrs);
            result += &serialize_field("inductives", Some(i), Some("rule_nrs"), ind.rule_nrs);
            result += &serialize_field("inductives", Some(i), Some("num_rules"), ind.num_rules);
            result += &serialize_field("inductives", Some(i), Some("rec_body"), ind.rec_body);
            result += &serialize_field("inductives", Some(i), Some("elim_argc"), ind.elim_argc);
            result += &serialize_field("inductives", Some(i), Some("projector"), ind.projector);
        }

        for i in 0..num_axs {
            let ax = self.axioms.get(i).unwrap_or(&0);
            result += &serialize_field("axioms", Some(i), None, *ax);
        }

        result += &format!("(expected_type #f{})\n", self.expected_type);
        result += &format!("(proving_rule #f{})\n", self.proving_rule);

        result += "(return true)\n";
        result += ") true; ignored\n))";

        return result.to_string();
    }

    pub fn serialize(&self) -> String {
        self.serialize_sized(
            max(self.rules.len(), 1),
            max(self.terms.len(), 1),
            max(self.contexts.nodes.len(), 1),
            max(self.lifts.len(), 1),
            max(self.inductives.len(), 1),
            max(self.public_terms.len(), 1),
            max(self.ind_rules.nodes.len(), 1),
            max(self.ind_nnrs.len(), 1),
            max(self.ind_nrs.len(), 1),
            max(self.axioms.len(), 1),
        )
    }
}
fn serialize_field(name: &str, index: Option<usize>, field: Option<&str>, value: usize) -> String {
    let mut res = "(".to_owned() + name;
    if let Some(i) = index {
        res += &format!(".{}", i);
    }

    if let Some(f) = field {
        res += &format!(".{}", f);
    }

    res += &format!(" #f{})\n", value);
    res
}

/// For now, just takes a single theorem
pub struct Exporter {
    eval: Evaluator,
    zk_input: ZkInput,

    inductives: HashMap<String, Inductive>,

    axioms: Option<HashMap<String, Term>>,
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
    zk_lift_cache: HashMap<ExpLift, usize>,
    // (term, context, max_binding) to rule that evals it
    zk_term_eval_cache: HashMap<(usize, usize, usize), usize>,
    zk_term_ty_cache: HashMap<(usize, usize, usize), usize>,

    zk_term_free_bindings: HashMap<usize, HashSet<usize>>,
}

impl Exporter {
    fn new() -> Exporter {
        Exporter {
            eval: Evaluator::new::<String, _>(&[], HashMap::new()),
            zk_input: ZkInput::new(),

            inductives: HashMap::new(),

            axioms: None,
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
            zk_lift_cache: HashMap::new(),
            zk_term_eval_cache: HashMap::new(),
            zk_term_ty_cache: HashMap::new(),

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
        exp.axioms = Some(axioms);

        for (name, term) in exp.axioms.clone().unwrap() {
            exp.add_axiom_term(name.to_string(), term.clone());
        }

        let term = exp.export_term(expected_type, 0);

        for t in &exp.zk_input.terms {
            exp.zk_input.public_terms.push(t.clone());
        }

        exp.zk_input.expected_type = term;
        exp
    }

    fn add_inductive(&mut self, inductive: &Inductive) {
        let ind_type = self.export_term(inductive.ty.clone(), 0);
        let ind = ExpInd {
            ty: ind_type,
            num_params: inductive.num_params,
            rules: HashList::EMPTY,
            rule_nnrs: HashList::EMPTY,
            rule_nrs: HashList::EMPTY,
            num_rules: inductive.rules.len(),
            rec_body: 0,
            elim_argc: 0,
            projector: 0,
        };
        let ind_idx = self.add_zk_ind(ind);
        self.inductive_mapping
            .insert(inductive.name.clone(), ind_idx);
        self.ind_rev_map.insert(ind_idx, inductive.name.clone());
        let mut rule_list = HashList::EMPTY;
        let mut nnr_list = HashList::EMPTY;
        let mut nr_list = HashList::EMPTY;

        for i in 0..inductive.rules.len() {
            let rule_term = self.export_term(inductive.rules[i].ty.clone(), 0);
            rule_list = self.zk_input.ind_rules.add(rule_list, i, rule_term);
            nnr_list = self.zk_input.ind_nnrs.add(
                nnr_list,
                i,
                inductive.num_nonrecursive_args_for_rule(i) - inductive.num_params,
            );
            nr_list =
                self.zk_input
                    .ind_nrs
                    .add(nr_list, i, inductive.num_recursive_args_for_rule(i));
            //self.zk_input.inductives[ind_idx].rule_nnrs[i] =
            //    inductive.num_nonrecursive_args_for_rule(i) - inductive.num_params;
            //self.zk_input.inductives[ind_idx].rule_nrs[i] =
            //    inductive.num_recursive_args_for_rule(i);

            self.inductive_rule_mapping
                .insert((inductive.name.clone(), inductive.rules[i].name.clone()), i);
        }

        self.zk_input.inductives[ind_idx].rules = rule_list;
        self.zk_input.inductives[ind_idx].rule_nnrs = nnr_list;
        self.zk_input.inductives[ind_idx].rule_nrs = nr_list;

        // TODO:
        let rec_body = &inductive.elim_body;
        // add "bindings" for ind params and motive...
        let rec_zk_body = self.export_term(rec_body.clone(), inductive.num_params + 1);
        let projector = if let Some(t) = &inductive.projector {
            self.export_term(t.clone(), 0)
        } else {
            0
        };
        let mut_zk_ind = self.get_zk_ind_mut(ind_idx);
        mut_zk_ind.rec_body = rec_zk_body;
        mut_zk_ind.elim_argc = rec_body.params().len() + inductive.num_params + 1;
        mut_zk_ind.projector = projector
    }

    // TODO: add exp again
    pub fn simulate(theorem: Theorem) -> Result<(), String> {
        let mut context = Context::new();
        let mut eval = Evaluator::new(&theorem.axioms, theorem.inductives.clone());
        let mut axioms = theorem.axioms;

        let simplified_ty = eval.eval(theorem.ty.clone()).unwrap();
        let mut exporter = Exporter::with_axioms(simplified_ty, axioms, eval.inductives.clone());

        let simplified_val = eval.eval(theorem.val.clone()).unwrap();
        let simplified_ty = eval.eval(theorem.ty.clone()).unwrap();
        let rule = exporter.export_ty_term(simplified_val).unwrap();
        let result_type = exporter.get_zk_rule(rule).result_term_idx;

        if result_type != exporter.zk_input.expected_type {
            let rule = exporter
                .export_unify(rule, exporter.zk_input.expected_type)
                .unwrap();
            exporter.zk_input.proving_rule = rule;
        } else {
            exporter.zk_input.proving_rule = rule;
        }

        exporter.zk_input.compress();

        // remove this later.. check for now...
        sim::simulate(
            exporter.zk_input.clone(),
            true,
            &exporter.axiom_rev_mapping,
            &exporter.ind_rev_map,
        );
        Ok(())
    }

    pub fn export(theorem: Theorem) -> Result<ZkInput, String> {
        let mut context = Context::new();
        let mut eval = Evaluator::new(&theorem.axioms, theorem.inductives.clone());
        let mut axioms = theorem.axioms;

        let simplified_ty = eval.eval(theorem.ty.clone()).unwrap();
        let mut exporter =
            Exporter::with_axioms(simplified_ty.clone(), axioms, eval.inductives.clone());

        let simplified_val = eval.eval(theorem.val.clone()).unwrap();
        let rule = exporter.export_ty_term(simplified_val)?;
        let result_type = exporter.get_zk_rule(rule).result_term_idx;

        if result_type != exporter.zk_input.expected_type {
            let rule = exporter.export_unify(rule, exporter.zk_input.expected_type)?;
            exporter.zk_input.proving_rule = rule;
        } else {
            exporter.zk_input.proving_rule = rule;
        }

        exporter.zk_input.compress();

        //let mut rule_type_counts = HashMap::new();
        //for rule in &exporter.zk_input.rules {
        //    let count = rule_type_counts.get(&rule.rule).unwrap_or(&0);
        //    rule_type_counts.insert(rule.rule, count + 1);
        //}

        //let mut rule_type_counts = rule_type_counts.iter().collect::<Vec<_>>();
        //rule_type_counts.sort_by_key(|a| a.1);
        //for (r, c) in rule_type_counts {
        //    eprintln!("{}: {}", rule_to_string(*r), c);
        //}

        //let mut rule_type_counts = unsafe { LIFT_COUNTS_MAP.iter().collect::<Vec<_>>() };
        //eprintln!("LIFTS");
        //for (r, c) in rule_type_counts {
        //    eprintln!("{}: {}", rule_to_string(*r), c);
        //}

        Ok(exporter.zk_input)
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

    fn argc(&self, input_idx: usize) -> usize {
        let mut res = 0;
        let mut term = self.get_zk_term(input_idx).clone();

        loop {
            match term.kind {
                EXPR_APP => {
                    res += 1;
                    term = self.get_zk_term(term.left).clone();
                }
                _ => {
                    break;
                }
            }
        }

        res
    }

    // try to evaluate the eliminators...
    // any term passed in should already be in normal form...
    //
    // This function first walks the entire tree, looking for eliminators.
    // If it finds one or more, it evaluates it, it resolves the rest of the tree and returns the
    // correct rule.
    //
    // Otherwise, it returns an error.
    fn export_eval_rec(
        &mut self,
        input_idx: usize,
        zk_context: usize,
        context: &mut HashMap<usize, usize>,
        max_binding: usize,
    ) -> Result<usize, String> {
        // if we are applying the recursor, then try to resolve it
        let input = self.get_zk_term(input_idx).clone();
        let input_tlf = self.get_zk_term(input.top_level_func).clone();
        assert!(input_tlf.kind == EXPR_IND_REC);
        let inductive = self.get_zk_ind(input_tlf.ind).clone();
        let num_args = self.argc(input_idx);

        if num_args == inductive.elim_argc {
            let arg = self.get_zk_term(input.right).clone();
            let ind_ctor = self.get_zk_term(arg.top_level_func).clone();
            if !(ind_ctor.kind == EXPR_IND_CTOR && ind_ctor.ind == input_tlf.ind) {
                return Err("Not a ctor!".to_string());
            }
            let get_elim_rule_idx = self
                .export_get_arg(
                    input_idx,
                    num_args - (inductive.num_params + 2 + ind_ctor.ind_ctor),
                )
                .unwrap();
            let elim_term_idx = self.get_zk_rule(get_elim_rule_idx).result_term_idx;

            let (nnrs, nnr_quot) = self
                .zk_input
                .ind_nnrs
                .get(inductive.rule_nnrs, ind_ctor.ind_ctor);
            let (nrs, nr_quot) = self
                .zk_input
                .ind_nrs
                .get(inductive.rule_nrs, ind_ctor.ind_ctor);
            let apply_elim_eval = self
                .export_apply_elim_eval(
                    input.right,
                    zk_context,
                    context,
                    max_binding,
                    input.left,
                    elim_term_idx,
                    nnrs,
                    nrs,
                )
                .unwrap();
            let result = self.get_zk_rule(apply_elim_eval).result_term_idx;

            // TODO: remove ... just for testing
            let f_rule = ExpRule::eval_id(input.left, zk_context, max_binding);
            let e_rule = ExpRule::eval_id(input.right, zk_context, max_binding);

            let f_rule_idx = self.add_zk_rule(f_rule);
            let e_rule_idx = self.add_zk_rule(e_rule);

            let sub1 = ExpRule::eval_ind_sub1(
                input.left,
                elim_term_idx,
                zk_context,
                max_binding,
                input_tlf.ind,
                ind_ctor.ind_ctor,
                0,
                get_elim_rule_idx,
            );
            let sub1_idx = self.add_zk_rule(sub1);

            let sub2 = ExpRule::eval_ind_sub2(
                input.right,
                result,
                zk_context,
                max_binding,
                input_tlf.ind,
                ind_ctor.ind_ctor,
                elim_term_idx,
                input.left,
                0,
                apply_elim_eval,
                nnr_quot,
                nr_quot,
            );
            let sub2_idx = self.add_zk_rule(sub2);

            let rule = ExpRule::eval_ind(
                input_idx,
                result,
                zk_context,
                max_binding,
                input_tlf.ind,
                sub1_idx,
                sub2_idx,
            );

            return Ok(self.add_zk_rule(rule));
        }

        Err("Eval Elim: Not enough args!".to_string())
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
        let apply_elim_rule = self.export_apply_elim(
            input_idx,
            rec_idx,
            elim_idx,
            input_idx,
            nonrec_params,
            rec_params,
            rec_params,
        )?;
        let res = self.get_zk_rule(apply_elim_rule).result_term_idx;
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
        rec_idx: usize,  // recursor
        elim_idx: usize, // the elim we resolve to
        orig_idx: usize,
        nonrec_params: usize,
        rec_params: usize,
        rec_applies: usize,
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
            let parent0_idx = self.export_apply_elim(
                f,
                rec_idx,
                elim_idx,
                orig_idx,
                nonrec_params - 1,
                rec_params,
                0,
            )?;
            let fp = self.get_zk_rule(parent0_idx).result_term_idx;
            let fp_tlf = self.get_zk_term(fp).top_level_func;
            let result_term = ExpTerm::app(fp, e, fp_tlf, self);
            let result_idx = self.add_zk_term(result_term);

            // let parent1_idx =
            //     self.export_eval(app_fp_e_idx, HashList::EMPTY, &mut HashMap::new(), 0);
            //let result_idx = self.get_zk_rule(parent1_idx).result_term_idx;

            // TODO
            let rule = ExpRule::apply_elim(
                input_idx,
                result_idx,
                rec_idx,
                elim_idx,
                HashList::EMPTY,
                nonrec_params,
                rec_params,
                0,
                parent0_idx,
                orig_idx,
            );
            Ok(self.add_zk_rule(rule))

        // elim_apply nnr (nr-1) 0 o e_i rec f => f'
        // ----------------------------------------------    (apply_nr)
        //  elim_apply nnr nr 0 o e_i (f e) => (f' e)
        } else if rec_applies == 0 {
            assert!(input.kind == EXPR_APP);

            assert!(input.kind == EXPR_APP);
            let f = input.left;
            let e = input.right;
            let parent0_idx = self.export_apply_elim(
                f,
                rec_idx,
                elim_idx,
                orig_idx,
                nonrec_params,
                rec_params - 1,
                0,
            )?;
            let fp = self.get_zk_rule(parent0_idx).result_term_idx;
            let fp_tlf = self.get_zk_term(fp).top_level_func;
            let result_term = ExpTerm::app(fp, e, fp_tlf, self);
            let result_idx = self.add_zk_term(result_term);

            // let parent1_idx =
            //     self.export_eval(app_fp_e_idx, HashList::EMPTY, &mut HashMap::new(), 0);
            //let result_idx = self.get_zk_rule(parent1_idx).result_term_idx;

            // TODO
            let rule = ExpRule::apply_elim(
                input_idx,
                result_idx,
                rec_idx,
                elim_idx,
                HashList::EMPTY,
                nonrec_params,
                rec_params,
                0,
                parent0_idx,
                orig_idx,
            );
            Ok(self.add_zk_rule(rule))

            // elim_apply nnr nr 0 o e_i rec o => o'
            // ----------------------------------------------    (apply_rec)
            //  elim_apply nnr nr 1 o e_i (f e) => (o' (rec e))
            //
            // elim_apply nnr nr (recs-1) o e_i rec f => f'
            // ----------------------------------------------    (apply_rec)
            //  elim_apply nnr nr recs o e_i (f e) => (f' (rec e))
        } else {
            assert!(input.kind == EXPR_APP);

            let f = input.left;
            let e = input.right;
            let parent0_idx = if rec_applies == 1 {
                self.export_apply_elim(
                    orig_idx,
                    rec_idx,
                    elim_idx,
                    orig_idx,
                    nonrec_params,
                    rec_params,
                    0,
                )?
            } else {
                self.export_apply_elim(
                    f,
                    rec_idx,
                    elim_idx,
                    orig_idx,
                    nonrec_params,
                    rec_params,
                    rec_applies - 1,
                )?
            };
            let fp = self.get_zk_rule(parent0_idx).result_term_idx;
            let fp_tlf = self.get_zk_term(fp).top_level_func;

            let app_rec_e = ExpTerm::app(rec_idx, e, rec_idx, self);
            let app_rec_e_idx = self.add_zk_term(app_rec_e);

            let app_fp_rec = ExpTerm::app(fp, app_rec_e_idx, fp_tlf, self);
            let result_idx = self.add_zk_term(app_fp_rec);

            // TODO:
            let rule = ExpRule::apply_elim(
                input_idx,
                result_idx,
                rec_idx,
                elim_idx,
                HashList::EMPTY,
                nonrec_params,
                rec_params,
                rec_applies,
                parent0_idx,
                orig_idx,
            );
            Ok(self.add_zk_rule(rule))
        }
    }

    // THIS IS BACKWARDS!!!
    fn export_get_arg(&mut self, input_idx: usize, arg_c: usize) -> Result<usize, String> {
        let input = self.get_zk_term(input_idx).clone();

        assert!(input.kind == EXPR_APP, "GOT: {}", input.kind);

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

    // try to evaluate any recursors in the input. If it succeeds,
    // it will return the rule that does it.
    fn try_unify_recs(
        &mut self,
        input_idx: usize,
        zk_context: usize,
        context: &mut HashMap<usize, usize>,
        max_binding: usize,
    ) -> Result<usize, String> {
        let input = self.get_zk_term(input_idx).clone();
        let tlf = self.get_zk_term(input.top_level_func).clone();
        if tlf.kind == EXPR_IND_REC {
            let res = self.export_eval_rec(input_idx, zk_context, context, max_binding);
            if res.is_ok() {
                let rule = self.get_zk_rule(res.clone().unwrap());
                return res;
            }
        }

        let rule = match input.kind {
            EXPR_LAM | EXPR_PI | EXPR_APP => {
                let left_res = self.try_unify_recs(input.left, zk_context, context, max_binding);
                let right_max_binding = if input.kind != EXPR_APP {
                    max_binding + 1
                } else {
                    max_binding
                };
                let right_res =
                    self.try_unify_recs(input.right, zk_context, context, right_max_binding);

                if left_res.is_err() && right_res.is_err() {
                    return Err(format!("Failed to unify recs"));
                }

                let left_idx = left_res.unwrap_or(self.add_zk_rule(ExpRule::eval_id(
                    input.left,
                    zk_context,
                    max_binding,
                )));
                let right_idx = right_res.unwrap_or(self.add_zk_rule(ExpRule::eval_id(
                    input.right,
                    zk_context,
                    max_binding,
                )));

                let left = self.get_zk_rule(left_idx).clone();
                let right = self.get_zk_rule(right_idx).clone();

                match input.kind {
                    EXPR_LAM | EXPR_PI => {
                        let res = if input.kind == EXPR_PI {
                            ExpTerm::pi(input.name, left.result_term_idx, right.result_term_idx)
                        } else {
                            ExpTerm::lam(input.name, left.result_term_idx, right.result_term_idx)
                        };

                        let res_idx = self.add_zk_term(res);
                        ExpRule::eval_pi(
                            input_idx,
                            res_idx,
                            zk_context,
                            left_idx,
                            HashList::EMPTY,
                            right_idx,
                            HashList::EMPTY,
                            max_binding,
                        )
                    }
                    EXPR_APP => {
                        let tlf = self.get_zk_term(left.result_term_idx).top_level_func;
                        let res =
                            ExpTerm::app(left.result_term_idx, right.result_term_idx, tlf, self);
                        let res_idx = self.add_zk_term(res);
                        ExpRule::eval_app(
                            input_idx,
                            res_idx,
                            zk_context,
                            left_idx,
                            HashList::EMPTY,
                            right_idx,
                            HashList::EMPTY,
                            max_binding,
                        )
                    }
                    _ => panic!("OOF"),
                }
            }
            EXPR_PROJ => {
                let rule = self.try_unify_recs(input.left, zk_context, context, max_binding);
                if rule.is_err() {
                    return Err(format!("Failed to unify recs"));
                }
                let rule = rule.unwrap();
                let rule_rule = self.get_zk_rule(rule).clone();

                let res = ExpTerm::proj(input.index, rule_rule.result_term_idx);
                let res_idx = self.add_zk_term(res);
                ExpRule::eval_proj_simpl(
                    input_idx,
                    res_idx,
                    zk_context,
                    rule,
                    HashList::EMPTY,
                    max_binding,
                )
            }
            _ => {
                return Err("Failed to unify recs".to_string());
            }
        };
        Ok(self.add_zk_rule(rule))
    }

    fn export_unify_helper(
        &mut self,
        result_type: usize,
        expected_type: usize,
        zk_context: usize,
        context: &mut HashMap<usize, usize>,
        max_binding: usize,
    ) -> Result<usize, String> {
        // TODO: carry around a typing context... this will be better...
        // TODO: can we perform eval with the expected type already known?
        //        could be much better...
        let result = self.get_zk_term(result_type).clone();
        let expected = self.get_zk_term(expected_type).clone();

        let result_tlf = self.get_zk_term(result.top_level_func);

        if result_type == expected_type {
            let rule = ExpRule::eval_id(result_type, zk_context, max_binding);
            return Ok(self.add_zk_rule(rule));
        }

        // eta expansion on result
        let exp_body = self.get_zk_term(expected.right).clone();
        let exp_body_right = self.get_zk_term(exp_body.right).clone();
        let test = self.export_lift(exp_body.left, max_binding, ExpTerm::MAX_BINDING, 50);
        let test_res = self.get_zk_lift(test).clone();
        if expected.kind == EXPR_LAM
            && exp_body.kind == EXPR_APP
            && test_res.result_term_idx == expected_type
            && exp_body_right.kind == EXPR_VAR
            && exp_body_right.name == expected.name
        {
            panic!("eta unsupported");
            // TODO:
            //let eval_exp = ExpRule::eval_id(expected_type, zk_context, max_binding);
            //let eval_exp_idx = self.add_zk_rule(eval_exp);

            //let sub2 = ExpRule::eval_eta_sub2(result_type,
        }

        // eta expansion on result
        let res_body = self.get_zk_term(result.right).clone();
        let res_body_right = self.get_zk_term(res_body.right).clone();
        let test = self.export_lift(res_body.left, max_binding, ExpTerm::MAX_BINDING, 50);
        let test_res = self.get_zk_lift(test).clone();
        if result.kind == EXPR_LAM
            && res_body.kind == EXPR_APP
            && test_res.result_term_idx == expected_type
            && res_body_right.kind == EXPR_VAR
            && res_body_right.name == result.name
        {
            //let lifted_rule = self.export_lift(*result_idx, max_binding, ExpTerm::MAX_BINDING);
            // TODO:
            panic!("eta unsupported");
            //let eval_exp = ExpRule::eval_id(expected_type, zk_context, max_binding);
            //let eval_exp_idx = self.add_zk_rule(eval_exp);

            //let sub2 = ExpRule::eval_eta_sub2(result_type,
        }

        let rule = match (result.kind, expected.kind) {
            (EXPR_PI, EXPR_PI) | (EXPR_LAM, EXPR_LAM) => {
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
                    let rule = ExpRule::eval_id(res_bod, zk_context, max_binding + 1);
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
            (EXPR_APP, EXPR_APP) => {
                let res_f = result.left;
                let exp_f = expected.left;
                //let (f_subs, f_quot) = self.split_zk_context(zk_context, res_f);

                let res_e = result.right;
                let exp_e = expected.right;
                //let (e_subs, e_quot) = self.split_zk_context(zk_context, res_e);
                //
                // if one is an App(Lam()) or App(Pi()) and other isn't, need to evaluate...
                let res_f_term = self.get_zk_term(res_f);
                let exp_f_term = self.get_zk_term(exp_f);

                if res_f_term.kind == EXPR_LAM && exp_f_term.kind != EXPR_LAM {
                    let eval_rule = self.export_eval(
                        result_type,
                        HashList::EMPTY,
                        &mut HashMap::new(),
                        max_binding,
                    );
                    let eval_rule_s = self.get_zk_rule(eval_rule).clone();
                    let unify_rule = self.export_unify_helper(
                        eval_rule_s.result_term_idx,
                        expected_type,
                        zk_context,
                        context,
                        max_binding,
                    )?;
                    let unify_rule_s = self.get_zk_rule(unify_rule).clone();
                    ExpRule::eval_transitive(
                        result_type,
                        unify_rule_s.result_term_idx,
                        zk_context,
                        max_binding,
                        eval_rule,
                        unify_rule,
                    )
                } else if exp_f_term.kind == EXPR_LAM && res_f_term.kind != EXPR_LAM {
                    // TODO: this may be wrong...
                    let eval_rule = self.export_eval(
                        expected_type,
                        HashList::EMPTY,
                        &mut HashMap::new(),
                        max_binding,
                    );
                    let eval_rule_s = self.get_zk_rule(eval_rule).clone();
                    let unify_rule = self.export_unify_helper(
                        result_type,
                        eval_rule_s.result_term_idx,
                        zk_context,
                        context,
                        max_binding,
                    )?;
                    let unify_rule_s = self.get_zk_rule(unify_rule).clone();
                    ExpRule::eval_transitive(
                        result_type,
                        unify_rule_s.result_term_idx,
                        zk_context,
                        max_binding,
                        unify_rule,
                        eval_rule,
                    )
                } else {
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
            }
            _ => {
                // attempt proof_irrel unification
                let res_ty_rule = self.export_ty(result_type, zk_context, context, max_binding)?;
                let exp_ty_rule =
                    self.export_ty(expected_type, zk_context, context, max_binding)?;
                let res_ty_idx = self.get_zk_rule(res_ty_rule).result_term_idx;
                let exp_ty_idx = self.get_zk_rule(exp_ty_rule).result_term_idx;

                let ty_ty_rule = self.export_ty(res_ty_idx, zk_context, context, max_binding)?;
                let ty_ty_idx = self.get_zk_rule(ty_ty_rule).result_term_idx;
                let ty_ty_term = self.get_zk_term(ty_ty_idx);

                if res_ty_idx == exp_ty_idx && ty_ty_term.kind == EXPR_SORT && ty_ty_term.name == 0
                {
                    let sub1 = ExpRule::proof_irrel_sub1(
                        expected_type,
                        ty_ty_idx,
                        zk_context,
                        max_binding,
                        exp_ty_rule,
                        ty_ty_rule,
                        res_ty_idx,
                    );
                    let sub1_idx = self.add_zk_rule(sub1);
                    ExpRule::proof_irrel(
                        result_type,
                        expected_type,
                        zk_context,
                        max_binding,
                        res_ty_rule,
                        sub1_idx,
                    )
                } else {
                    //ExpRule::proof_irrel(
                    //    result_type,
                    //    expected_type,
                    //    zk_context,
                    //    max_binding,
                    //    res_ty_rule,
                    //    0,
                    //)
                    //'

                    return Err("oof".to_string());
                }
            }
        };

        Ok(self.add_zk_rule(rule))
    }

    fn add_axiom_term(&mut self, name: String, term: Term) {
        let term = self.export_term(term, 0);

        if !self.axiom_mapping.contains_key(&name) {
            self.zk_input.axioms.push(term);
            let ax_num = self.zk_input.axioms.len() - 1;
            self.axiom_mapping.insert(name.clone(), (ax_num, 0));
            self.axiom_rev_mapping.insert((ax_num, 0), name);
            self.ax_test.insert(ax_num, 0);
        }
    }

    pub fn export_eval_term(&mut self, input: Term) -> usize {
        let term = self.export_term(input, 0);
        self.export_eval(term, HashList::EMPTY, &mut HashMap::new(), 0)
    }

    pub fn export_ty_term(&mut self, input: Term) -> Result<usize, String> {
        let term = self.export_term(input, 0);
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
        if let Some(rule) = self
            .zk_term_eval_cache
            .get(&(input_idx, zk_context, max_binding))
        {
            return *rule;
        }
        //let input_idx = self.add_zk_term(input.clone());
        //
        let input = self.get_zk_term(input_idx).clone();
        //let (subset_ctx, quotient_ctx) = self.(input_idx, zk_context);

        // TODO: use eval function ... but not today
        //let result = self.eval.eval_with_context(input.clone(), &mut context

        let zk_rule = match input.kind {
            // TODO: make sure that we use levels in the circuit, but indicies out here...
            EXPR_VAR => {
                // lift here...
                let level = input.name;
                if let Some(result_idx) = context.get(&level) {
                    let lifted_rule = self.export_lift(
                        *result_idx,
                        max_binding,
                        ExpTerm::MAX_BINDING,
                        RULE_EVAL_VAR,
                    );
                    let lifted_idx = self.get_zk_lift(lifted_rule).result_term_idx;
                    let ctx_rem =
                        self.zk_input
                            .contexts
                            .remove(zk_context, input.name, *result_idx);
                    let ctx = self
                        .zk_input
                        .contexts
                        .add(HashList::EMPTY, input.name, *result_idx);
                    ExpRule::eval_var(input_idx, lifted_idx, ctx, max_binding, lifted_rule)
                } else {
                    ExpRule::eval_id(input_idx, zk_context, max_binding)
                }
            }
            EXPR_SORT => ExpRule::eval_id(input_idx, zk_context, max_binding),
            EXPR_APP => {
                let f = input.left;
                let e = input.right;

                let (f_subs, f_quot) = self.split_zk_context(zk_context, f, context);
                let f_rule = self.export_eval(f, f_subs, context, max_binding);

                let (e_subs, e_quot) = self.split_zk_context(zk_context, e, context);
                let e_rule = self.export_eval(e, e_subs, context, max_binding);

                let f_result = self.zk_input.rules[f_rule].result_term_idx;
                let e_result = self.zk_input.rules[e_rule].result_term_idx;

                let f_term = self.get_zk_term(f_result);
                // HUGE TODO: eval app pi
                if f_term.kind == EXPR_LAM || f_term.kind == EXPR_PI {
                    let name = f_term.name;
                    assert!(name == max_binding);
                    let body = f_term.right;
                    context.insert(name, e_result);
                    let inserted_ctx = self.zk_context_insert(zk_context, name, e_result);
                    let (new_context, new_context_quot) =
                        self.split_zk_context(inserted_ctx, body, context);
                    let value_rule = self.export_eval(body, new_context, context, max_binding + 1);
                    //let value_idx = self.export_eval(
                    context.remove(&name);

                    let value_idx = self.get_zk_rule(value_rule).result_term_idx;

                    let lift_rule = self.export_lift(
                        value_idx,
                        max_binding,
                        ExpTerm::MAX_BINDING,
                        RULE_EVAL_APP_LAM,
                    );
                    let zk_result_idx = self.get_zk_lift(lift_rule).result_term_idx;

                    let eval_app_p1 = ExpRule::eval_app_lam_p1(
                        body,
                        zk_result_idx,
                        zk_context,
                        e_rule,
                        e_quot,
                        value_rule,
                        new_context_quot,
                        lift_rule,
                        max_binding,
                        e,
                    );
                    let eval_app_p1_idx = self.add_zk_rule(eval_app_p1);

                    ExpRule::eval_app_lam_p2(
                        input_idx,
                        zk_result_idx,
                        zk_context,
                        f_rule,
                        f_quot,
                        eval_app_p1_idx,
                        max_binding,
                    )
                } else {
                    let e_term = self.get_zk_term(e_result);
                    //let min_binding = min(f_term.min_binding, e_term.min_binding);
                    let zk_result = ExpTerm::app(f_result, e_result, f_term.top_level_func, self);
                    let result_idx = self.add_zk_term(zk_result);

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
            EXPR_PI | EXPR_LAM => {
                let name = input.name;
                assert!(name == max_binding);
                let domain = input.left;
                let body = input.right;

                let (domain_subs, domain_quot) = self.split_zk_context(zk_context, domain, context);
                let domain_rule = self.export_eval(domain, domain_subs, context, max_binding);
                let domain_result = self.get_zk_rule(domain_rule).result_term_idx;

                let (body_subs, body_quot) = self.split_zk_context(zk_context, body, context);
                let body_rule = self.export_eval(body, body_subs, context, max_binding + 1);
                let body_result = self.get_zk_rule(body_rule).result_term_idx;

                let zk_result = if input.kind == EXPR_PI {
                    ExpTerm::pi(name, domain_result, body_result)
                } else {
                    ExpTerm::lam(name, domain_result, body_result)
                };
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
            EXPR_PROJ => {
                let (expr_subs, expr_quot) = self.split_zk_context(zk_context, input.left, context);
                let expr_eval = self.export_eval(input.left, expr_subs, context, max_binding);

                let expr_eval_rule = self.get_zk_rule(expr_eval).clone();
                let expr_eval_term = self.get_zk_term(expr_eval_rule.result_term_idx).clone();
                let expr_eval_term_tlf = self.get_zk_term(expr_eval_term.top_level_func).clone();
                let inductive = self.get_zk_ind(expr_eval_term_tlf.ind).clone();

                // if the result ins't an app of IndCtor with args, then we just return an ID node
                if expr_eval_term.kind != EXPR_APP
                    || !(expr_eval_term_tlf.kind == EXPR_IND_CTOR
                        || expr_eval_term_tlf.kind == EXPR_PROJ_PLACEHOLDER)
                {
                    if expr_eval_rule.result_term_idx == input.left {
                        ExpRule::eval_id(input_idx, zk_context, max_binding)
                    } else {
                        let term = ExpTerm::proj(input.index, expr_eval_rule.result_term_idx);
                        let term_idx = self.add_zk_term(term);
                        ExpRule::eval_proj_simpl(
                            input_idx,
                            term_idx,
                            zk_context,
                            expr_eval,
                            expr_quot,
                            max_binding,
                        )
                    }
                } else {
                    //  e => e'   e' is Ind_ctor    get_arg(e', n + ind.) = a
                    // ----------------------------------------------
                    //     proj n e => a
                    let get_arg = self
                        .export_get_arg(expr_eval_rule.result_term_idx, input.index)
                        .unwrap();
                    let get_arg_rule = self.get_zk_rule(get_arg);
                    ExpRule::eval_proj(
                        input_idx,
                        get_arg_rule.result_term_idx,
                        zk_context,
                        expr_eval,
                        expr_quot,
                        get_arg,
                        expr_eval_term_tlf.ind,
                        max_binding,
                    )
                }
            }
            EXPR_AXIOM => ExpRule::eval_id(input_idx, zk_context, max_binding),
            _ => {
                unimplemented!()
            }
        };

        let res = self.add_zk_rule(zk_rule);
        self.zk_term_eval_cache
            .insert((input_idx, zk_context, max_binding), res);
        return res;
    }

    pub fn export_ty(
        &mut self,
        input_idx: usize,
        zk_context: usize,
        context: &mut HashMap<usize, usize>,
        max_binding: usize,
        //expected_idx: usize,
    ) -> Result<usize, String> {
        if let Some(rule) = self
            .zk_term_ty_cache
            .get(&(input_idx, zk_context, max_binding))
        {
            return Ok(*rule);
        }
        let input = self.get_zk_term(input_idx).clone();
        //let expected = self.get_zk_term(expected_idx).clone();

        let zk_rule = match input.kind {
            // TODO: make sure that we use levels in the circuit, but indicies out here...
            EXPR_VAR => {
                let level = input.name;
                // we look up the index in the zk_context...
                if let Some(result_idx) = context.get(&level) {
                    let lifted_rule = self.export_lift(
                        *result_idx,
                        max_binding,
                        ExpTerm::MAX_BINDING,
                        RULE_TYPE_VAR,
                    );
                    let lifted_idx = self.get_zk_lift(lifted_rule).result_term_idx;

                    let ctx_rem =
                        self.zk_input
                            .contexts
                            .remove(zk_context, input.name, *result_idx);
                    let ctx = self
                        .zk_input
                        .contexts
                        .add(HashList::EMPTY, input.name, *result_idx);
                    ExpRule::ty_var(input_idx, lifted_idx, ctx, max_binding, lifted_rule)
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

                let (f_subs, f_quot) = self.split_zk_context(zk_context, f, context);
                let mut f_rule = self.export_ty(f, f_subs, context, max_binding)?;
                let mut f_result = self.get_zk_rule(f_rule).result_term_idx;
                let (e_subs, e_quot) = self.split_zk_context(zk_context, e, context);
                let mut e_rule = self.export_ty(e, e_subs, context, max_binding)?;
                let mut e_result = self.get_zk_rule(e_rule).result_term_idx;

                let mut f_ty = self.get_zk_term(f_result).clone();

                // this probably means we need to resolve a rec.....................
                // ultimate sadness
                while f_ty.kind != EXPR_PI {
                    // try to evaluate the recursors fully
                    // Just do domain for now
                    let rule_idx = self.try_unify_recs(
                        f_result,
                        HashList::EMPTY,
                        &mut HashMap::new(),
                        max_binding,
                    );
                    let new_result = self.get_zk_rule(rule_idx.clone().unwrap()).result_term_idx;
                    let f_rule_new = ExpRule::eval_ty(
                        f,
                        new_result,
                        zk_context,
                        max_binding,
                        f_rule,
                        rule_idx.clone().unwrap(),
                    );
                    f_rule = self.add_zk_rule(f_rule_new);
                    f_result = new_result;
                    f_ty = self.get_zk_term(new_result).clone()
                }

                // try to evaluate the func type
                let eval_f_ty =
                    self.export_eval(f_result, HashList::EMPTY, &mut HashMap::new(), max_binding);
                let eval_f_ty_rule = self.get_zk_rule(eval_f_ty).clone();
                let f_rule_new = ExpRule::eval_ty(
                    f,
                    eval_f_ty_rule.result_term_idx,
                    f_subs,
                    max_binding,
                    f_rule,
                    eval_f_ty,
                );
                f_rule = self.add_zk_rule(f_rule_new);
                f_result = eval_f_ty_rule.result_term_idx;
                f_ty = self.get_zk_term(f_result).clone();

                //assert!(f_ty.kind == EXPR_PI);
                let name = f_ty.name;
                let mut domain_ty = f_ty.left;
                let body_ty = f_ty.right;

                // if the types aren't equal...attempt to unify
                while domain_ty != e_result {
                    // fast case ... try to unify first
                    if let Ok(eval_rule) = self.export_unify_helper(
                        e_result,
                        domain_ty,
                        zk_context,
                        context,
                        max_binding,
                    ) {
                        let ty_rule =
                            ExpRule::eval_ty(e, domain_ty, e_subs, max_binding, e_rule, eval_rule);

                        e_rule = self.add_zk_rule(ty_rule);
                        break;
                    } else {
                        // try to evaluate the recursors fully
                        // Just do domain for now
                        let rule_idx = self.try_unify_recs(
                            domain_ty,
                            HashList::EMPTY,
                            &mut HashMap::new(),
                            max_binding,
                        );
                        if rule_idx.is_ok() {
                            let rule = self.get_zk_rule(rule_idx.clone().unwrap()).clone();
                            let final_eval = self.export_eval(
                                rule.result_term_idx,
                                HashList::EMPTY,
                                &mut HashMap::new(),
                                max_binding,
                            );

                            // need a rule to link rule_idx and final_eval.......
                            let final_eval_rule = self.get_zk_rule(final_eval).clone();
                            if e_result != final_eval_rule.result_term_idx {
                                if let Ok(eval_rule) = self.export_unify_helper(
                                    e_result,
                                    final_eval_rule.result_term_idx,
                                    zk_context,
                                    context,
                                    max_binding,
                                ) {
                                    let ty_rule = ExpRule::eval_ty(
                                        e,
                                        final_eval_rule.result_term_idx,
                                        e_subs,
                                        max_binding,
                                        e_rule,
                                        eval_rule,
                                    );
                                    e_result = final_eval_rule.result_term_idx;
                                    e_rule = self.add_zk_rule(ty_rule);
                                }
                            }
                            //if final_eval_rule.result_term_idx != e_result {
                            //    // TODO: fail case
                            //    panic!();
                            //}
                            let linking_eval = ExpRule::eval_transitive(
                                domain_ty,
                                final_eval_rule.result_term_idx,
                                HashList::EMPTY,
                                max_binding,
                                rule_idx.unwrap(),
                                final_eval,
                            );
                            let linking_eval_idx = self.add_zk_rule(linking_eval);

                            let body_rule =
                                ExpRule::eval_id(f_ty.right, HashList::EMPTY, max_binding);
                            let body_rule_idx = self.add_zk_rule(body_rule);
                            let f_ty_new =
                                ExpTerm::pi(f_ty.name, final_eval_rule.result_term_idx, f_ty.right);
                            let f_ty_new_idx = self.add_zk_term(f_ty_new);
                            let f_eval = ExpRule::eval_pi(
                                f_result,
                                f_ty_new_idx,
                                HashList::EMPTY,
                                linking_eval_idx,
                                HashList::EMPTY,
                                body_rule_idx,
                                HashList::EMPTY,
                                max_binding,
                            );
                            let f_eval_idx = self.add_zk_rule(f_eval.clone());
                            let f_ty_new_rule = ExpRule::eval_ty(
                                f,
                                f_ty_new_idx,
                                f_subs,
                                max_binding,
                                f_rule,
                                f_eval_idx,
                            );
                            f_result = f_ty_new_idx;
                            f_rule = self.add_zk_rule(f_ty_new_rule);
                            domain_ty = final_eval_rule.result_term_idx;
                        } else {
                            let eval_e_idx = self.export_eval(
                                e,
                                HashList::EMPTY,
                                &mut HashMap::new(),
                                max_binding,
                            );
                            let eval_e = self.get_zk_rule(eval_e_idx).clone();
                            // try to evaluate the recursors fully
                            // Just do domain for now
                            let rule_idx = self.try_unify_recs(
                                eval_e.result_term_idx,
                                HashList::EMPTY,
                                &mut HashMap::new(),
                                max_binding,
                            );
                            if rule_idx.is_ok() {
                                let rule_idx = rule_idx.clone().unwrap();
                                let rule = self.get_zk_rule(rule_idx).clone();
                            }

                            // evall...
                            let eval_erule_idx = self.export_eval(
                                e_result,
                                HashList::EMPTY,
                                &mut HashMap::new(),
                                max_binding,
                            );
                            let eval_e_rule = self.get_zk_rule(eval_erule_idx).clone();
                            let e_rule_ty = ExpRule::eval_ty(
                                e,
                                eval_e_rule.result_term_idx,
                                HashList::EMPTY,
                                max_binding,
                                e_rule,
                                eval_erule_idx,
                            );
                            e_rule = self.add_zk_rule(e_rule_ty);
                            e_result = eval_e_rule.result_term_idx;

                            let mut curr_e_res = e_result;
                            let mut curr_e_rule = e_rule;
                            loop {
                                let rule_idx = self.try_unify_recs(
                                    curr_e_res,
                                    HashList::EMPTY,
                                    &mut HashMap::new(),
                                    max_binding,
                                );
                                if rule_idx.is_ok() {
                                    let rule_idx = rule_idx.clone().unwrap();
                                    let rule = self.get_zk_rule(rule_idx).clone();
                                    curr_e_res = rule.result_term_idx;
                                    //let unify_rule_idx = rule_idx.clone().unwrap();
                                    //let unify_rule = self.get_zk_rule(unify_rule_idx).clone();

                                    //let eval_erule_idx = self.export_eval(
                                    //    unify_rule.result_term_idx,
                                    //    HashList::EMPTY,
                                    //    &mut HashMap::new(),
                                    //    max_binding,
                                    //);
                                    //let eval_erule = self.get_zk_rule(eval_erule_idx);

                                    //let rule = ExpRule::eval_transitive(
                                    //    curr_e_res,
                                    //    eval_erule.result_term_idx,
                                    //    HashList::EMPTY,
                                    //    max_binding,
                                    //    unify_rule_idx,
                                    //    eval_erule_idx,
                                    //);
                                    //let rule_idx = self.add_zk_rule(rule.clone());

                                    //let curr_e_res = rule.result_term_idx;
                                    let e_rule_new = ExpRule::eval_ty(
                                        e,
                                        rule.result_term_idx,
                                        HashList::EMPTY,
                                        max_binding,
                                        e_rule,
                                        rule_idx,
                                    );
                                    e_rule = self.add_zk_rule(e_rule_new);
                                    if let Ok(eval_rule) = self.export_unify_helper(
                                        curr_e_res,
                                        domain_ty,
                                        zk_context,
                                        context,
                                        max_binding,
                                    ) {
                                        let ty_rule = ExpRule::eval_ty(
                                            e,
                                            domain_ty,
                                            e_subs,
                                            max_binding,
                                            e_rule,
                                            eval_rule,
                                        );

                                        e_rule = self.add_zk_rule(ty_rule);
                                        e_result = domain_ty;
                                        break;
                                    }
                                } else {
                                    if domain_ty == e_result {
                                        break;
                                    }
                                    println!(
                                        "TEST1 : {:?}\nTEST2 : {:?}\n",
                                        &self.zk_input.terms[domain_ty].left,
                                        &self.zk_input.terms[e_result].left,
                                    );

                                    println!(
                                        "Expected: {} (idx: {})\n\nGot: {} (idx: {})\n\nCURR E RES: {}\n\nE: {}",
                                        term_to_string(
                                            domain_ty,
                                            &self.zk_input.terms,
                                            &self.axiom_rev_mapping,
                                            &self.ind_rev_map
                                        ),
                                        domain_ty,
                                        term_to_string(
                                            e_result,
                                            &self.zk_input.terms,
                                            &self.axiom_rev_mapping,
                                            &self.ind_rev_map
                                        ),
                                        e_result,
                                        term_to_string(
                                            curr_e_res,
                                            &self.zk_input.terms,
                                            &self.axiom_rev_mapping,
                                            &self.ind_rev_map
                                        ),
                                        term_to_string(
                                            e,
                                            &self.zk_input.terms,
                                            &self.axiom_rev_mapping,
                                            &self.ind_rev_map
                                        ),
                                    );
                                    return Err(format!("Typing error:"));
                                }
                            }
                        }
                    }
                }

                let mut eval_context = HashMap::new();
                eval_context.insert(name, e);
                let eval_zk_context = self.zk_context_insert(HashList::EMPTY, name, e);
                let (body_subs, body_quot) =
                    self.split_zk_context(eval_zk_context, body_ty, &mut eval_context);

                let body_rule =
                    self.export_eval(body_ty, body_subs, &mut eval_context, max_binding + 1);
                let body_result = self.get_zk_rule(body_rule).result_term_idx;

                let unlift_rule = self.export_lift(
                    body_result,
                    max_binding,
                    ExpTerm::MAX_BINDING,
                    RULE_TYPE_APP,
                );
                let unlift_result = self.get_zk_lift(unlift_rule).result_term_idx;

                let ty_app_sub = ExpRule::ty_app_sub(
                    f_result,
                    body_result,
                    zk_context,
                    e_rule,
                    e_quot,
                    body_rule,
                    body_quot,
                    max_binding,
                    e,
                );
                let ty_app_sub_idx = self.add_zk_rule(ty_app_sub);

                ExpRule::ty_app(
                    input_idx,
                    unlift_result,
                    zk_context,
                    f_rule,
                    f_quot,
                    ty_app_sub_idx,
                    HashList::EMPTY,
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

                let sub = ExpRule::ty_pi_sub(
                    domain,
                    domain_result,
                    zk_context,
                    domain_eval_rule,
                    zk_context,
                    domain_ty_rule,
                    domain_quot,
                    max_binding,
                    domain_eval_result,
                );
                let sub_idx = self.add_zk_rule(sub);

                //assert!(result_idx == expected_idx);
                ExpRule::ty_pi(
                    input_idx,
                    result_idx,
                    zk_context,
                    sub_idx,
                    HashList::EMPTY,
                    body_ty_rule,
                    body_quot,
                    max_binding,
                )
            }
            EXPR_AX => {
                let term = self.zk_input.axioms[input.ax];
                let lift_rule =
                    self.export_lift(term, max_binding, ExpTerm::MAX_BINDING, RULE_TYPE_AX);
                let lift_res = self.get_zk_lift(lift_rule).result_term_idx;

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
                let ind = self.get_zk_ind(input.ind).clone();
                let lift_rule =
                    self.export_lift(ind.ty, max_binding, ExpTerm::MAX_BINDING, RULE_TYPE_IND);
                let lift_res = self.get_zk_lift(lift_rule).result_term_idx;

                ExpRule::ty_ind(input_idx, lift_res, max_binding, lift_rule)
            }
            EXPR_IND_CTOR => {
                let ind = self.get_zk_ind(input.ind).clone();
                let (rule_ty, quot) = self.zk_input.ind_rules.get(ind.rules, input.ind_ctor);
                //let rule_ty = ind.rules
                //ind.rules[input.ind_ctor];
                let lift_rule = self.export_lift(
                    rule_ty,
                    max_binding,
                    ExpTerm::MAX_BINDING,
                    RULE_TYPE_IND_CTOR,
                );
                let lift_res = self.get_zk_lift(lift_rule).result_term_idx;

                ExpRule::ty_ind_ctor(input_idx, lift_res, max_binding, lift_rule, quot)
            }
            EXPR_IND_REC => {
                let zk_ind = self.get_zk_ind(input.ind).clone();
                let motive_sort = input.ind_ctor;

                let ind_name = self.ind_rev_map.get(&input.ind).unwrap();
                let ind = self.inductives.get(ind_name).unwrap().clone();

                let num_type_params = ind.num_params;

                let motive_term = ind.generate_motive(motive_sort);
                let motive_zk_term = self.export_term(motive_term, num_type_params);
                let rec_body = zk_ind.rec_body;

                // TODO: check name
                let mut rec_term = ExpTerm::pi(num_type_params, motive_zk_term, rec_body);
                let mut rec_idx = self.add_zk_term(rec_term);

                for (i, ty) in ind.ty.params()[..num_type_params].iter().enumerate().rev() {
                    let ty_idx = self.export_term(ty.clone(), i);
                    rec_term = ExpTerm::pi(i, ty_idx, rec_idx);
                    rec_idx = self.add_zk_term(rec_term);
                }

                let ind_ty_idx = self.export_term(ind.ty, 0);

                let pref_rule =
                    self.export_ind_pref(rec_idx, ind_ty_idx, num_type_params, rec_body)?;

                // create lift rule
                let lift_rule = self.export_lift(
                    rec_idx,
                    max_binding,
                    ExpTerm::MAX_BINDING,
                    RULE_TYPE_IND_REC,
                );
                let lift_res = self.get_zk_lift(lift_rule).result_term_idx;

                // TODO: fix...
                ExpRule::ty_ind_rec(input_idx, lift_res, max_binding, pref_rule, lift_rule)
            }
            EXPR_PROJ => {
                let parent0 = self.export_constr_proj(input.left, zk_context, context, max_binding);
                let parent0_rule = self.get_zk_rule(parent0);
                let parent1_input = ExpTerm::proj(input.index, parent0_rule.result_term_idx);
                let parent1_input_idx = self.add_zk_term(parent1_input);
                let parent1 = self.export_eval(
                    parent1_input_idx,
                    HashList::EMPTY,
                    &mut HashMap::new(),
                    max_binding,
                );
                let parent1_rule = self.get_zk_rule(parent1);

                ExpRule::ty_proj(
                    input_idx,
                    parent1_rule.result_term_idx,
                    zk_context,
                    parent0,
                    parent1,
                    max_binding,
                )
            }
            EXPR_PROJ_PLACEHOLDER => {
                assert!(false);
                unimplemented!();
            }
            _ => {
                unimplemented!()
            }
        };
        let res = self.add_zk_rule(zk_rule);
        self.zk_term_ty_cache
            .insert((input_idx, zk_context, max_binding), res);
        Ok(res)
    }

    fn export_walk_proj(
        &mut self,
        input_idx: usize,
        inductive_idx: usize,
        max_binding: usize,
    ) -> usize {
        let input_term = self.get_zk_term(input_idx).clone();
        let inductive = self.get_zk_ind(inductive_idx).clone();

        if input_term.kind == EXPR_APP {
            let parent0 = self.export_walk_proj(input_term.left, inductive_idx, max_binding);
            let parent0_rule = self.get_zk_rule(parent0);
            let app_term = ExpTerm::app(
                parent0_rule.result_term_idx,
                input_term.right,
                inductive.projector,
                self,
            );
            let app_idx = self.add_zk_term(app_term);
            let rule =
                ExpRule::walk_proj(input_idx, app_idx, parent0, inductive_idx, 0, max_binding);
            self.add_zk_rule(rule)
        } else if input_term.kind == EXPR_IND {
            let lift = self.export_lift(
                inductive.projector,
                max_binding,
                ExpTerm::MAX_BINDING,
                RULE_WALK_PROJ,
            );
            let lift_rule = self.get_zk_lift(lift);
            let rule = ExpRule::walk_proj(
                input_idx,
                lift_rule.result_term_idx,
                0,
                inductive_idx,
                lift,
                max_binding,
            );
            self.add_zk_rule(rule)
        } else {
            panic!("Export Walk proj reached non-inductive type...");
        }
    }

    fn export_constr_proj(
        &mut self,
        input_idx: usize,
        zk_context: usize,
        context: &mut HashMap<usize, usize>,
        max_binding: usize,
    ) -> usize {
        let (subs, quot) = self.split_zk_context(zk_context, input_idx, context);
        let parent0 = self
            .export_ty(input_idx, subs, context, max_binding)
            .unwrap();
        let parent0_rule = self.get_zk_rule(parent0);
        let parent0_result = self.get_zk_term(parent0_rule.result_term_idx);

        let parent0_tlf = self.get_zk_term(parent0_result.top_level_func);
        assert!(parent0_tlf.kind == EXPR_IND, "GOT: {}", parent0_tlf.kind);
        assert!(parent0_tlf.kind == EXPR_IND);
        let inductive = parent0_tlf.ind;
        let parent1 = self.export_walk_proj(parent0_rule.result_term_idx, inductive, max_binding);
        let parent1_rule = self.get_zk_rule(parent1);

        let result_term = ExpTerm::app(parent1_rule.result_term_idx, input_idx, max_binding, self);
        let result_term_idx = self.add_zk_term(result_term);

        let rule = ExpRule::ctor_proj(
            input_idx,
            result_term_idx,
            zk_context,
            inductive,
            parent0,
            quot,
            parent1,
        );
        self.add_zk_rule(rule)
    }

    pub fn export_lift(
        &mut self,
        input_idx: usize,
        max_binding: usize,
        min_binding_seen: usize,
        rule_type: usize,
    ) -> usize {
        unsafe {
            LIFT_COUNTS_MAP.insert(rule_type, *LIFT_COUNTS_MAP.get(&rule_type).unwrap_or(&0))
        };
        let input = self.get_zk_term(input_idx).clone();

        let zk_rule = match input.kind {
            EXPR_VAR => {
                if input.name >= min_binding_seen {
                    let result = ExpTerm::bound(input.name + max_binding - min_binding_seen);
                    let result_idx = self.add_zk_term(result);
                    ExpLift::lift(input_idx, result_idx, max_binding, min_binding_seen, 0, 0)
                } else {
                    ExpLift::lift(input_idx, input_idx, max_binding, min_binding_seen, 0, 0)
                }
            }
            EXPR_SORT => ExpLift::lift(input_idx, input_idx, max_binding, min_binding_seen, 0, 0),
            EXPR_LAM => {
                let new_min_binding = min(input.name, min_binding_seen);

                let body_idx =
                    self.export_lift(input.right, max_binding, new_min_binding, rule_type);
                let body_result = self.get_zk_lift(body_idx).result_term_idx;

                let domain_idx =
                    self.export_lift(input.left, max_binding, new_min_binding, rule_type);
                let domain_result = self.get_zk_lift(domain_idx).result_term_idx;

                let result = ExpTerm::lam(
                    input.name + max_binding - new_min_binding,
                    domain_result,
                    body_result,
                );
                let result_idx = self.add_zk_term(result);

                ExpLift::lift(
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

                let domain_idx =
                    self.export_lift(input.left, max_binding, min_binding_seen, rule_type);
                let domain_result = self.get_zk_lift(domain_idx).result_term_idx;

                let body_idx =
                    self.export_lift(input.right, max_binding, new_min_binding, rule_type);
                let body_result = self.get_zk_lift(body_idx).result_term_idx;

                let result = ExpTerm::pi(
                    input.name + max_binding - new_min_binding,
                    domain_result,
                    body_result,
                );
                let result_idx = self.add_zk_term(result);

                ExpLift::lift(
                    input_idx,
                    result_idx,
                    max_binding,
                    min_binding_seen,
                    body_idx,
                    domain_idx,
                )
            }
            EXPR_APP => {
                let f_idx = self.export_lift(input.left, max_binding, min_binding_seen, rule_type);
                let f_result = self.get_zk_lift(f_idx).result_term_idx;
                let f_term = self.get_zk_term(f_result).clone();

                let e_idx = self.export_lift(input.right, max_binding, min_binding_seen, rule_type);
                let e_result = self.get_zk_lift(e_idx).result_term_idx;

                let result = ExpTerm::app(f_result, e_result, f_term.top_level_func, self);
                let result_idx = self.add_zk_term(result);

                ExpLift::lift(
                    input_idx,
                    result_idx,
                    max_binding,
                    min_binding_seen,
                    e_idx,
                    f_idx,
                )
            }
            EXPR_AX => ExpLift::lift(input_idx, input_idx, max_binding, min_binding_seen, 0, 0),
            EXPR_IND => ExpLift::lift(input_idx, input_idx, max_binding, min_binding_seen, 0, 0),
            EXPR_IND_CTOR => {
                ExpLift::lift(input_idx, input_idx, max_binding, min_binding_seen, 0, 0)
            }
            EXPR_IND_REC => {
                ExpLift::lift(input_idx, input_idx, max_binding, min_binding_seen, 0, 0)
            }
            EXPR_PROJ => {
                // TODO:
                let e_idx = self.export_lift(input.left, max_binding, min_binding_seen, rule_type);
                let e_result = self.get_zk_lift(e_idx).result_term_idx;
                let result = ExpTerm::proj(input.index, e_result);
                let result_idx = self.add_zk_term(result);

                ExpLift::lift(
                    input_idx,
                    result_idx,
                    max_binding,
                    min_binding_seen,
                    e_idx,
                    0,
                )
            }
            EXPR_PROJ_PLACEHOLDER => {
                // TODO:
                ExpLift::lift(input_idx, input_idx, max_binding, min_binding_seen, 0, 0)
            }
            _ => panic!("Unknown expr kind!"),
        };

        self.add_zk_lift(zk_rule, rule_type)
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
        // Clear top_level_func for cache
        let mut zk_term_test = zk_term.clone();
        // fixup top_level_func for non app terms.
        if zk_term.kind != EXPR_APP {
            zk_term_test.top_level_func = 0;
        }
        if let Some(index) = self.zk_term_cache.get(&zk_term_test) {
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
            EXPR_PROJ => {
                free_bindings = self
                    .zk_term_free_bindings
                    .get(&zk_term.left)
                    .unwrap()
                    .clone()
            }
            _ => {}
        }

        let mut zk_term = zk_term;
        let index = self.zk_input.terms.len();

        // dont include top level func for caching...
        self.zk_term_cache.insert(zk_term.clone(), index);
        if (index == 19 || index == 2) {
            println!("ZK TEMR: {:?}", zk_term);
        }

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

    fn add_zk_lift(&mut self, zk_lift: ExpLift, rule_type: usize) -> usize {
        if let Some(index) = self.zk_lift_cache.get(&zk_lift) {
            return *index;
        }

        unsafe { *LIFT_COUNTS_MAP.get_mut(&rule_type).unwrap() += 1 };
        // push the new zk term and return index
        self.zk_input.lifts.push(zk_lift.clone());
        let index = self.zk_input.lifts.len() - 1;
        self.zk_lift_cache.insert(zk_lift.clone(), index);
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

    fn get_zk_lift(&self, index: usize) -> &ExpLift {
        &self.zk_input.lifts[index]
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
        let t = self.get_zk_term(term);
        if t.kind != EXPR_VAR {
            for bound in subset.clone() {
                if let Some(val) = context.get(&bound) {
                    let pointers = self.zk_term_free_bindings.get(&val).unwrap();
                    subset = subset.union(pointers).cloned().collect();
                }
            }
        }

        self.zk_input.contexts.split(zk_context, subset)
    }

    pub fn export_term(&mut self, term: Term, num_bindings: usize) -> usize {
        if let Some(index) = self.term_cache.get(&(term.clone(), num_bindings)) {
            return *index;
        }

        let zk_term = match &**term {
            // convert debruijn index to debruijn level...
            // TODO: need more sophisticated names...todo
            TermData::Bound(index) => {
                let db_level = num_bindings - *index - 1;
                ExpTerm::bound(db_level)
            }
            TermData::Sort(level) => ExpTerm::sort(*level),
            TermData::Binding(BindingData { ty, domain, body }) => {
                let body_idx = self.export_term(body.clone(), num_bindings + 1);
                let domain_idx = self.export_term(domain.clone(), num_bindings);
                match ty {
                    // TODO: names
                    BindingType::Lam => ExpTerm::lam(num_bindings, domain_idx, body_idx),
                    BindingType::Pi => ExpTerm::pi(num_bindings, domain_idx, body_idx),
                }
            }
            TermData::App(f, e) => {
                let f_idx = self.export_term(f.clone(), num_bindings);
                let f_term = self.get_zk_term(f_idx).clone();
                let e_idx = self.export_term(e.clone(), num_bindings);

                ExpTerm::app(f_idx, e_idx, f_term.top_level_func, self)
            }
            TermData::Axiom(name) => {
                // TODO: inductives and inductive rules....
                if let Some((ax, tag)) = self.axiom_mapping.get(name) {
                    ExpTerm::ax(*ax, *tag)
                } else {
                    if let Some(axioms_map) = &self.axioms {
                        let term = axioms_map
                            .get(name)
                            .expect(&format!("Couldn't find axiom named: {}", name));
                        self.add_axiom_term(name.to_string(), term.clone());
                        let (ax, tag) = *self.axiom_mapping.get(name).unwrap();
                        ExpTerm::ax(ax, tag)
                    } else {
                        panic!("Couldn't find axiom named: {}", name);
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
            TermData::Proj(name, index, expr) => {
                let e_idx = self.export_term(expr.clone(), num_bindings);

                // flip index... 0 is last arg, n is first arg
                let inductive = self.inductives.get(name).unwrap_or(
                    self.inductives
                        .iter()
                        .find_map(|(k, v)| {
                            let k_parts = k.split(".").collect::<Vec<_>>();
                            let k_parts = k_parts[0..k_parts.len() - 1].join(".");
                            if name == &k_parts {
                                Some(v)
                            } else {
                                None
                            }
                        })
                        .unwrap(),
                );
                let inductive_rule = inductive.rules[0].clone();
                let flipped_index =
                    (inductive_rule.ty.params().len() - inductive.num_params) - *index - 1;
                ExpTerm::proj(flipped_index, e_idx)
            }
            TermData::ProjTyper(name) => {
                let inductive = self.get_or_export_ind(name);
                ExpTerm::proj_placeholder(inductive)
            }
            TermData::Defn(name, ty, val) => {
                let val_idx = self.export_term(val.clone(), num_bindings);
                let val_term = self.get_zk_term(val_idx).clone();
                val_term
            }
            _ => {
                assert!(false);
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
        EXPR_AX => {
            format!(
                "Axiom({})",
                (axioms_rev_map.get(&(term.ax, term.right)).unwrap())
            )
        }
        EXPR_IND => format!("Ind({})", ind_rev_map.get(&term.ind).unwrap()),
        EXPR_IND_CTOR => format!(
            "IndCtor({}.{})",
            ind_rev_map.get(&term.ind).unwrap(),
            term.ind_ctor,
        ),
        EXPR_IND_REC => format!(
            "IndRec({}, {})",
            ind_rev_map.get(&term.ind).unwrap(),
            term.ind_ctor
        ),
        EXPR_PROJ => format!(
            "Proj({}, {})",
            term.index,
            term_to_string(term.left, terms, axioms_rev_map, ind_rev_map),
        ),
        _ => unimplemented!(),
    }
}

pub fn to_term(
    term_idx: usize,
    terms: &[ExpTerm],
    axioms_rev_map: &HashMap<(usize, usize), String>,
    ind_rev_map: &HashMap<usize, String>,
    inds: &HashMap<String, Inductive>,
) -> Term {
    let term = &terms[term_idx];
    match term.kind {
        EXPR_VAR => term::bound(term.name),
        EXPR_SORT => term::sort(term.name),
        EXPR_LAM => {
            let domain = to_term(term.left, terms, axioms_rev_map, ind_rev_map, inds);
            let body = to_term(term.right, terms, axioms_rev_map, ind_rev_map, inds);
            term::lam(domain, body)
        }
        EXPR_PI => {
            let domain = to_term(term.left, terms, axioms_rev_map, ind_rev_map, inds);
            let body = to_term(term.right, terms, axioms_rev_map, ind_rev_map, inds);
            term::pi(domain, body)
        }
        EXPR_APP => {
            let f = to_term(term.left, terms, axioms_rev_map, ind_rev_map, inds);
            let e = to_term(term.right, terms, axioms_rev_map, ind_rev_map, inds);
            term::app(f, e)
        }
        EXPR_AX => term::axiom(axioms_rev_map.get(&(term.left, term.right)).unwrap()),
        EXPR_IND => term::ind(ind_rev_map.get(&term.ind).unwrap()),
        EXPR_IND_CTOR => {
            let ind = ind_rev_map.get(&term.ind).unwrap().to_string();
            let rule = term.ind_ctor;
            term::ind_ctor(&ind, &inds.get(&ind).unwrap().rules[rule].name)
        }
        EXPR_IND_REC => {
            let ind = ind_rev_map.get(&term.ind).unwrap().to_string();
            term::ind_rec(ind, term.ind_ctor)
        }
        EXPR_PROJ => {
            let ind = &inds[ind_rev_map.get(&term.ind).unwrap()];
            // flip index back around...
            term::proj(
                ind_rev_map.get(&term.ind).unwrap().to_string(),
                ind.rules[0].ty.params().len() - ind.num_params - term.index - 1,
                to_term(term.left, terms, axioms_rev_map, ind_rev_map, inds),
            )
        }
        EXPR_PROJ_PLACEHOLDER => term::proj_typer(ind_rev_map.get(&term.ind).unwrap().to_string()),
        _ => unimplemented!("to_term unimplemented: {}", term.kind),
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::term::*;
    use sim::simulate;

    fn run_eval_test(input: Term, output: Term, inds: HashMap<String, Inductive>) {
        let mut exp = Exporter::with_axioms(output.clone(), HashMap::new(), inds.clone());
        let rule = exp.export_eval_term(input.clone());
        //assert_eq!(res, output);

        simulate(
            exp.zk_input.clone(),
            false,
            &exp.axiom_rev_mapping,
            &exp.ind_rev_map,
        );

        let res = exp.export_term(output.clone(), 0);
        let actual_res = exp.get_zk_rule(rule).result_term_idx;
        println!("INPUT TERM: {:?}", input);
        println!(
            "EXPECT TERM: {:?}",
            to_term(
                res,
                &exp.zk_input.terms,
                &exp.axiom_rev_mapping,
                &exp.ind_rev_map,
                &inds,
            )
        );
        println!(
            "GOT TERM: {:?}",
            to_term(
                actual_res,
                &exp.zk_input.terms,
                &exp.axiom_rev_mapping,
                &exp.ind_rev_map,
                &inds
            )
        );
        assert_eq!(res, actual_res);
        assert_eq!(
            to_term(
                actual_res,
                &exp.zk_input.terms,
                &exp.axiom_rev_mapping,
                &exp.ind_rev_map,
                &inds
            ),
            output
        );
    }

    fn run_ty_test(input: Term, ty: Term, inds: HashMap<String, Inductive>) {
        let theorem = Theorem::new(input, ty, &HashMap::new(), &inds);
        let mut exp = Exporter::simulate(theorem).unwrap();

        //let res = exp.export_term(ty.clone(), 0);
        //let actual_res = exp.get_zk_rule(rule).result_term_idx;
        //println!(
        //    "EXPECT TERM: {:?}",
        //    to_term(
        //        res,
        //        &exp.zk_input.terms,
        //        &exp.axiom_rev_mapping,
        //        &exp.ind_rev_map,
        //        &inds,
        //    )
        //);
        //println!(
        //    "GOT TERM: {:?}",
        //    to_term(
        //        actual_res,
        //        &exp.zk_input.terms,
        //        &exp.axiom_rev_mapping,
        //        &exp.ind_rev_map,
        //        &inds
        //    )
        //);
        //assert_eq!(res, actual_res);
        //assert_eq!(
        //    to_term(
        //        actual_res,
        //        &exp.zk_input.terms,
        //        &exp.axiom_rev_mapping,
        //        &exp.ind_rev_map,
        //        &inds
        //    ),
        //    ty
        //);
    }

    #[test]
    fn eval_proj_cannot_reduce() {
        let prod_rule = InductiveRule::new(
            "mk",
            pi(
                sort(1),
                pi(
                    sort(1),
                    pi(
                        bound(1),
                        pi(bound(1), app(app(ind("PProd.{1}"), bound(3)), bound(2))),
                    ),
                ),
            ),
        );
        let prod = Inductive::new(
            "PProd.{1}",
            2,
            pi(sort(1), pi(sort(1), sort(1))),
            &[prod_rule],
            false,
        );
        let mut inds = HashMap::new();
        inds.insert("PProd.{1}".to_string(), prod);

        let term = lam(
            app(app(ind("PProd.{1}"), sort(0)), sort(0)),
            proj("PProd.{1}".to_string(), 0, bound(0)),
        );
        run_eval_test(term.clone(), term.clone(), inds);
    }

    #[test]
    fn ty_proj_cannot_reduce() {
        let prod_rule = InductiveRule::new(
            "mk",
            pi(
                sort(1),
                pi(
                    sort(1),
                    pi(
                        bound(1),
                        pi(bound(1), app(app(ind("PProd.{1}"), bound(3)), bound(2))),
                    ),
                ),
            ),
        );
        let prod = Inductive::new(
            "PProd.{1}",
            2,
            pi(sort(1), pi(sort(1), sort(1))),
            &[prod_rule],
            false,
        );
        let mut inds = HashMap::new();
        inds.insert("PProd.{1}".to_string(), prod);

        let term = lam(
            app(app(ind("PProd.{1}"), sort(0)), sort(0)),
            proj("PProd.{1}".to_string(), 0, bound(0)),
        );
        let ty = pi(app(app(ind("PProd.{1}"), sort(0)), sort(0)), sort(0));
        run_ty_test(term.clone(), ty.clone(), inds.clone());

        let term = lam(
            app(app(ind("PProd.{1}"), sort(0)), sort(0)),
            proj("PProd.{1}".to_string(), 1, bound(0)),
        );
        let ty = pi(app(app(ind("PProd.{1}"), sort(0)), sort(0)), sort(0));
        run_ty_test(term.clone(), ty.clone(), inds);
    }

    #[test]
    fn ty_proj_ctor_bound() {
        let prod_rule = InductiveRule::new(
            "mk",
            pi(
                sort(1),
                pi(
                    sort(1),
                    pi(
                        sort(1),
                        pi(
                            bound(0),
                            pi(bound(2), app(app(ind("Struct.{1}"), bound(4)), bound(3))),
                        ),
                    ),
                ),
            ),
        );
        let prod = Inductive::new(
            "Struct.{1}",
            2,
            pi(sort(1), pi(sort(1), sort(1))),
            &[prod_rule],
            false,
        );
        let mut inds = HashMap::new();
        inds.insert("Struct.{1}".to_string(), prod);

        let term = lam(
            app(app(ind("Struct.{1}"), sort(0)), sort(0)),
            proj("Struct.{1}".to_string(), 0, bound(0)),
        );
        let ty = pi(app(app(ind("Struct.{1}"), sort(0)), sort(0)), sort(1));
        run_ty_test(term.clone(), ty.clone(), inds.clone());

        let term = lam(
            app(app(ind("Struct.{1}"), sort(0)), sort(0)),
            proj("Struct.{1}".to_string(), 1, bound(0)),
        );
        let ty = pi(
            app(app(ind("Struct.{1}"), sort(0)), sort(0)),
            proj("Struct.{1}".to_string(), 0, bound(0)),
        );
        run_ty_test(term.clone(), ty.clone(), inds.clone());

        let term = lam(
            app(app(ind("Struct.{1}"), sort(0)), sort(0)),
            proj("Struct.{1}".to_string(), 2, bound(0)),
        );
        let ty = pi(app(app(ind("Struct.{1}"), sort(0)), sort(0)), sort(0));
        run_ty_test(term.clone(), ty.clone(), inds);
    }

    #[test]
    fn eval_app_sub_reduce() {
        let term = app(
            app(lam(sort(1), lam(sort(2), app(bound(0), bound(1)))), sort(0)),
            sort(1),
        );
        let result = app(sort(1), sort(0));

        run_eval_test(term.clone(), result, HashMap::new());

        let term = app(
            app(pi(sort(1), pi(sort(2), app(bound(0), bound(1)))), sort(0)),
            sort(1),
        );
        let result = app(sort(1), sort(0));

        run_eval_test(term.clone(), result, HashMap::new());
    }

    #[test]
    fn eval_proj_reduce() {
        let prod_rule = InductiveRule::new(
            "mk",
            pi(
                sort(1),
                pi(
                    sort(1),
                    pi(
                        bound(1),
                        pi(bound(1), app(app(ind("PProd.{1}"), bound(3)), bound(2))),
                    ),
                ),
            ),
        );
        let prod = Inductive::new(
            "PProd.{1}",
            2,
            pi(sort(1), pi(sort(1), sort(1))),
            &[prod_rule],
            false,
        );

        let nat_zero = InductiveRule::new("zero", ind("Nat"));
        let nat_succ = InductiveRule::new("succ", pi(ind("Nat"), ind("Nat")));
        let nat = Inductive::new("Nat", 0, sort(1), &[nat_zero, nat_succ], false);

        let mut inds = HashMap::new();
        inds.insert("PProd.{1}".to_string(), prod);
        inds.insert("Nat".to_string(), nat);

        let term = proj(
            "PProd.{1}".to_string(),
            0,
            app(
                app(
                    app(app(ind_ctor("PProd.{1}", "mk"), ind("Nat")), ind("Nat")),
                    ind_ctor("Nat", "zero"),
                ),
                ind_ctor("Nat", "zero"),
            ),
        );
        let result = ind_ctor("Nat", "zero");

        run_eval_test(term.clone(), result, inds.clone());

        let term = proj(
            "PProd.{1}".to_string(),
            1,
            app(
                app(
                    app(app(ind_ctor("PProd.{1}", "mk"), ind("Nat")), ind("Nat")),
                    ind_ctor("Nat", "zero"),
                ),
                app(ind_ctor("Nat", "succ"), ind_ctor("Nat", "zero")),
            ),
        );
        let result = app(ind_ctor("Nat", "succ"), ind_ctor("Nat", "zero"));

        run_eval_test(term.clone(), result, inds);
    }

    // TODO: test for:
    //       walk_proj
    //       typing proj with args
    //       typing proj with no args
    //       typing proj with eval proj
}

//#[cfg(test)]
//mod test {
//    use super::*;
//    use crate::term::*;
//    use sim::simulate;
//
//    fn run_eval_test(input: Term, output: Term) {
//        let mut exp = Exporter::new();
//        let rule = exp.export_eval_term(input);
//        //assert_eq!(res, output);
//
//        simulate(exp.zk_input.clone(), true, &exp.axiom_rev_mapping);
//
//        let res = exp.export_term(output, 0, None);
//        let actual_res = exp.get_zk_rule(rule).result_term_idx;
//        println!(
//            "GOT TERM: {:?}",
//            to_term(actual_res, &exp.zk_input.terms, &exp.axiom_rev_mapping)
//        );
//        assert_eq!(res, actual_res);
//    }
//
//    fn run_fail_eval_test(input: Term, output: Term) {
//        let mut exp = Exporter::new();
//        let rule = exp.export_eval_term(input);
//
//        let wrong_output_idx = exp.export_term(output, 0, None);
//        exp.zk_input.rules[rule].result_term_idx = wrong_output_idx;
//
//        simulate(exp.zk_input, true, &exp.axiom_rev_mapping);
//    }
//
//    #[test]
//    fn eval_sort() {
//        run_eval_test(sort(0), sort(0));
//    }
//
//    #[test]
//    #[should_panic]
//    fn eval_sort_fail() {
//        run_eval_test(sort(0), sort(1));
//    }
//
//    #[test]
//    fn eval_lam() {
//        let input = lam(sort(0), sort(0));
//        run_eval_test(input.clone(), input);
//    }
//
//    #[test]
//    #[should_panic]
//    fn eval_lam_fail() {
//        run_fail_eval_test(lam(sort(0), sort(0)), lam(sort(0), sort(1)));
//    }
//
//    #[test]
//    fn eval_pi() {
//        let input = pi(sort(0), sort(0));
//        run_eval_test(input.clone(), input);
//    }
//
//    #[test]
//    fn eval_nested() {
//        let input = pi(sort(0), app(lam(sort(2), bound(0)), sort(1)));
//        let res = pi(sort(0), sort(1));
//        run_eval_test(input.clone(), res);
//    }
//
//    #[test]
//    fn eval_nested_lam() {
//        let input = lam(
//            sort(0),
//            app(lam(pi(sort(0), sort(0)), bound(0)), lam(sort(0), bound(0))),
//        );
//        let res = lam(sort(0), lam(sort(0), bound(0)));
//        run_eval_test(input.clone(), res);
//    }
//
//    #[test]
//    fn successive_apps() {
//        let input = app(
//            app(lam(pi(sort(0), sort(0)), bound(0)), lam(sort(0), bound(0))),
//            sort(1),
//        );
//        let res = sort(1);
//        run_eval_test(input, res);
//    }
//
//    #[test]
//    #[should_panic]
//    fn eval_lam_nonlam_fail() {
//        run_fail_eval_test(lam(sort(0), sort(0)), sort(0));
//    }
//
//    #[test]
//    fn eval_app() {
//        let input = app(sort(0), sort(1));
//        run_eval_test(input.clone(), input);
//    }
//
//    #[test]
//    #[should_panic(expected = "assertion failed: result_term.kind == EXPR_APP")]
//    fn eval_app_fail() {
//        run_fail_eval_test(app(sort(0), sort(1)), sort(0));
//    }
//
//    #[test]
//    fn eval_app_lam() {
//        run_eval_test(app(lam(sort(1), sort(2)), sort(0)), sort(2));
//    }
//
//    #[test]
//    #[should_panic(expected = "assertion failed: parent3.result_term_idx == node.result_term_idx")]
//    fn eval_app_lam_fail() {
//        run_fail_eval_test(app(lam(sort(1), sort(2)), sort(0)), sort(1));
//    }
//
//    #[test]
//    fn eval_app_lam_bound() {
//        run_eval_test(app(lam(sort(1), bound(0)), sort(0)), sort(0));
//    }
//
//    #[test]
//    fn eval_app_lam_bound_subsets() {
//        // TODO: cannot actually run this because we don't do lifting/unlifting and our names are
//        // wrong LOL
//        //run_eval_test(
//        //    app(lam(sort(1), lam(sort(1), bound(0))), sort(0)),
//        //    lam(sort(1), bound(1)),
//        //);
//    }
//
//    #[test]
//    fn eval_app_renaming() {
//        // TODO: fix
//        //    run_eval_test(
//        //        app(
//        //            lam(pi(sort(0), sort(0)), app(bound(0), bound(0))),
//        //            lam(pi(sort(0), sort(0)), bound(0)),
//        //        ),
//        //        lam(sort(0), bound(0)),
//        //    );
//    }
//
//    // TODO:
//    //#[test]
//    //fn eval_app_lam_bound_fail() {
//    //    let mut exp = Exporter::new();
//    //    let (rule, res) = exp.export_eval(
//    //        app(lam(sort(2), bound(0)), sort(1)),
//    //        HashList::EMPTY,
//    //        &mut Context::new(),
//    //        &mut Vec::new(),
//    //    );
//
//    //    // craft fake proof
//    //    let wrong_output_idx = exp.export_term(sort(0), &mut Vec::new());
//    //    exp.rules[rule].result_term_idx = wrong_output_idx;
//
//    //    let parent2 = exp.rules[rule].parent2;
//    //    exp.rules[parent2].result_term_idx = wrong_output_idx;
//
//    //    let zk_input = exp.to_zk_input();
//    //    simulate(zk_input);
//    //}
//    //
//    //#[test]
//    //fn eval_bound() {
//    //    let mut exp = Exporter::new();
//    //    let s0 = exp.export_term(sort(0), &mut Vec::new());
//    //    let zk_context = exp.contexts.add(HashList::EMPTY, 0, s0);
//    //    let mut context = Context::new();
//    //    context.push(sort(0));
//    //    println!("ctx: {:?}", exp.contexts.nodes[0]);
//    //    let (rule, res) = exp.export_eval(bound(0), zk_context, &mut context, &mut vec![0]);
//    //    println!("rule: {:?} {:?}", exp.rules[rule], res);
//    //    simulate(exp.to_zk_input());
//    //}
//
//    //#[test]
//    //#[should_panic(
//    //    expected = "assertion failed: contexts.contains(node.ctx_idx, input_term.left, node.result_term_idx)"
//    //)]
//    //fn fail_eval_bound() {
//    //    let mut exp = Exporter::new();
//    //    let s0 = exp.export_term(sort(0), &mut Vec::new());
//    //    let zk_context = exp.contexts.add(HashList::EMPTY, 0, s0);
//    //    context.push(sort(1));
//    //    let (rule, res) = exp.export_eval(bound(0), zk_context, &mut context, &mut vec![0]);
//    //    println!("rule: {:?} {:?}", exp.rules[rule], res);
//    //    simulate(exp.to_zk_input());
//    //}
//
//    //#[test]
//    //fn eval_app_lam_
//    //
//    fn run_ty_test(input: Term, output: Term) {
//        let mut exp = Exporter::new();
//        let rule = exp.export_ty_term(input).unwrap();
//        //assert_eq!(res, output);
//
//        simulate(exp.zk_input.clone(), true, &exp.axiom_rev_mapping);
//
//        let res = exp.export_term(output, 0, None);
//        let actual_res = exp.get_zk_rule(rule).result_term_idx;
//        println!(
//            "GOT TERM: {:?}",
//            to_term(actual_res, &exp.zk_input.terms, &exp.axiom_rev_mapping)
//        );
//        assert_eq!(res, actual_res);
//    }
//
//    #[test]
//    fn type_sort() {
//        run_ty_test(sort(0), sort(1));
//    }
//
//    #[test]
//    fn type_lam() {
//        run_ty_test(lam(sort(0), sort(0)), pi(sort(0), sort(1)));
//    }
//
//    #[test]
//    fn type_lam_bound() {
//        run_ty_test(lam(sort(0), bound(0)), pi(sort(0), sort(0)));
//    }
//
//    #[test]
//    fn type_pi() {
//        run_ty_test(pi(sort(0), sort(0)), sort(1));
//    }
//
//    #[test]
//    fn type_app() {
//        run_ty_test(app(lam(sort(1), bound(0)), sort(0)), sort(1))
//    }
//
//    fn run_ty_axioms(input: Term, output: Term, axioms: HashMap<String, Term>) {
//        //let mut exp = Exporter::with_axioms(axioms);
//        //let rule = exp.export_ty_term(input);
//        ////assert_eq!(res, output);
//
//        //// TODO: wtf
//        //println!(
//        //    "input: {:?}",
//        //    to_term(
//        //        exp.get_zk_rule(rule).input_term_idx,
//        //        &exp.zk_input.terms,
//        //        &exp.axiom_rev_mapping
//        //    )
//        //);
//        //simulate(exp.zk_input.clone(), &exp.axiom_rev_mapping);
//
//        //let res = exp.export_term(output, 0, None);
//        //let actual_res = exp.get_zk_rule(rule).result_term_idx;
//        //println!(
//        //    "GOT TERM: {:?}",
//        //    to_term(actual_res, &exp.zk_input.terms, &exp.axiom_rev_mapping)
//        //);
//        //assert_eq!(res, actual_res);
//    }
//
//    #[test]
//    fn type_sort_axioms() {
//        let mut axioms = HashMap::new();
//        axioms.insert("and".to_owned(), pi(sort(0), pi(sort(0), sort(0))));
//        run_ty_axioms(axiom("and"), pi(sort(0), pi(sort(0), sort(0))), axioms);
//    }
//
//    #[test]
//    fn type_props() {
//        let axioms: HashMap<String, Term> = HashMap::from([
//            ("p", sort(0)),
//            ("q", sort(0)),
//            ("or", pi(sort(0), pi(sort(0), sort(0)))),
//            (
//                "or.inr",
//                pi(
//                    sort(0),
//                    pi(
//                        sort(0),
//                        pi(bound(0), app(app(axiom("or"), bound(2)), bound(1))),
//                    ),
//                ),
//            ),
//        ])
//        .iter()
//        .map(|(k, v)| (k.to_string(), v.clone()))
//        .collect();
//
//        println!("axioms: {:?}", axioms);
//
//        //run_ty_axioms(
//        //    axiom("or"),
//        //    pi(sort(0), pi(sort(0), sort(0))),
//        //    axioms.clone(),
//        //);
//        ////run_ty_axioms(axiom("or.inr"), sort(0), axioms);
//        //run_ty_axioms(app(axiom("or.inr"), axiom("p")), sort(0), axioms);
//    }
//
//    #[test]
//    fn type_naming() {
//        let axioms: HashMap<String, Term> = HashMap::from([
//            ("p", sort(0)),
//            ("q", sort(0)),
//            ("or", pi(sort(0), pi(sort(0), sort(0)))),
//            (
//                "or.inr",
//                pi(
//                    sort(0),
//                    pi(
//                        sort(0),
//                        pi(bound(0), app(app(axiom("or"), bound(2)), bound(1))),
//                    ),
//                ),
//            ),
//        ])
//        .iter()
//        .map(|(k, v)| (k.to_string(), v.clone()))
//        .collect();
//
//        run_ty_axioms(
//            lam(
//                sort(0),
//                lam(sort(0), app(app(axiom("or.inr"), bound(0)), bound(1))),
//            ),
//            sort(0),
//            axioms,
//        );
//    }
//
//    #[test]
//    fn ty_ax_lift() {
//        //let axioms: HashMap<String, Term> = HashMap::from([(
//        //    "or.inr",
//        //    pi(
//        //        sort(0),
//        //        pi(sort(0), pi(bound(0), app(app(sort(0), bound(2)), bound(1)))),
//        //    ),
//        //)])
//        //.iter()
//        //.map(|(k, v)| (k.to_string(), v.clone()))
//        //.collect();
//
//        //let mut exp = Exporter::with_axioms(axioms.clone());
//
//        //let term = axiom("or.inr");
//        //let zk_term = exp.export_term(term, 0, None);
//        //let res = exp.export_ty(zk_term, HashList::EMPTY, &mut HashMap::new(), 0);
//        //let rule = exp.get_zk_rule(res);
//
//        //assert_eq!("Π (0 : Sort(0), Π (1 : Sort(0), Π (2 : Bound(1), App(App(Sort(0), Bound(0)), Bound(1)))))",
//        //    term_to_string(
//        //        rule.result_term_idx,
//        //        &exp.zk_input.terms,
//        //        &exp.axiom_rev_mapping
//        //    ));
//
//        //let res = exp.export_ty(zk_term, HashList::EMPTY, &mut HashMap::new(), 3);
//        //let rule = exp.get_zk_rule(res);
//
//        //assert_eq!("Π (3 : Sort(0), Π (4 : Sort(0), Π (5 : Bound(4), App(App(Sort(0), Bound(3)), Bound(4)))))",
//        //    term_to_string(
//        //        rule.result_term_idx,
//        //        &exp.zk_input.terms,
//        //        &exp.axiom_rev_mapping
//        //    ));
//
//        //simulate(exp.zk_input, &exp.axiom_rev_mapping);
//    }
//
//    fn ty_ax_more() {
//        // todo
//    }
//
//    #[test]
//    fn basic_lift() {
//        let mut exp = Exporter::new();
//        let term = pi(sort(0), pi(sort(0), bound(0)));
//        let zk_term = exp.export_term(term, 3, None);
//
//        assert_eq!(
//            "Π (3 : Sort(0), Π (4 : Sort(0), Bound(4)))",
//            term_to_string(zk_term, &exp.zk_input.terms, &HashMap::new())
//        );
//
//        let lift_rule = exp.export_lift(zk_term, 5, usize::MAX);
//        let lift_res = exp.get_zk_rule(lift_rule).result_term_idx;
//        assert_eq!(
//            "Π (5 : Sort(0), Π (6 : Sort(0), Bound(6)))",
//            term_to_string(lift_res, &exp.zk_input.terms, &HashMap::new())
//        );
//
//        let unlift_rule = exp.export_lift(zk_term, 1, usize::MAX);
//        let unlift_res = exp.get_zk_rule(unlift_rule).result_term_idx;
//        assert_eq!(
//            "Π (1 : Sort(0), Π (2 : Sort(0), Bound(2)))",
//            term_to_string(unlift_res, &exp.zk_input.terms, &HashMap::new())
//        );
//
//        simulate(exp.zk_input, true, &HashMap::new());
//    }
//
//    #[test]
//    fn free_lift() {
//        let mut exp = Exporter::new();
//        let term = pi(sort(0), pi(sort(0), bound(4)));
//        let zk_term = exp.export_term(term, 3, None);
//
//        assert_eq!(
//            "Π (3 : Sort(0), Π (4 : Sort(0), Bound(0)))",
//            term_to_string(zk_term, &exp.zk_input.terms, &HashMap::new())
//        );
//
//        let lift_rule = exp.export_lift(zk_term, 5, usize::MAX);
//        let lift_res = exp.get_zk_rule(lift_rule).result_term_idx;
//        assert_eq!(
//            "Π (5 : Sort(0), Π (6 : Sort(0), Bound(0)))",
//            term_to_string(lift_res, &exp.zk_input.terms, &HashMap::new())
//        );
//
//        let unlift_rule = exp.export_lift(zk_term, 1, usize::MAX);
//        let unlift_res = exp.get_zk_rule(unlift_rule).result_term_idx;
//        assert_eq!(
//            "Π (1 : Sort(0), Π (2 : Sort(0), Bound(0)))",
//            term_to_string(unlift_res, &exp.zk_input.terms, &HashMap::new())
//        );
//
//        simulate(exp.zk_input, true, &HashMap::new());
//    }
//
//    #[test]
//    fn get_arg() {
//        let mut exp = Exporter::new();
//
//        let term = app(sort(0), sort(1));
//        let zk_term = exp.export_term(term, 0, None);
//
//        let get_arg_rule = exp.export_get_arg(zk_term, 0).unwrap();
//        let get_arg_res = exp.get_zk_rule(get_arg_rule).result_term_idx;
//
//        assert_eq!(
//            "Sort(1)",
//            term_to_string(get_arg_res, &exp.zk_input.terms, &HashMap::new())
//        );
//
//        simulate(exp.zk_input.clone(), false, &HashMap::new());
//
//        let term = app(
//            app(app(app(app(sort(0), sort(1)), sort(2)), sort(3)), sort(4)),
//            sort(5),
//        );
//        let zk_term = exp.export_term(term, 0, None);
//
//        let get_arg_rule = exp.export_get_arg(zk_term, 2).unwrap();
//        let get_arg_res = exp.get_zk_rule(get_arg_rule).result_term_idx;
//        assert_eq!(
//            "Sort(3)",
//            term_to_string(get_arg_res, &exp.zk_input.terms, &HashMap::new())
//        );
//        simulate(exp.zk_input.clone(), false, &HashMap::new());
//    }
//
//    #[test]
//    fn apply_elim() {
//        let mut exp = Exporter::new();
//
//        let rec = sort(0);
//        let elim = sort(1);
//        let term = app(sort(2), sort(3));
//        let zk_rec = exp.export_term(rec, 0, None);
//        let zk_elim = exp.export_term(elim, 0, None);
//        let zk_term = exp.export_term(term, 0, None);
//
//        let apply_elim_norec = exp
//            .export_apply_elim(zk_term, zk_rec, zk_elim, 1, 0)
//            .unwrap();
//        let apply_elim_res = exp.get_zk_rule(apply_elim_norec).result_term_idx;
//
//        assert_eq!(
//            "App(Sort(1), Sort(3))",
//            term_to_string(apply_elim_res, &exp.zk_input.terms, &HashMap::new())
//        );
//
//        simulate(exp.zk_input.clone(), false, &HashMap::new());
//
//        let term = app(
//            app(app(app(app(sort(2), sort(3)), sort(4)), sort(5)), sort(6)),
//            sort(7),
//        );
//        let zk_term = exp.export_term(term, 0, None);
//
//        let apply_elim_rec = exp
//            .export_apply_elim(zk_term, zk_rec, zk_elim, 2, 3)
//            .unwrap();
//        let apply_elim_res = exp.get_zk_rule(apply_elim_rec).result_term_idx;
//        assert_eq!(
//            "App(App(App(App(App(Sort(1), Sort(3)), Sort(4)), App(Sort(0), Sort(5))), App(Sort(0), Sort(6))), App(Sort(0), Sort(7)))",
//            term_to_string(apply_elim_res, &exp.zk_input.terms, &HashMap::new())
//        );
//        simulate(exp.zk_input.clone(), false, &HashMap::new());
//    }
//
//    #[test]
//    fn apply_elim_eval() {
//        let mut exp = Exporter::new();
//
//        let rec = sort(0);
//        let elim = lam(sort(3), sort(5));
//        let term = app(sort(2), sort(3));
//        let zk_rec = exp.export_term(rec, 0, None);
//        let zk_elim = exp.export_term(elim, 0, None);
//        let zk_term = exp.export_term(term, 0, None);
//
//        let apply_elim_norec = exp
//            .export_apply_elim_eval(
//                zk_term,
//                HashList::EMPTY,
//                &mut HashMap::new(),
//                0,
//                zk_rec,
//                zk_elim,
//                1,
//                0,
//            )
//            .unwrap();
//        let apply_elim_res = exp.get_zk_rule(apply_elim_norec).result_term_idx;
//
//        assert_eq!(
//            "Sort(5)",
//            term_to_string(apply_elim_res, &exp.zk_input.terms, &HashMap::new())
//        );
//
//        simulate(exp.zk_input.clone(), false, &HashMap::new());
//    }
//
//    // TODO: add some fail tests for shadowing / not actually replacing vars
//}
