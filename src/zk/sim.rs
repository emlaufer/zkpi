//! Simulator for the ZK circuit
#![allow(non_snake_case)]

use super::*;

fn print_rule(
    rule_str: &str,
    ctx: usize,
    input: usize,
    result: usize,
    contexts: &HashList,
    terms: &[ExpTerm],
    db_axiom_rev_map: &HashMap<(usize, usize), String>,
    eval_rule: bool,
) {
    let sep = if eval_rule { "=>" } else { "::" };
    //println!(
    //    "checking {}: {} |- {:?} {} {:?}",
    //    rule_str,
    //    contexts.to_string(ctx),
    //    to_term(input, terms, db_axiom_rev_map),
    //    sep,
    //    to_term(result, terms, db_axiom_rev_map)
    //);
}

fn imax(i: usize, j: usize) -> usize {
    if j == 0 {
        0
    } else {
        max(i, j)
    }
}

fn is_eval_rule(rule: usize) -> bool {
    //return rule >= 1 && rule < 10
    return rule == RULE_EVAL_ID
        || rule == RULE_EVAL_VAR
        || rule == RULE_EVAL_SORT
        || rule == RULE_EVAL_APP
        || rule == RULE_EVAL_APP_LAM
        || rule == RULE_EVAL_APP_PI
        || rule == RULE_EVAL_LAM
        || rule == RULE_EVAL_PI
        || rule == RULE_PROOF_IRREL
        || rule == RULE_EVAL_IND
        || rule == RULE_EVAL_TRANSITIVE;
}

fn is_type_rule(rule: usize) -> bool {
    //return rule >= 10 && rule < 16
    return rule == RULE_TYPE_VAR
        || rule == RULE_TYPE_SORT
        || rule == RULE_TYPE_APP
        || rule == RULE_TYPE_LAM
        || rule == RULE_TYPE_PI
        || rule == RULE_EVAL_TYPE
        || rule == RULE_TYPE_AX
        || rule == RULE_TYPE_IND
        || rule == RULE_TYPE_IND_CTOR
        || rule == RULE_TYPE_IND_REC;
}

/// TODO: problem here....
/// TODO: this should be equivalent to simple index checking as long as contains is correct
fn hash_list_equals(l1: usize, l2: usize, contexts: &HashList) -> bool {
    contexts.equals(l1, l2)
}

fn hash_list_contains(
    l1: usize,
    key: usize,
    value: usize,
    rem: usize,
    contexts: &HashList,
) -> bool {
    let val_hash = contexts.hash(key, value).0;
    contexts.contains_hash(l1, val_hash, rem)
}

fn hash_list_subset(list: usize, subset: usize, quot: usize, contexts: &HashList) -> bool {
    //println!(
    //    "Checking if {} is a subset of {} (quot: {})",
    //    contexts.to_string(subset),
    //    contexts.to_string(list),
    //    contexts.to_string(quot)
    //);
    contexts.subset(list, subset, quot)
}

// no names here....
// just plop it in the context...
fn check_lift(
    node: &ExpLift,
    proof: &[ExpLift],
    terms: &[ExpTerm],
    db_axiom_rev_map: &HashMap<(usize, usize), String>,
) {
    // track min binding here...
    // case lam:
    //
    let input_term = &terms[node.input_term_idx];
    let result_term = &terms[node.result_term_idx];

    let min_binding = node.min_binding_seen;

    assert!(input_term.kind == result_term.kind);

    if input_term.kind == EXPR_VAR {
        if !(input_term.name < min_binding) {
            assert!(result_term.name == input_term.name + node.max_binding - min_binding);
        }
    } else {
        let parent0 = &proof[node.parent0];
        // ensure lam and pi names lifted properly
        if input_term.kind == EXPR_LAM || input_term.kind == EXPR_PI {
            // TODO: assumption: terms are well formed so we can only have this for the first binding.
            if input_term.name <= min_binding {
                // TODO: hack...just add another field...
                assert!(parent0.min_binding_seen == input_term.name);
                assert!(result_term.name == node.max_binding);
            } else {
                assert!(result_term.name == input_term.name + node.max_binding - min_binding);
            }
        }
    }

    if input_term.kind == EXPR_LAM || input_term.kind == EXPR_PI || input_term.kind == EXPR_APP {
        let parent0 = &proof[node.parent0];
        assert!(node.max_binding == parent0.max_binding);
        // TODO: check...
        //assert!(node.min_binding
        assert!(input_term.right == parent0.input_term_idx);
        assert!(result_term.right == parent0.result_term_idx);

        if input_term.kind != EXPR_LAM {
            let parent1 = &proof[node.parent1];
            // CHECK Min binding is correct
            assert!(node.max_binding == parent1.max_binding);
            assert!(input_term.left == parent1.input_term_idx);
            assert!(result_term.left == parent1.result_term_idx);
        }
    }
}

// TODO: assert parent rule isn't rule_null
// TODO: remove type_var ... can just use a single rule for type and eval...
fn check_type_var(
    node: &ExpRule,
    proof: &[ExpRule],
    lifts: &[ExpLift],
    terms: &[ExpTerm],
    contexts: &HashList,
    db_axiom_rev_map: &HashMap<(usize, usize), String>,
) {
    //println!("Checking: {} |- {:?} :: {:?}",
    //print_rule(
    //    "TYPE_VAR",
    //    node.ctx_idx,
    //    node.input_term_idx,
    //    node.result_term_idx,
    //    contexts,
    //    terms,
    //    db_axiom_rev_map,
    //    false,
    //);
    let input_term = &terms[node.input_term_idx];
    let lift_node = &lifts[node.lift_rule];

    // TODO:
    //assert!(
    //    hash_list_contains(
    //        node.ctx_idx,
    //        input_term.name,
    //        lift_node.input_term_idx,
    //        node.parent0_quot,
    //        contexts
    //    ),
    //    "ctx: {}, quot: {}, got: {} {}",
    //    contexts.to_string(node.ctx_idx),
    //    contexts.to_string(node.parent0_quot),
    //    input_term.name,
    //    lift_node.input_term_idx
    //);
    //assert!(lift_node.rule == RULE_LIFT);
    assert!(lift_node.result_term_idx == node.result_term_idx);
}

fn check_type_sort(node: &ExpRule, proof: &[ExpRule], terms: &[ExpTerm]) {
    let input_term = &terms[node.input_term_idx];
    let result_term = &terms[node.result_term_idx];

    // intput is sort
    assert!(input_term.kind == EXPR_SORT);
    // result is sort
    assert!(result_term.kind == EXPR_SORT);

    // result term has level i+1 of input term
    assert!(input_term.name + 1 == result_term.name);
}

// ============================================================================
//
//                             (C, l) |- a :: A  (a:C, 0) |- B => B'
//                            ----------------------------------------------------------
// (C, l) |- f :: (pi x:A.B)      C |- extra:a,  (pi x:A.B) ^ B' (idk what symbol) (C, 0) |- unlift(B', B'')
// ---------------------------------------------------------------------------------------
//                  (C, l) |- (f a) :: B''
//
// ============================================================================
fn check_type_app(
    node: &ExpRule,
    proof: &[ExpRule],
    lifts: &[ExpLift],
    terms: &[ExpTerm],
    contexts: &HashList,
    db_axiom_rev_map: &HashMap<(usize, usize), String>,
    db_ind_rev_map: &HashMap<usize, String>,
) {
    //println!(
    //    "checking: {} |- {:?} :: {:?}",
    //    contexts.to_string(node.ctx_idx),
    //    to_term(node.input_term_idx, terms, db_axiom_rev_map),
    //    to_term(node.result_term_idx, terms, db_axiom_rev_map)
    //);

    let input_term = &terms[node.input_term_idx];
    let result_term = &terms[node.result_term_idx];

    let parent0 = &proof[node.parent0];
    let parent1 = &proof[node.parent1];
    let parent0_res = &terms[parent0.result_term_idx]; // TODO: could move...
    let lift_rule = &lifts[node.lift_rule];

    assert!(input_term.kind == EXPR_APP);

    assert!(is_type_rule(parent0.rule));
    assert!(parent0.input_term_idx == input_term.left);
    assert!(parent0_res.kind == EXPR_PI);
    assert!(hash_list_subset(
        node.ctx_idx,
        parent0.ctx_idx,
        node.parent0_quot,
        contexts
    ));

    assert!(parent1.rule == RULE_TYPE_APP_SUB);
    assert!(parent1.extra == input_term.right);
    assert!(parent1.input_term_idx == parent0.result_term_idx);
    assert!(hash_list_subset(
        node.ctx_idx,
        parent1.ctx_idx,
        node.parent1_quot,
        contexts
    ));

    assert!(parent1.result_term_idx == lift_rule.input_term_idx);
    assert!(node.result_term_idx == lift_rule.result_term_idx);
}

//  (C, l) |- a :: A  (a:C, 0) |- B => B'
// ----------------------------------------------------- (pi_sub)
//    C |- extra:a,  (pi x:A.B) ^ B' (idk what symbol)
fn check_type_app_sub(
    node: &ExpRule,
    proof: &[ExpRule],
    terms: &[ExpTerm],
    contexts: &HashList,
    db_axiom_rev_map: &HashMap<(usize, usize), String>,
    db_ind_rev_map: &HashMap<usize, String>,
) {
    let input_term = &terms[node.input_term_idx];
    let result_term = &terms[node.result_term_idx];

    // TODO: add A eval...
    let parent0 = &proof[node.parent0];
    let parent1 = &proof[node.parent1];

    assert!(is_type_rule(parent0.rule));
    assert!(is_eval_rule(parent1.rule));
    assert!(input_term.kind == EXPR_PI);

    assert!(parent0.input_term_idx == node.extra);
    assert!(parent0.result_term_idx == input_term.left);
    assert!(hash_list_subset(
        node.ctx_idx,
        parent0.ctx_idx,
        node.parent0_quot,
        contexts
    ));

    assert!(parent1.input_term_idx == input_term.right);
    assert!(parent1.result_term_idx == node.result_term_idx);
    // TODO: ctx add (name, a)
    //assert!(hash_list_subset(
    //    node.ctx_idx,
    //    parent1.ctx_idx,
    //    node.parent1_quot,
    //    contexts
    //));
}

// ============================================================================
//
//          C |- A => A'   (A':C, l) |- b :: B
// ----------------------------------------------------------------------------
//          (C, l) |- \ -> b :: (pi A.B)
//
// ============================================================================
fn check_type_lam(node: &ExpRule, proof: &[ExpRule], terms: &[ExpTerm]) {
    let input_term = &terms[node.input_term_idx];
    let result_term = &terms[node.result_term_idx];

    // TODO: add A eval...
    let parent0 = &proof[node.parent0];

    // ensure node well formed
    assert!(input_term.kind == EXPR_LAM);
    assert!(result_term.kind == EXPR_PI);
    let node_b_idx = input_term.right;
    let node_A_idx = result_term.left;
    let node_B_idx = result_term.right;

    // ensure parent well formed
    assert!(is_type_rule(parent0.rule));
    let p_b_idx = parent0.input_term_idx;
    let p_B_idx = parent0.result_term_idx;

    // TODO: subset equal proof here...
    // ensure context is a prefix
    //res = res && hash_list_popped(parent0.ctx_idx, node.ctx_idx, context)
    //field p_A_idx = context.nodes[parent0.ctx_idx].value

    // check lifts
    //res = res && parent0.num_lifts == node.num_lifts

    // ensure terms match
    //assert!(p_A_idx == node_A_idx);
    assert!(p_B_idx == node_B_idx);
    assert!(p_b_idx == node_b_idx);

    assert!(input_term.name == node.max_binding);
}

// ============================================================================
//
//  (C, l) |- p => v  (C, l) |- v :: Sort i
//  --------------------------------------- (sub)
//          p :: Sort i, extra: v                  (v:C, l) |- p' :: Sort j
// ----------------------------------------------------------------------------
//          (C, l) |- Pi p.p' :: Sort (imax (i, j))
//
// ============================================================================
fn check_type_pi(node: &ExpRule, proof: &[ExpRule], terms: &[ExpTerm], contexts: &HashList) {
    let input_term = &terms[node.input_term_idx];
    let result_term = &terms[node.result_term_idx];

    let parent0 = &proof[node.parent0];
    let parent1 = &proof[node.parent1];

    let sort_i = &terms[parent0.result_term_idx];
    let sort_j = &terms[parent1.result_term_idx];

    assert!(input_term.kind == EXPR_PI);
    assert!(result_term.kind == EXPR_SORT);

    assert!(parent0.rule == RULE_TYPE_PI_SUB);
    assert!(parent0.input_term_idx == input_term.left);

    assert!(parent1.input_term_idx == input_term.right);

    // ensure node well formed
    assert!(input_term.name == node.max_binding);
    assert!(result_term.name == imax(sort_i.name, sort_j.name));
}

// ============================================================================
//
//  (C, l) |- p => v  (C, l) |- v :: Sort i
//  --------------------------------------- (sub) (see check_type_pi)
//          p :: Sort i, extra: v
// ============================================================================
fn check_type_pi_sub(node: &ExpRule, proof: &[ExpRule], terms: &[ExpTerm], contexts: &HashList) {
    let input_term = &terms[node.input_term_idx];
    let result_term = &terms[node.result_term_idx];

    let parent0 = &proof[node.parent0];
    let parent1 = &proof[node.parent1];

    assert!(is_eval_rule(parent0.rule));
    assert!(is_type_rule(parent1.rule));

    // check contexts equal
    assert!(hash_list_subset(
        node.ctx_idx,
        parent0.ctx_idx,
        node.parent0_quot,
        contexts
    ));
    assert!(hash_list_subset(
        node.ctx_idx,
        parent1.ctx_idx,
        node.parent1_quot,
        contexts
    ));

    assert!(node.result_term_idx == parent1.result_term_idx);
    assert!(parent0.result_term_idx == parent1.input_term_idx);
    assert!(node.input_term_idx == parent0.input_term_idx);
    assert!(node.extra == parent1.input_term_idx);
}

fn check_eval_id(node: &ExpRule, terms: &[ExpTerm]) {
    assert!(node.input_term_idx == node.result_term_idx);
}

// ============================================================================
//           lookup(C, n) = e
// ----------------------------------------------------
//        C |- Var n => e'
//
// ============================================================================
fn check_eval_var(
    node: &ExpRule,
    proof: &[ExpRule],
    lifts: &[ExpLift],
    terms: &[ExpTerm],
    contexts: &HashList,
    db_axiom_rev_map: &HashMap<(usize, usize), String>,
    db_ind_rev_map: &HashMap<usize, String>,
) {
    //print_rule(
    //    "EVAL_VAR",
    //    node.ctx_idx,
    //    node.input_term_idx,
    //    node.result_term_idx,
    //    contexts,
    //    terms,
    //    db_axiom_rev_map,
    //    true,
    //);
    //assert!(node.ctx_id
    let input_term = &terms[node.input_term_idx];
    let lift_node = &lifts[node.lift_rule];

    //println!(
    //    "Got term: {} (looking for {})",
    //    term_to_string(
    //        node.result_term_idx,
    //        terms,
    //        db_axiom_rev_map,
    //        db_ind_rev_map
    //    ),
    //    lift_node.input_term_idx
    //);
    //println!("zk_context: {:?}", contexts.to_string(node.ctx_idx));
    assert!(
        hash_list_contains(
            node.ctx_idx,
            input_term.name,
            lift_node.input_term_idx,
            HashList::EMPTY,
            contexts
        ),
        "GOT: {} ({}, {})",
        contexts.to_string(node.ctx_idx),
        input_term.name,
        lift_node.input_term_idx
    );
    //assert!(contexts.contains(node.ctx_idx, input_term.name, lift_node.input_term_idx));
    //assert!(lift_node.rule == RULE_LIFT);
    assert!(lift_node.result_term_idx == node.result_term_idx);
    //assert!(
    //    result_term.min_binding >= node.max_binding,
    //    "Node {:?} has min_binding {}, expected max_binding is: {}",
    //    to_term(node.result_term_idx, terms, db_axiom_rev_map),
    //    result_term.min_binding,
    //    node.max_binding
    //);
    //assert!(node.

    //bool res = true
    //bool ax_ok = true TODO axioms
    //Node parent0 = proof[node.parent0] // lift correct

    //Term input_term = terms[node.input_term_idx]
    //Term result_term = terms[node.result_term_idx]

    //// ensure lookup is correct
    //res = res && input_term.simple_term == EXPR_VAR
    //res = res && input_term.left_idx >= node.num_lifts
    //field ctx_term_idx = context[node.ctx_idx + input_term.left_idx - node.num_lifts]

    //// ensure lift is correct
    //res = res && parent0.rule == RULE_LIFT
    //res = res && parent0.input_term_idx == ctx_term_idx
    //res = res && parent0.result_term_idx == node.result_term_idx
    //res = res && parent0.num_lifts == node.num_lifts
    //res = res && parent0.num_local_bindings == 0
}

fn check_eval_lam(node: &ExpRule, proof: &[ExpRule], terms: &[ExpTerm], contexts: &HashList) {
    let input_term = &terms[node.input_term_idx];
    let result_term = &terms[node.result_term_idx];
    let parent0 = &proof[node.parent0];

    assert!(is_eval_rule(parent0.rule));

    let parent0_e_idx = parent0.input_term_idx;
    let parent0_v_idx = parent0.result_term_idx;

    let node_e_idx = input_term.right;
    let node_v_idx = result_term.right;

    assert!(hash_list_subset(
        node.ctx_idx,
        parent0.ctx_idx,
        node.parent0_quot,
        contexts
    ));

    // lift in body
    //assert!(parent0.num_lifts == node.num_lifts + 1);
    // TODO: might need "blank" binding?
    // ensure contexts the same
    //assert!(hash_list_permutation(node.ctx_idx, parent0.ctx_idx, context))

    assert!(input_term.kind == EXPR_LAM);
    assert!(result_term.kind == EXPR_LAM);
    assert!(parent0_e_idx == node_e_idx);
    assert!(parent0_v_idx == node_v_idx);

    // ensure name correct
    assert!(input_term.name == node.max_binding);
}

fn check_eval_pi(
    node: &ExpRule,
    proof: &[ExpRule],
    terms: &[ExpTerm],
    contexts: &HashList,
    db_axiom_rev_map: &HashMap<(usize, usize), String>,
    db_ind_rev_map: &HashMap<usize, String>,
) {
    let input_term = &terms[node.input_term_idx];
    let result_term = &terms[node.result_term_idx];
    let parent0 = &proof[node.parent0];
    let parent1 = &proof[node.parent1];

    // get info from result pi type, and ensure well formedness
    assert!(result_term.kind == EXPR_PI || result_term.kind == EXPR_LAM);
    assert!(input_term.kind == result_term.kind);
    assert!(is_eval_rule(parent0.rule));
    let pi_p_idx = input_term.left;
    let pi_pp_idx = input_term.right;

    // get info from result pi type, and ensure well formedness
    assert!(is_eval_rule(parent1.rule));
    let pi_t_idx = result_term.left;
    let pi_tp_idx = result_term.right;

    // get info from the parent0 rule
    let parent0_p_idx = parent0.input_term_idx;
    let parent0_t_idx = parent0.result_term_idx;

    // get info from the parent1 rule
    let parent1_pp_idx = parent1.input_term_idx;
    let parent1_tp_idx = parent1.result_term_idx;

    // context subsets
    assert!(hash_list_subset(
        node.ctx_idx,
        parent0.ctx_idx,
        node.parent0_quot,
        contexts
    ));
    // TODO: check for additional value in ctx_idx
    //assert!(
    //    hash_list_subset(node.ctx_idx, parent1.ctx_idx, node.parent1_quot, contexts),
    //    "got ctx: {} and {} and {}",
    //    contexts.to_string(node.ctx_idx),
    //    contexts.to_string(parent1.ctx_idx),
    //    contexts.to_string(node.parent1_quot)
    //);

    // no lift in type
    //assert!(parent0.num_lifts == node.num_lifts);
    // lift in body
    //assert!(parent1.num_lifts == node.num_lifts + 1);

    // TODO: might need "blank" binding
    // ensure contexts the same
    //assert!(hash_list_permutation(
    //    node.ctx_idx,
    //    parent0.ctx_idx,
    //    context
    //));
    //assert!(hash_list_permutation(
    //    node.ctx_idx,
    //    parent1.ctx_idx,
    //    context
    //));

    // check rules
    println!(
        "got {} \n\n{}",
        term_to_string(parent0_p_idx, terms, db_axiom_rev_map, db_ind_rev_map),
        term_to_string(pi_p_idx, terms, db_axiom_rev_map, db_ind_rev_map),
    );
    assert!(parent0_t_idx == pi_t_idx);
    assert!(parent0_p_idx == pi_p_idx);

    assert!(
        parent1_pp_idx == pi_pp_idx,
        "Fail: {} {}",
        term_to_string(parent1_pp_idx, terms, db_axiom_rev_map, db_ind_rev_map),
        term_to_string(pi_pp_idx, terms, db_axiom_rev_map, db_ind_rev_map),
    );
    assert!(parent1_tp_idx == pi_tp_idx);

    assert!(input_term.name == node.max_binding);
}

// ============================================================================
// e => n   e' => v'
// ---------------------------------
//  e e' => n v'
// ============================================================================
fn check_eval_app(node: &ExpRule, proof: &[ExpRule], terms: &[ExpTerm], contexts: &HashList) {
    let input_term = &terms[node.input_term_idx];
    let result_term = &terms[node.result_term_idx];
    let parent0 = &proof[node.parent0];
    let parent1 = &proof[node.parent1];

    println!("parent0: {}", parent0.rule);
    assert!(is_eval_rule(parent0.rule));
    assert!(is_eval_rule(parent1.rule));

    let parent0_e_idx = parent0.input_term_idx;
    let parent0_n_idx = parent0.result_term_idx;
    let parent1_ep_idx = parent1.input_term_idx;
    let parent1_vp_idx = parent1.result_term_idx;

    let node_e_idx = input_term.left;
    let node_ep_idx = input_term.right;
    let node_n_idx = result_term.left;
    let node_vp_idx = result_term.right;

    // maintain number of lifts
    //res = res && node.num_lifts == parent0.num_lifts && parent0.num_lifts == parent1.num_lifts

    // check context same
    assert!(
        hash_list_subset(node.ctx_idx, parent0.ctx_idx, node.parent0_quot, contexts),
        "FAIL: {} {} {}",
        contexts.to_string(node.ctx_idx),
        contexts.to_string(parent0.ctx_idx),
        contexts.to_string(node.parent0_quot)
    );
    assert!(hash_list_subset(
        node.ctx_idx,
        parent1.ctx_idx,
        node.parent1_quot,
        contexts
    ));

    assert!(input_term.kind == EXPR_APP);
    assert!(result_term.kind == EXPR_APP);
    assert!(parent0_e_idx == node_e_idx);
    assert!(parent1_ep_idx == node_ep_idx);
    assert!(parent0_n_idx == node_n_idx);
    assert!(parent1_vp_idx == node_vp_idx);
}

//                            e => v      v:C, b => v'
//                          --------------------------- (p1)
// C: f => \ -> b                 v:C, b => v'
// --------------------------------------------- (p2)
//                C: f e => vp
fn check_eval_app_lam(
    node: &ExpRule,
    proof: &[ExpRule],
    lifts: &[ExpLift],
    terms: &[ExpTerm],
    contexts: &HashList,
) {
    let parent0 = &proof[node.parent0];
    let parent1 = &proof[node.parent1];

    // consequent is correct
    let input_term = &terms[node.input_term_idx];
    let result_term = &terms[node.result_term_idx];

    let node_f_idx = input_term.left;
    let node_e_idx = input_term.right;
    let node_vpp_idx = node.result_term_idx;

    assert!(input_term.kind == EXPR_APP);

    // parent 0 is correct
    assert!(is_eval_rule(parent0.rule));
    let parent0_result_term = &terms[parent0.result_term_idx];

    let parent0_f_idx = parent0.input_term_idx;
    let parent0_b_idx = parent0_result_term.right;

    assert!(parent0_result_term.kind == EXPR_LAM);
    assert!(node_f_idx == parent0_f_idx);
    assert!(
        hash_list_subset(node.ctx_idx, parent0.ctx_idx, node.parent0_quot, contexts),
        "failed subset check: {} = {} U {}",
        contexts.to_string(node.ctx_idx),
        contexts.to_string(parent0.ctx_idx),
        contexts.to_string(node.parent0_quot)
    );

    assert!(parent1.rule == RULE_EVAL_APP_LAM_SUB);
    assert!(parent1.extra == node_e_idx);
    assert!(parent1.input_term_idx == parent0_b_idx);
    assert!(parent1.result_term_idx == node_vpp_idx);
}

//                            e => v      v:C, b => v'
//                          --------------------------- (p1)
// C: f => \ -> b                 C, b => v'
// --------------------------------------------- (p2)
//                C: f e => vp
fn check_eval_app_lam_sub(
    node: &ExpRule,
    proof: &[ExpRule],
    lifts: &[ExpLift],
    terms: &[ExpTerm],
    contexts: &HashList,
) {
    let parent0 = &proof[node.parent0];
    let parent1 = &proof[node.parent1];
    let lift = &lifts[node.lift_rule];

    // consequent is correct
    let input_term = &terms[node.input_term_idx];
    let result_term = &terms[node.result_term_idx];
    let node_e_idx = node.extra;
    let node_b_idx = node.input_term_idx;
    let node_vpp_idx = node.result_term_idx;

    let parent0_e_idx = parent0.input_term_idx;
    let parent0_v_idx = parent0.result_term_idx;
    let parent1_b_idx = parent1.input_term_idx;
    let parent1_vp_idx = parent1.result_term_idx;

    let lift_vp_idx = lift.input_term_idx;
    let lift_vpp_idx = lift.result_term_idx;

    assert!(node_e_idx == parent0_e_idx);
    assert!(node_b_idx == parent1_b_idx);
    assert!(
        parent1_vp_idx == lift_vp_idx,
        "got: {} {}",
        parent1_vp_idx,
        lift_vp_idx
    );
    assert!(node_vpp_idx == lift_vpp_idx);

    //assert!(hah
}

// gross but whatever...
// a => b         b => c
// ---------------------
//         a => c
fn check_eval_transitive(node: &ExpRule, proof: &[ExpRule], terms: &[ExpTerm]) {
    let parent0 = &proof[node.parent0];
    let parent1 = &proof[node.parent1];

    assert!(parent0.input_term_idx == node.input_term_idx);
    assert!(parent1.input_term_idx == parent0.result_term_idx);
    assert!(parent1.result_term_idx == node.result_term_idx);

    assert!(is_eval_rule(parent0.rule));
    assert!(is_eval_rule(parent1.rule));

    // TODO: CHECK CTXS and stuff
}

//
// ---------------------
//  0)|- f e => e
//
//  n-1 |- f => e'
// ---------------------
//  n |- f e => e'
fn check_get_arg(node: &ExpRule, proof: &[ExpRule], terms: &[ExpTerm]) {
    let input_term = &terms[node.input_term_idx];
    let result_term = &terms[node.result_term_idx];

    // no context for these rules...is okay to ignore
    let count = node.ctx_idx;

    assert!(input_term.kind == EXPR_APP);

    if count == 0 {
        assert!(node.result_term_idx == input_term.right);
    } else {
        let parent0 = &proof[node.parent0];

        assert!(parent0.rule == RULE_GET_ARG);
        assert!(parent0.ctx_idx == count - 1);
        assert!(parent0.input_term_idx == input_term.left);
        assert!(parent0.result_term_idx == node.result_term_idx);
    }
}

// No need to worry about Inductive global params because we are walking
// backwards, not forwards...
//
//          f.tlf == ind_i
// --------------------------------                 (apply_base)
// elim_apply 0 0 e_i elim f => e_i

//  elim_apply (nnr-1) 0 e_i rec f => f'
// --------------------------------------           (apply_nonrec)
//  elim_apply nnr 0 e_i (f e) => (f' e)

// elim_apply (nr-1) e_i rec f => f'
// ----------------------------------------------    (apply_rec)
//  elim_apply nnr nr e_i (f e) => (f' (rec e))
fn check_apply_elim(node: &ExpRule, proof: &[ExpRule], terms: &[ExpTerm], inductives: &[ExpInd]) {
    let input_term = &terms[node.input_term_idx];
    let result_term = &terms[node.result_term_idx];

    let parent0 = &proof[node.parent0];

    // use some random unused fields for extra data...
    let num_nonrec_args = node.extra;
    let num_rec_args = node.extra2;
    let rec = node.extra3;
    let e_i = node.extra4;

    // TODO: get and check e_i
    let node_f = input_term.left;
    let node_e = input_term.right;

    let node_fp = result_term.left;
    let node_ep = result_term.right;

    if num_nonrec_args == 0 && num_rec_args == 0 {
        //assert!(input_term.kind == EXPR_IND_CTOR);
        //assert!(input_term.left == IND);
        assert!(node.result_term_idx == e_i);
    } else if num_rec_args == 0 {
        assert!(parent0.rule == RULE_APPLY_ELIM);
        assert!(parent0.extra == num_nonrec_args - 1);
        assert!(parent0.extra2 == 0);

        assert!(result_term.kind == EXPR_APP);

        //  f == f
        assert!(parent0.input_term_idx == node_f);
        //  f' == f'
        assert!(parent0.result_term_idx == result_term.left);
        // e == e
        assert!(input_term.right == result_term.right);
    } else {
        assert!(parent0.rule == RULE_APPLY_ELIM);
        assert!(parent0.extra == num_nonrec_args);
        assert!(parent0.extra2 == num_rec_args - 1);

        assert!(result_term.kind == EXPR_APP);

        //  f == f
        assert!(parent0.input_term_idx == node_f);
        //  f' == f'
        assert!(parent0.result_term_idx == result_term.left);

        let result_right = &terms[result_term.right];

        assert!(result_right.kind == EXPR_APP);
        assert!(result_right.left == rec);

        // e == e
        assert!(result_right.right == input_term.right);
    }
}

// elim_apply nnr nr e_i e => e'  C |- e' => e''
// ----------------------------------------
//     C |- e => e''
fn check_apply_elim_eval(
    node: &ExpRule,
    proof: &[ExpRule],
    terms: &[ExpTerm],
    inductives: &[ExpInd],
) {
    let input_term = &terms[node.input_term_idx];
    let result_term = &terms[node.result_term_idx];

    let parent0 = &proof[node.parent0];
    let parent1 = &proof[node.parent1];

    let node_e = node.input_term_idx;
    let node_epp = node.result_term_idx;

    let p0_e = parent0.input_term_idx;
    let p0_ep = parent0.result_term_idx;

    let p1_ep = parent1.input_term_idx;
    let p1_epp = parent1.result_term_idx;

    assert!(parent0.rule == RULE_APPLY_ELIM);
    assert!(is_eval_rule(parent1.rule));

    assert!(node_e == p0_e);
    assert!(node_epp == p1_epp);
    assert!(p0_ep == p1_ep);

    // TODO: need to check elim_apply args....
    assert!(parent0.extra == node.extra);
    assert!(parent0.extra2 == node.extra2);
    assert!(parent0.extra3 == node.extra3);

    // ensure nnr, nr, rec, and ei are correct in parent0
    // SEE constructors for these ExpRules for explanation
    assert!(node.extra4 == parent0.extra4);
}

//  (f is ind_elim) (get_arg f (ty_args + 1 + i) => e_i) (f has enough args)   (e is ind_i) (e :: Ind)  (elim_apply_eval nnr nr e_i e => e')
//  ------------------------------------------------------------------------   -------------------------------------------------------------
//              C |- f ^ e_i, extra: i                                                          C |- e ^ e', extra: i, extra2: e_i, extra3: f
// ------------------------------------------------------------------------------------------------------------------------------------------------
//                                                       C |- f e => e'
fn check_eval_ind(node: &ExpRule, proof: &[ExpRule], terms: &[ExpTerm], inductives: &[ExpInd]) {
    // TODO: finish this
    let input_term = &terms[node.input_term_idx];
    let result_term = &terms[node.result_term_idx];

    let parent0 = &proof[node.parent0];
    let parent1 = &proof[node.parent1];
    let inductive = &inductives[node.inductive];

    assert!(parent0.rule == RULE_EVAL_IND_SUB1);
    assert!(parent0.input_term_idx == input_term.left);
    assert!(parent0.inductive == node.inductive);
    //assert!(parent0.extra == inductive.elim_argc - (inductive.num_params + ind_rule_index + 2));

    assert!(parent1.rule == RULE_EVAL_IND_SUB2);
    assert!(parent1.input_term_idx == input_term.right);
    assert!(parent1.result_term_idx == node.result_term_idx);
    assert!(parent1.inductive == node.inductive);
    //assert!(parent1.extra == inductive.elim_argc - (inductive.num_params + ind_rule_index + 2));
    assert!(parent1.extra2 == parent0.result_term_idx);

    // TODO:
    //let parent2 = &proof[node.parent2]; // get_arg
    //let parent3 = &proof[node.parent3]; // elim_apply_eval

    //let inductive = &inductives[node.inductive];

    //let parent0_fp = parent0.result_term_idx;
    //let fp_term = &terms[parent0_fp];

    //let parent1_ep = parent1.result_term_idx;
    //let ep_term = &terms[parent1_ep];
    //let ep_tlf_term = &terms[ep_term.top_level_func];

    //assert!(is_eval_rule(parent0.rule));

    //// TODO: ensure that e' is valid Ind construction...
    //assert!(is_eval_rule(parent1.rule));

    //// ensure f' is the induction eliminator
    //// TODO: this is wrong... fix...
    ////assert!(fp_term.top_level_func == inductive.elim);

    //// ensure f' has the correct number of args
    //// TODO: ensure the argc is correct
    ////assert!(fp_term.argc == inductive.elim_argc);

    //// ensure e' is an induction ctor
    //println!("ep_tlf_term: {}", ep_tlf_term.kind);
    //assert!(ep_tlf_term.kind == EXPR_IND_CTOR);
    //assert!(ep_tlf_term.ind == node.inductive); // the inductive is correct
    //let ind_rule_index = ep_tlf_term.ind_ctor;

    //// ensure result of parent2 is elim
    //assert!(parent2.rule == RULE_GET_ARG);
    //// the arg number is correct
    //println!(
    //    "ctx_idx: {} {}",
    //    parent2.ctx_idx,
    //    inductive.num_rules - ind_rule_index + 2
    //);
    //assert!(parent2.ctx_idx == inductive.elim_argc - (inductive.num_params + ind_rule_index + 2));
    //let e_i = parent2.result_term_idx;

    //// parent 3 is elim apply eval
    //assert!(parent3.rule == RULE_APPLY_ELIM_EVAL);
    //// ensure nnr, nr, rec, and ei are correct in parent3
    //// SEE constructors for these ExpRules for explanation
    //assert!(inductive.rule_nnrs[ind_rule_index] == parent3.parent2); // nnr
    //assert!(inductive.rule_nrs[ind_rule_index] == parent3.parent3); // nr
    //assert!(input_term.left == parent3.parent0_quot); // rec
    //assert!(e_i == parent3.parent1_quot); // e_i

    //assert!(parent3.input_term_idx == parent1_ep);
    //let parent3_epp = parent3.result_term_idx;

    //assert!(node.result_term_idx == parent3_epp);

    //// TODO: check contexts....
}

//  (f is ind_elim) (get_arg f (ty_args + 1 + i) => e_i) (f has enough args)
//  ------------------------------------------------------------------------
//              C |- f ^ e_i
fn check_eval_ind_sub1(
    node: &ExpRule,
    proof: &[ExpRule],
    terms: &[ExpTerm],
    inductives: &[ExpInd],
) {
    let input_term = &terms[node.input_term_idx];
    let result_term = &terms[node.result_term_idx];

    let parent0 = &proof[node.parent0];
    let parent1 = &proof[node.parent1];
    let inductive = &inductives[node.inductive];
    let ind_rule_index = node.ind_rule;

    // TODO: check f is ind elim

    assert!(parent1.rule == RULE_GET_ARG);
    assert!(parent1.extra == inductive.elim_argc - (inductive.num_params + ind_rule_index + 2));
}

//(e is ind_i) (e :: Ind)  (elim_apply_eval nnr nr e_i rec e => e')
//-------------------------------------------------------------
//                 C |- e ^ e', extra: i, extra2: e_i, extra3: f
fn check_eval_ind_sub2(
    node: &ExpRule,
    proof: &[ExpRule],
    terms: &[ExpTerm],
    inductives: &[ExpInd],
    nnrs: &HashList,
    nrs: &HashList,
) {
    let input_term = &terms[node.input_term_idx];
    let result_term = &terms[node.result_term_idx];

    let parent0 = &proof[node.parent0];
    let parent1 = &proof[node.parent1];
    let inductive = &inductives[node.inductive];
    let ind_rule_index = node.extra;
    let elim = node.extra2;

    let e_tlf = &terms[input_term.top_level_func];
    assert!(e_tlf.kind == EXPR_IND_CTOR);
    assert!(e_tlf.ind == node.inductive);
    assert!(
        e_tlf.ind_ctor == ind_rule_index,
        "got {} {}",
        e_tlf.ind_ctor,
        ind_rule_index
    );

    assert!(parent1.rule == RULE_APPLY_ELIM_EVAL);
    assert!(hash_list_contains(
        inductive.rule_nnrs,
        ind_rule_index,
        parent1.extra,
        node.ind_nnr_quot,
        nnrs
    ));
    assert!(hash_list_contains(
        inductive.rule_nrs,
        ind_rule_index,
        parent1.extra2,
        node.ind_nr_quot,
        nrs
    ));
    assert!(node.extra3 == parent1.extra3); // rec // TODO: move to extra3
    assert!(node.extra2 == parent1.extra4); // rec // TODO: move to extra3
    assert!(parent1.input_term_idx == node.input_term_idx);
    assert!(parent1.result_term_idx == node.result_term_idx);
}

// TODO: This is wrong....
//       need to have either another index for top level ax terms,
//       or have a map between axiom indices and top level terms...
fn check_type_ax(node: &ExpRule, proof: &[ExpRule], lifts: &[ExpLift], max_ax: usize) {
    // let parent0 = &lifts[node.lift_rule];
    // //println!("ax term is: {}, max ax: {}", parent0.input_term_idx, max_ax);
    // assert!(parent0.input_term_idx < max_ax);
    // assert!(parent0.max_binding == node.max_binding);
    // //assert!(parent0.rule == RULE_LIFT);
    // assert!(node.result_term_idx == parent0.result_term_idx);
}

// b :: T   T :: Prop
// -----------------------
//      b ^ Prop, extra: T
fn check_proof_irrel_sub1(
    node: &ExpRule,
    proof: &[ExpRule],
    terms: &[ExpTerm],
    db_axiom_rev_map: &HashMap<(usize, usize), String>,
    db_ind_rev_map: &HashMap<usize, String>,
) {
    let input_term = &terms[node.input_term_idx];
    let result_term = &terms[node.result_term_idx];

    let parent0 = &proof[node.parent0];
    let parent1 = &proof[node.parent1];

    assert!(is_type_rule(parent0.rule));
    assert!(is_type_rule(parent1.rule));

    assert!(parent0.input_term_idx == node.input_term_idx);
    assert!(parent0.result_term_idx == parent1.input_term_idx);
    assert!(parent0.result_term_idx == node.extra);
    assert!(parent1.result_term_idx == node.result_term_idx);

    assert!(result_term.kind == EXPR_SORT);
    assert!(result_term.name == 0);
}

//  a :: T   b :: T   T :: Prop
// -----------------------------
//              a => b
//
fn check_proof_irrel(
    node: &ExpRule,
    proof: &[ExpRule],
    terms: &[ExpTerm],
    db_axiom_rev_map: &HashMap<(usize, usize), String>,
    db_ind_rev_map: &HashMap<usize, String>,
) {
    let parent0 = &proof[node.parent0];
    let parent1 = &proof[node.parent1];

    assert!(is_type_rule(parent0.rule));
    assert!(parent1.rule == RULE_PROOF_IRREL_SUB1);

    assert!(parent0.input_term_idx == node.input_term_idx);
    assert!(parent0.result_term_idx == parent1.extra);
    assert!(parent1.input_term_idx == node.result_term_idx);
}

// TODO: ensure contexts correct here...
//  a :: T   T => T'
// ------------------
//      a :: T'
//
fn check_eval_type(
    node: &ExpRule,
    proof: &[ExpRule],
    terms: &[ExpTerm],
    db_axiom_rev_map: &HashMap<(usize, usize), String>,
    db_ind_rev_map: &HashMap<usize, String>,
) {
    let parent0 = &proof[node.parent0];
    let parent1 = &proof[node.parent1];

    assert!(is_type_rule(parent0.rule));
    assert!(is_eval_rule(parent1.rule));

    let node_a_idx = node.input_term_idx;
    let node_Tp_idx = node.result_term_idx;

    let p0_a_idx = parent0.input_term_idx;
    let p0_T_idx = parent0.result_term_idx;

    let p1_T_idx = parent1.input_term_idx;
    let p1_Tp_idx = parent1.result_term_idx;

    assert!(node_a_idx == p0_a_idx);
    println!(
        "F: {} :: {}\nT: {} => {}",
        term_to_string(p0_a_idx, terms, db_axiom_rev_map, db_ind_rev_map),
        term_to_string(p0_T_idx, terms, db_axiom_rev_map, db_ind_rev_map),
        term_to_string(p1_T_idx, terms, db_axiom_rev_map, db_ind_rev_map),
        term_to_string(p1_Tp_idx, terms, db_axiom_rev_map, db_ind_rev_map),
    );
    assert!(p0_T_idx == p1_T_idx);
    assert!(p1_Tp_idx == node_Tp_idx);
}

// TODO: move
fn check_type_ind(
    node: &ExpRule,
    proof: &[ExpRule],
    lifts: &[ExpLift],
    terms: &[ExpTerm],
    inductives: &[ExpInd],
) {
    let input_term = &terms[node.input_term_idx];
    let result_term = &terms[node.result_term_idx];

    let parent0 = &lifts[node.lift_rule];

    assert!(input_term.kind == EXPR_IND);
    assert!(inductives[input_term.ind].ty == parent0.input_term_idx);
    assert!(node.result_term_idx == parent0.result_term_idx);
}

fn check_type_ind_ctor(
    node: &ExpRule,
    proof: &[ExpRule],
    lifts: &[ExpLift],
    terms: &[ExpTerm],
    inductives: &[ExpInd],
    rules: &HashList,
) {
    let input_term = &terms[node.input_term_idx];
    let result_term = &terms[node.result_term_idx];

    let parent0 = &lifts[node.lift_rule];
    //assert!(parent0.rule == RULE_LIFT);

    let ind = &inductives[input_term.ind];
    //let rule_ty = ind.rules[input_term.ind_ctor];

    assert!(input_term.kind == EXPR_IND_CTOR);
    //assert!(rule_ty == parent0.input_term_idx);
    assert!(hash_list_contains(
        ind.rules,
        input_term.ind_ctor,
        parent0.input_term_idx,
        node.ind_ctor_quot,
        rules,
    ));
    assert!(node.result_term_idx == parent0.result_term_idx);
}

//
// -------------------------------------
//  ind_pref 0 elim (Pi x: A. elim) B
//
//            ind_pref (n-1) elim B C
// -------------------------------------------
//  ind_pref n elim (Pi x: A. B) (Pi x: A. C)
fn check_ind_prefix(
    node: &ExpRule,
    proof: &[ExpRule],
    terms: &[ExpTerm],
    inductives: &[ExpInd],
    db_axiom_rev_map: &HashMap<(usize, usize), String>,
    db_ind_rev_map: &HashMap<usize, String>,
) {
    let input_term = &terms[node.input_term_idx];
    let result_term = &terms[node.result_term_idx];

    let parent0 = &proof[node.parent0];

    // don't use contexts...so use them for other things
    let n = node.extra;
    let elim = node.extra2;

    if n == 0 {
        assert!(input_term.kind == EXPR_PI);
        assert!(input_term.right == elim);

        // TODO: check motive sort here too ...... hmmmmmmmmmmmmmm
    } else {
        assert!(input_term.kind == EXPR_PI);
        assert!(result_term.kind == EXPR_PI);
        assert!(input_term.left == result_term.left);

        assert!(parent0.rule == RULE_IND_PREFIX);
        assert!(parent0.extra == n - 1);
        assert!(parent0.extra2 == elim);
    }
}

// TODO: add type check of ind_ty :: motive_sort in here -> is this always true?
//
//  ind_pref num_params elim ty ind_ty            lift ind_ty ind_ty'
// ----------------------------------------------------------------------------
//        C |- ind_rec ind motive_sort :: ind_ty'
fn check_type_ind_rec(
    node: &ExpRule,
    proof: &[ExpRule],
    lifts: &[ExpLift],
    terms: &[ExpTerm],
    inductives: &[ExpInd],
) {
    let input_term = &terms[node.input_term_idx];
    let result_term = &terms[node.result_term_idx];

    let inductive = &inductives[input_term.ind];

    let parent0 = &proof[node.parent0];
    let parent1 = &lifts[node.lift_rule];

    assert!(parent0.rule == RULE_IND_PREFIX);
    assert!(parent0.input_term_idx == parent1.input_term_idx);
    assert!(parent0.result_term_idx == inductive.ty);
    assert!(parent0.extra == inductive.num_params);
    assert!(parent0.extra2 == inductive.rec_body);

    assert!(parent1.result_term_idx == node.result_term_idx);
}

//   a :: Pi x:A.B   a x *
// -------------------
//    a => \x . a x
//fn check_eval_eta(node: &ExpRule, proof: &[ExpRule], terms: &[ExpTerm], inductives: &[ExpInd]) {
//    let input_term = &terms[node.input_term_idx];
//    let result_term = &terms[node.result_term_idx];
//
//    let parent0 = &proof[node.parent0];
//    let parent0_res = &terms[parent0.result_term_idx];
//
//    assert!(result_term.kind == EXPR_LAM);
//    assert!(app_res.kind == EXPR_APP);
//    assert!(app_res.left == node.input_term_idx);
//    assert!(app_res.right == node.input_term_idx);
//
//    // TODO: check (a x) well formed...
//}

fn check_axioms(axioms: &[ExpTerm], terms: &[ExpTerm]) {
    for i in 0..axioms.len() {
        assert_eq!(axioms[i], terms[i]);
    }
}

fn check_terms(terms: &[ExpTerm]) {
    for i in 0..terms.len() {
        let term = &terms[i];
        let f = &terms[term.left];
        if term.kind == EXPR_APP {
            assert!(term.top_level_func == f.top_level_func);
        } else {
            assert!(term.top_level_func == i);
        }
    }
}

/// For now, we will just panic if verification fails.
pub fn simulate(
    input: ZkInput,
    check_res: bool,
    db_axiom_rev_map: &HashMap<(usize, usize), String>,
    db_ind_rev_map: &HashMap<usize, String>,
) {
    //println!(
    //    "simulation size: {} nodes, {} terms, {} contexts, {} axioms",
    //    input.rules.len(),
    //    input.terms.len(),
    //    input.contexts.nodes.len(),
    //    input.public_terms.len()
    //);

    // TODO: hash lists well formed
    //
    // check axiom terms ...
    let proof = &input.rules;
    let lifts = &input.lifts;
    let contexts = &input.contexts;
    let terms = &input.terms;
    let public_terms = &input.public_terms;
    let axioms = input.axioms;
    let expected_type = input.expected_type;
    let proving_rule = input.proving_rule;
    let inductives = &input.inductives;
    let rules = &input.ind_rules;
    let nnrs = &input.ind_nnrs;
    let nrs = &input.ind_nrs;

    // TODO: axiom hash map....

    check_terms(terms);
    check_axioms(public_terms, terms);

    if check_res {
        assert!(
            proof[proving_rule].result_term_idx == expected_type,
            "Expected: {:?}, Got: {:?}",
            term_to_string(expected_type, &terms, db_axiom_rev_map, db_ind_rev_map),
            term_to_string(
                proof[proving_rule].result_term_idx,
                &terms,
                db_axiom_rev_map,
                db_ind_rev_map
            ),
        );
    }

    for i in 0..input.lifts.len() {
        let lift = &lifts[i];
        check_lift(lift, lifts, terms, db_axiom_rev_map);
    }

    for i in 0..input.rules.len() {
        let node = &proof[i];

        match node.rule {
            RULE_EVAL_ID => check_eval_id(node, terms),
            RULE_EVAL_VAR => check_eval_var(
                node,
                proof,
                lifts,
                terms,
                contexts,
                db_axiom_rev_map,
                db_ind_rev_map,
            ),
            //RULE_EVAL_LAM => check_eval_lam(node, proof, terms, contexts),
            RULE_EVAL_PI => check_eval_pi(
                node,
                proof,
                terms,
                contexts,
                db_axiom_rev_map,
                db_ind_rev_map,
            ),
            RULE_EVAL_APP => check_eval_app(node, proof, terms, contexts),
            RULE_EVAL_APP_LAM => check_eval_app_lam(node, proof, lifts, terms, contexts),
            RULE_EVAL_APP_LAM_SUB => check_eval_app_lam_sub(node, proof, lifts, terms, contexts),
            // EVAL APP PI????????????
            RULE_TYPE_VAR => check_type_var(node, proof, lifts, terms, contexts, db_axiom_rev_map),
            RULE_TYPE_SORT => check_type_sort(node, proof, terms),
            RULE_TYPE_LAM => check_type_lam(node, proof, terms),
            RULE_TYPE_PI => check_type_pi(node, proof, terms, contexts),
            RULE_TYPE_PI_SUB => check_type_pi_sub(node, proof, terms, contexts),
            RULE_TYPE_APP => check_type_app(
                node,
                proof,
                lifts,
                terms,
                contexts,
                db_axiom_rev_map,
                db_ind_rev_map,
            ),
            RULE_TYPE_APP_SUB => check_type_app_sub(
                node,
                proof,
                terms,
                contexts,
                db_axiom_rev_map,
                db_ind_rev_map,
            ),
            RULE_TYPE_AX => check_type_ax(node, proof, lifts, 0),

            //RULE_LIFT => check_lift(node, proof, terms, db_axiom_rev_map),
            RULE_PROOF_IRREL => {
                check_proof_irrel(node, proof, terms, db_axiom_rev_map, db_ind_rev_map)
            }
            RULE_PROOF_IRREL_SUB1 => {
                check_proof_irrel_sub1(node, proof, terms, db_axiom_rev_map, db_ind_rev_map)
            }
            RULE_EVAL_TYPE => check_eval_type(node, proof, terms, db_axiom_rev_map, db_ind_rev_map),

            RULE_EVAL_IND => check_eval_ind(node, proof, terms, inductives),
            RULE_EVAL_IND_SUB1 => check_eval_ind_sub1(node, proof, terms, inductives),
            RULE_EVAL_IND_SUB2 => check_eval_ind_sub2(node, proof, terms, inductives, nnrs, nrs),
            RULE_GET_ARG => check_get_arg(node, proof, terms),
            RULE_APPLY_ELIM => check_apply_elim(node, proof, terms, inductives),
            RULE_APPLY_ELIM_EVAL => check_apply_elim_eval(node, proof, terms, inductives),

            RULE_TYPE_IND => check_type_ind(node, proof, lifts, terms, inductives),
            RULE_TYPE_IND_CTOR => check_type_ind_ctor(node, proof, lifts, terms, inductives, rules),
            RULE_TYPE_IND_REC => check_type_ind_rec(node, proof, lifts, terms, inductives),

            RULE_IND_PREFIX => check_ind_prefix(
                node,
                proof,
                terms,
                inductives,
                db_axiom_rev_map,
                db_ind_rev_map,
            ),

            RULE_EVAL_TRANSITIVE => check_eval_transitive(node, proof, terms),
            r => panic!("Unknown rule {}!", r),
        }
    }
}
