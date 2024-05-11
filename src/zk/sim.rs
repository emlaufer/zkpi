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
}

fn imax(i: usize, j: usize) -> usize {
    if j == 0 {
        0
    } else {
        max(i, j)
    }
}

fn check_context(node: &ExpRule, parent: &ExpRule, quot: usize, contexts: &HashList) -> bool {
    return hash_list_subset(node.ctx_idx, parent.ctx_idx, quot, contexts);
}

fn check_eval_parent(parent: &ExpRule, expected_input: usize, expected_result: usize) -> bool {
    let res = if parent.rule == RULE_EVAL_ID {
        expected_input == expected_result
    } else {
        parent.input_term_idx == expected_input && parent.result_term_idx == expected_result
    };
    res
}

fn check_parent_lift(node: &ExpRule, lift_node: &ExpLift) -> bool {
    return lift_node.max_binding == node.max_binding
        && lift_node.result_term_idx == node.result_term_idx;
}

fn get_eval_parent_res(parent: &ExpRule, expected_input: usize) -> usize {
    if parent.rule == RULE_EVAL_ID {
        expected_input
    } else {
        parent.result_term_idx
    }
}

fn check_expected_binding(parent: &ExpRule, expected_max_binding: usize) -> bool {
    return if parent.rule == RULE_EVAL_ID
        || parent.rule == RULE_TYPE_SORT
        || parent.rule == RULE_EVAL_SORT
    {
        true
    } else {
        parent.max_binding == expected_max_binding
    };
}

fn get_eval_parent_input(parent: &ExpRule, expected_result: usize) -> usize {
    if parent.rule == RULE_EVAL_ID {
        expected_result
    } else {
        parent.input_term_idx
    }
}

pub fn is_eval_rule(rule: usize) -> bool {
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
        || rule == RULE_EVAL_TRANSITIVE
        || rule == RULE_EVAL_PROJ
        || rule == RULE_EVAL_PROJ_SIMPL;
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
        || rule == RULE_TYPE_IND_REC
        || rule == RULE_TYPE_PROJ;
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
    assert!(check_parent_lift(node, lift_node));
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
    assert!(check_expected_binding(parent0, node.max_binding));
    assert!(check_expected_binding(parent1, node.max_binding));

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
    assert!(check_eval_parent(
        parent1,
        input_term.right,
        node.result_term_idx
    ));
    assert!(input_term.kind == EXPR_PI);

    assert!(parent0.input_term_idx == node.extra);
    assert!(parent0.result_term_idx == input_term.left);
    assert!(hash_list_subset(
        node.ctx_idx,
        parent0.ctx_idx,
        node.parent0_quot,
        contexts
    ));
    // TODO: ctx add (name, a)
    //assert!(hash_list_subset(
    //    node.ctx_idx,
    //    parent1.ctx_idx,
    //    node.parent1_quot,
    //    contexts
    //));
    assert!(check_expected_binding(parent0, node.max_binding));
    assert!(check_expected_binding(parent1, node.max_binding + 1));
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

    assert!(check_expected_binding(parent0, node.max_binding + 1));
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
    assert!(parent0.ctx_idx == node.ctx_idx);
    assert!(parent0.input_term_idx == input_term.left);

    assert!(parent1.input_term_idx == input_term.right);

    // ensure node well formed
    assert!(input_term.name == node.max_binding);
    assert!(result_term.name == imax(sort_i.name, sort_j.name));
    assert!(check_expected_binding(parent0, node.max_binding));
    assert!(check_expected_binding(parent1, node.max_binding + 1));
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

    assert!(is_eval_rule(parent0.rule));
    assert!(check_eval_parent(
        parent0,
        node.input_term_idx,
        parent1.input_term_idx
    ));
    assert!(node.result_term_idx == parent1.result_term_idx);
    assert!(node.extra == parent1.input_term_idx);
    assert!(check_expected_binding(parent0, node.max_binding));
    assert!(check_expected_binding(parent1, node.max_binding));
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
    let input_term = &terms[node.input_term_idx];
    let lift_node = &lifts[node.lift_rule];

    assert!(hash_list_contains(
        node.ctx_idx,
        input_term.name,
        lift_node.input_term_idx,
        HashList::EMPTY,
        contexts
    ));
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
    assert!(is_eval_rule(parent0.rule));
    assert!(check_eval_parent(parent0, node_e_idx, node_v_idx));

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
    assert!(is_eval_rule(parent0.rule));
    assert!(is_eval_rule(parent1.rule));
    assert!(check_eval_parent(parent0, pi_p_idx, pi_t_idx));
    assert!(check_eval_parent(parent1, pi_pp_idx, pi_tp_idx));
    assert!(check_expected_binding(parent0, node.max_binding));
    assert!(check_expected_binding(parent1, node.max_binding + 1));
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
    assert!(is_eval_rule(parent0.rule));
    assert!(is_eval_rule(parent1.rule));
    assert!(check_eval_parent(parent0, node_e_idx, node_n_idx));
    assert!(check_eval_parent(parent1, node_ep_idx, node_vp_idx));
    assert!(check_expected_binding(parent0, node.max_binding));
    assert!(check_expected_binding(parent1, node.max_binding));
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
    let parent0_result_idx = get_eval_parent_res(parent0, node_f_idx);
    let parent0_result_term = &terms[parent0_result_idx];

    let parent0_f_idx = parent0.input_term_idx;
    let parent0_b_idx = parent0_result_term.right;

    assert!(check_eval_parent(parent0, node_f_idx, parent0_result_idx));
    assert!(parent0_result_term.kind == EXPR_LAM || parent0_result_term.kind == EXPR_PI);
    assert!(
        hash_list_subset(node.ctx_idx, parent0.ctx_idx, node.parent0_quot, contexts),
        "failed subset check: {} = {} U {}",
        contexts.to_string(node.ctx_idx),
        contexts.to_string(parent0.ctx_idx),
        contexts.to_string(node.parent0_quot)
    );
    assert!(node.ctx_idx == parent1.ctx_idx);

    assert!(parent1.rule == RULE_EVAL_APP_LAM_SUB);
    assert!(parent1.extra == node_e_idx);
    assert!(parent1.input_term_idx == parent0_b_idx);
    assert!(parent1.result_term_idx == node_vpp_idx);
    assert!(check_expected_binding(parent0, node.max_binding));
    assert!(check_expected_binding(parent1, node.max_binding));
}

// collect args
//
// ------------------------------------------------
//              C |- f => C, f
//
//         collect_args(b) => C', b'
// -------------------------------------------------
//          C |- (f e) => (v: C'), b'

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
    let parent0_v_idx = get_eval_parent_res(parent0, node_e_idx);
    let parent1_b_idx = parent1.input_term_idx;
    let parent1_vp_idx = parent1.result_term_idx;

    let lift_vp_idx = lift.input_term_idx;
    let lift_vpp_idx = lift.result_term_idx;

    // TODO: contexts?
    assert!(is_eval_rule(parent0.rule));
    assert!(is_eval_rule(parent1.rule));
    assert!(check_eval_parent(parent0, node_e_idx, parent0_v_idx));
    assert!(check_eval_parent(parent1, node_b_idx, lift_vp_idx));
    assert!(node_vpp_idx == lift_vpp_idx);
    assert!(check_parent_lift(node, lift));

    assert!(check_expected_binding(parent0, node.max_binding));
    assert!(check_expected_binding(parent1, node.max_binding + 1));
}

// gross but whatever...
// a => b         b => c
// ---------------------
//         a => c
fn check_eval_transitive(node: &ExpRule, proof: &[ExpRule], terms: &[ExpTerm]) {
    let parent0 = &proof[node.parent0];
    let parent1 = &proof[node.parent1];

    assert!(is_eval_rule(parent0.rule));
    assert!(is_eval_rule(parent1.rule));
    let parent0_res = get_eval_parent_res(parent0, node.input_term_idx);
    let parent1_inp = get_eval_parent_input(parent1, node.result_term_idx);
    assert!(check_eval_parent(parent0, node.input_term_idx, parent1_inp));
    assert!(check_expected_binding(parent0, node.max_binding));
    assert!(check_expected_binding(parent1, node.max_binding));
    assert!(check_eval_parent(
        parent1,
        parent0_res,
        node.result_term_idx
    ));

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
    let count = node.extra;

    assert!(input_term.kind == EXPR_APP);

    if count == 0 {
        assert!(node.result_term_idx == input_term.right);
    } else {
        let parent0 = &proof[node.parent0];

        assert!(parent0.rule == RULE_GET_ARG);
        assert!(parent0.extra == count - 1);
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
//
//  elim_apply nnr (nr-1) 0 o e_i rec f => f'
// ----------------------------------------------    (apply_nr)
//  elim_apply nnr nr 0 o e_i (f e) => (f' e)
//
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
    let num_rec_applies = node.extra5;
    let orig_idx = node.extra6;

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
    } else if num_rec_applies == 0 {
        assert!(parent0.rule == RULE_APPLY_ELIM);
        assert!(parent0.extra == num_nonrec_args);
        assert!(parent0.extra2 == num_rec_args - 1);

        assert!(result_term.kind == EXPR_APP, "GOT {}", result_term.kind);

        //  f == f
        assert!(parent0.input_term_idx == node_f);
        //  f' == f'
        assert!(parent0.result_term_idx == result_term.left);
    } else {
        assert!(parent0.rule == RULE_APPLY_ELIM);
        assert!(parent0.extra == num_nonrec_args);
        assert!(parent0.extra2 == num_rec_args);
        assert!(parent0.extra5 == num_rec_applies - 1);

        assert!(result_term.kind == EXPR_APP, "GOT {}", result_term.kind);

        //  f == f
        if num_rec_applies == 1 {
            assert!(
                parent0.input_term_idx == orig_idx,
                "GOT {}, expect {}",
                parent0.input_term_idx,
                orig_idx
            );
        } else {
            assert!(
                parent0.input_term_idx == node_f,
                "GOT {}, expect {}",
                parent0.input_term_idx,
                node_f
            );
        }
        //  f' == f'
        assert!(parent0.result_term_idx == result_term.left);
        let result_right = &terms[result_term.right];

        assert!(result_right.kind == EXPR_APP, "GOT {}", result_right.kind);
        assert!(
            result_right.left == rec,
            "GOT {} and {}",
            result_right.left,
            rec
        );

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
    assert!(check_eval_parent(parent1, p0_ep, node_epp));

    assert!(node_e == p0_e);

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
    let ind_rule_index = node.ind_rule;
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

fn check_type_ax(node: &ExpRule, proof: &[ExpRule], lifts: &[ExpLift], max_ax: usize) {}

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
    assert!(check_expected_binding(parent0, node.max_binding));
    assert!(check_expected_binding(parent1, node.max_binding));
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
    assert!(check_expected_binding(parent0, node.max_binding));
    assert!(check_expected_binding(parent1, node.max_binding));
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

    assert!(check_eval_parent(parent1, p0_T_idx, node_Tp_idx));
    assert!(node_a_idx == p0_a_idx);
    assert!(parent1.ctx_idx == EMPTY_CONTEXT_IDX);
    assert!(check_expected_binding(parent0, node.max_binding));
    assert!(check_expected_binding(parent1, node.max_binding));
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
    assert!(check_parent_lift(node, parent0));
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
    assert!(check_parent_lift(node, parent0));
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

    assert!(check_parent_lift(node, parent1));
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

// lean4 extentions
fn check_eval_proj(
    node: &ExpRule,
    proof: &[ExpRule],
    terms: &[ExpTerm],
    inductives: &[ExpInd],
    contexts: &HashList,
) {
    let input_term = &terms[node.input_term_idx];
    let inductive = &inductives[node.inductive];
    let parent0 = &proof[node.parent0];
    let parent1 = &proof[node.parent1];

    // 1. parent0 => eval input_term -> e'
    assert!(is_eval_rule(parent0.rule));
    // TODO: refactor oportunity...using parent0.result_term.top_level_func adds a lot of overhead...
    let parent0_res = get_eval_parent_res(parent0, input_term.left);
    assert!(check_eval_parent(parent0, input_term.left, parent0_res));
    assert!(check_expected_binding(parent0, node.max_binding));
    let evaled_input_term = &terms[parent0_res];
    let input_tlf = &terms[evaled_input_term.top_level_func];

    assert!(hash_list_subset(
        node.ctx_idx,
        parent0.ctx_idx,
        node.parent0_quot,
        contexts,
    ));

    // 1. Input term must be app giving args to ind ctor
    assert!(evaled_input_term.kind == EXPR_APP);
    // TODO: check that the ind_ctor has full arguments...);
    //        THIS MIGHT BE OK to skip IF we type check the expression before we eval...);
    //        because then we will ALWAYS see );
    assert!(input_tlf.kind == EXPR_IND_CTOR || input_tlf.kind == EXPR_PROJ_PLACEHOLDER);
    assert!(
        input_tlf.ind == node.inductive,
        "got: {} {}",
        input_tlf.ind,
        node.inductive
    );

    // 2. Inductive must only have a single rule...);
    //    TODO: not sure if this matters for eval... but check to be safe);
    assert!(inductive.num_rules == 1, "got: {}", inductive.num_rules);

    // 3. parent0 => inductive.num_params + field_index arg of the input term);
    assert!(parent1.rule == RULE_GET_ARG);
    assert!(parent1.extra == input_term.index);
    assert!(parent1.input_term_idx == parent0_res);
    assert!(parent1.result_term_idx == node.result_term_idx);
}

//       lift projector => proj'
// ----------------------------
//      Ind => projector
//
//     walk_proj(f) => f'
// ----------------------------
//      walk_proj(f arg) => (f' arg)
fn check_walk_proj(
    node: &ExpRule,
    proof: &[ExpRule],
    terms: &[ExpTerm],
    lifts: &[ExpLift],
    inductives: &[ExpInd],
) {
    let input_term = &terms[node.input_term_idx];
    let result_term = &terms[node.result_term_idx];
    let lift = &lifts[node.lift_rule];
    let parent0 = &proof[node.parent0];
    let inductive = &inductives[node.inductive];
    let projector_idx = inductive.projector;

    if input_term.kind == EXPR_APP {
        assert!(parent0.rule == RULE_WALK_PROJ);
        assert!(parent0.input_term_idx == input_term.left);
        assert!(parent0.result_term_idx == result_term.left);
        assert!(input_term.right == result_term.right);
    } else {
        if input_term.kind == EXPR_IND {
            assert!(lift.input_term_idx == projector_idx);
            assert!(node.result_term_idx == lift.result_term_idx);
            assert!(lift.max_binding == node.max_binding);
            assert!(lift.min_binding_seen == ExpTerm::MAX_BINDING);
            assert!(check_parent_lift(node, lift));
        } else {
            assert!(false);
        }
    }
}

fn check_constr_proj(
    node: &ExpRule,
    proof: &[ExpRule],
    terms: &[ExpTerm],
    inductives: &[ExpInd],
    contexts: &HashList,
    db_ind_rev_map: &HashMap<usize, String>,
) {
    let input_term = &terms[node.input_term_idx];
    let result_term = &terms[node.result_term_idx];
    let inductive = &inductives[node.inductive];
    let parent0 = &proof[node.parent0];
    let parent1 = &proof[node.parent1];

    let evaled_input_term = &terms[parent0.result_term_idx];
    let input_tlf = &terms[evaled_input_term.top_level_func];

    // 2. Inductive must only have a single rule...
    //    TODO: not sure if this matters for eval... but check to be safe
    assert!(inductive.num_rules == 1);

    // check parent0
    assert!(parent0.input_term_idx == node.input_term_idx);
    assert!(is_type_rule(parent0.rule));
    assert!(hash_list_subset(
        node.ctx_idx,
        parent0.ctx_idx,
        node.parent0_quot,
        contexts
    ));

    // check parent1
    assert!(parent1.rule == RULE_WALK_PROJ);
    assert!(parent1.inductive == node.inductive);
    assert!(parent1.input_term_idx == parent0.result_term_idx);

    // check result
    assert!(result_term.kind == EXPR_APP);
    assert!(result_term.left == parent1.result_term_idx);
    assert!(result_term.right == node.input_term_idx);
}

// just simplifies the inner expr inside the proj
//     e => e'
// --------------------------------------
//   proj(i, e) => proj(i, e')
fn check_eval_proj_simpl(
    node: &ExpRule,
    proof: &[ExpRule],
    terms: &[ExpTerm],
    inductives: &[ExpInd],
    contexts: &HashList,
) {
    let input_term = &terms[node.input_term_idx];
    let result_term = &terms[node.result_term_idx];
    let parent0 = &proof[node.parent0];

    assert!(input_term.kind == EXPR_PROJ);
    assert!(result_term.kind == EXPR_PROJ);
    assert!(check_expected_binding(parent0, node.max_binding));
    assert!(is_eval_rule(parent0.rule));
    assert!(check_eval_parent(
        parent0,
        input_term.left,
        result_term.left
    ));
    assert!(check_context(node, parent0, node.parent0_quot, contexts));
}

fn check_type_proj(node: &ExpRule, proof: &[ExpRule], terms: &[ExpTerm]) {
    let input_term = &terms[node.input_term_idx];
    let result_term = &terms[node.result_term_idx];
    let parent0 = &proof[node.parent0];
    let parent1 = &proof[node.parent1];
    let parent1_inp_idx = get_eval_parent_input(parent1, node.result_term_idx);
    let parent1_inp = &terms[parent1_inp_idx];

    // check well formedness of input term
    assert!(input_term.kind == EXPR_PROJ);

    // parent0
    assert!(parent0.rule == RULE_CONSTR_PROJ);
    assert!(parent0.input_term_idx == input_term.left);
    assert!(parent0.ctx_idx == node.ctx_idx);

    // parent1
    assert!(is_eval_rule(parent1.rule));
    assert!(check_eval_parent(
        parent1,
        parent1_inp_idx,
        node.result_term_idx
    ));
    assert!(check_expected_binding(parent1, node.max_binding));
    assert!(parent1_inp.kind == EXPR_PROJ);
    assert!(parent1_inp.left == parent0.result_term_idx);
    assert!(parent1_inp.index == input_term.index);
}

fn check_terms(terms: &[ExpTerm]) {
    for i in 0..terms.len() {
        let term = &terms[i];
        let f = &terms[term.left];
        if term.kind == EXPR_APP {
            assert!(
                term.top_level_func == f.top_level_func,
                "GOT: {:?} {:?} {:?} {:?} {}",
                term,
                f,
                term.argc,
                f.argc,
                i
            );
            assert!(
                term.argc == f.argc + 1,
                "GOT: {:?} {:?} {:?} {:?} {}",
                term,
                f,
                term.argc,
                f.argc,
                i
            );
        } else {
            assert!(term.argc == 0);
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
    assert!(is_type_rule(proof[proving_rule].rule));
    assert!(proof[proving_rule].ctx_idx == EMPTY_CONTEXT_IDX);

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

            // lean4 extensions
            RULE_EVAL_PROJ => check_eval_proj(node, proof, terms, inductives, contexts),

            RULE_TYPE_PROJ => check_type_proj(node, proof, terms),
            RULE_CONSTR_PROJ => {
                check_constr_proj(node, proof, terms, inductives, contexts, db_ind_rev_map)
            }
            RULE_WALK_PROJ => check_walk_proj(node, proof, terms, lifts, inductives),
            RULE_EVAL_PROJ_SIMPL => check_eval_proj_simpl(node, proof, terms, inductives, contexts),
            r => panic!("Unknown rule {}!", r),
        }
    }
}
