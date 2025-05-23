//use crate::lru::HConLruCache;
use hashconsing::{
    consign,
    hash_coll::p_hash::{HConMap, HConSet},
    HConsed, HConsign, HashConsign,
};
use log::debug;
use lru::LruCache;
use nom::number;
use serde::de::value;
use std::collections::hash_map::DefaultHasher;
use std::collections::{BTreeMap, HashMap, HashSet};
use std::hash::{Hash, Hasher};
use std::num::NonZeroUsize;
use std::sync::RwLock;

pub fn imax(i: usize, j: usize) -> usize {
    if j == 0 {
        0
    } else {
        std::cmp::max(i, j)
    }
}

pub struct EvaluationCache {
    cache: LruCache<(Term, u64), Term, fxhash::FxBuildHasher>,
    term_set: HConSet<Term>,
    free_bindings_cache: HashMap<(Term, usize), HashSet<usize>, fxhash::FxBuildHasher>,
}

impl EvaluationCache {
    fn new() -> Self {
        EvaluationCache {
            cache: LruCache::with_hasher(
                NonZeroUsize::new(100_000_000).unwrap(),
                fxhash::FxBuildHasher::default(),
            ),
            term_set: HConSet::default(),
            free_bindings_cache: HashMap::default(),
        }
    }

    fn get_context_hash(&mut self, term: Term, context: &Context) -> u64 {
        let free_bindings = self.free_bindings_nonrec(term, 0);
        //let free_bindings = self.free_bindings_of(term, 0);

        let mut hasher = DefaultHasher::new();
        for i in free_bindings {
            (i, context.get_bound(i)).hash(&mut hasher);
        }
        hasher.finish()
    }

    fn get(&mut self, term: Term, context: &Context) -> Option<&Term> {
        if self.term_set.contains(&term) {
            let hash = self.get_context_hash(term.clone(), context);
            self.cache.get(&(term.clone(), hash))
        } else {
            None
        }
    }

    fn insert(&mut self, term: Term, context: &Context, result: Term) {
        self.term_set.insert(term.clone());
        let hash = self.get_context_hash(term.clone(), context);
        self.cache.put((term.clone(), hash), result);
    }

    pub fn free_bindings_of(&mut self, term: Term, num_bindings: usize) -> HashSet<usize> {
        if let Some(res) = self.free_bindings_cache.get(&(term.clone(), num_bindings)) {
            return res.clone();
        }

        let res = match &**term {
            TermData::Bound(index) => {
                if *index >= num_bindings {
                    let mut res = HashSet::new();
                    res.insert(*index - num_bindings);
                    res
                } else {
                    HashSet::new()
                }
            }
            TermData::App(f, e) => {
                let f_res = self.free_bindings_of(f.clone(), num_bindings);
                let e_res = self.free_bindings_of(e.clone(), num_bindings);
                f_res.union(&e_res).cloned().collect()
            }
            TermData::Binding(BindingData { domain, body, .. }) => {
                let domain_res = self.free_bindings_of(domain.clone(), num_bindings);
                let body_res = self.free_bindings_of(body.clone(), num_bindings + 1);

                domain_res.union(&body_res).cloned().collect()
            }
            TermData::Proj(name, index, expr) => self.free_bindings_of(expr.clone(), num_bindings),
            _ => HashSet::new(),
        };

        self.free_bindings_cache
            .insert((term.clone(), num_bindings), res.clone());
        res
    }

    pub fn free_bindings_nonrec(&mut self, term: Term, num_bindings: usize) -> HashSet<usize> {
        if let Some(res) = self.free_bindings_cache.get(&(term.clone(), num_bindings)) {
            return res.clone();
        }

        let mut res = HashSet::new();
        let mut stack = Vec::with_capacity(1000000);
        // term, depth, children pushed
        stack.push((term.clone(), num_bindings, 0));

        while !stack.is_empty() {
            let (t, b, children_pushed) = stack.pop().unwrap();
            if children_pushed == 0 {
                if let Some(cached) = self.free_bindings_cache.get(&(t.clone(), b)) {
                    res = res.union(cached).cloned().collect();
                    continue;
                }

                stack.push((t.clone(), b, 1));
                match &**t {
                    TermData::App(f, e) => {
                        stack.push((f.clone(), b, 0));
                        //stack.push((e.clone(), b, false));
                    }
                    TermData::Binding(BindingData { domain, body, .. }) => {
                        stack.push((domain.clone(), b, 0));
                        //stack.push((body.clone(), b + 1, false));
                    }
                    TermData::Proj(name, index, expr) => stack.push((expr.clone(), b, 0)),
                    _ => {}
                };
            } else if children_pushed == 1 {
                //if let Some(cached) = self.free_bindings_cache.get(&(term.clone(), num_bindings)) {
                //    res = res.union(cached).cloned().collect();
                //    continue;
                //}

                stack.push((t.clone(), b, 2));
                match &**t {
                    TermData::App(f, e) => {
                        //stack.push((f.clone(), b, 0));
                        stack.push((e.clone(), b, 0));
                    }
                    TermData::Binding(BindingData { domain, body, .. }) => {
                        //stack.push((domain.clone(), b, 0));
                        stack.push((body.clone(), b + 1, 0));
                    }
                    _ => {}
                };
            } else {
                let this_res = match &**t {
                    TermData::Bound(index) => {
                        if *index >= b {
                            let mut res = HashSet::new();
                            res.insert(*index - b);
                            res
                        } else {
                            HashSet::new()
                        }
                    }
                    TermData::App(f, e) => {
                        let f_res = self.free_bindings_cache.get(&(f.clone(), b)).unwrap();
                        let e_res = self.free_bindings_cache.get(&(e.clone(), b)).unwrap();
                        f_res.union(e_res).cloned().collect()
                    }
                    TermData::Binding(BindingData { domain, body, .. }) => {
                        let d_res = self.free_bindings_cache.get(&(domain.clone(), b)).unwrap();
                        let b_res = self
                            .free_bindings_cache
                            .get(&(body.clone(), b + 1))
                            .unwrap();
                        d_res.union(b_res).cloned().collect()
                    }
                    TermData::Proj(name, index, expr) => self
                        .free_bindings_cache
                        .get(&(expr.clone(), b))
                        .cloned()
                        .unwrap(),
                    _ => HashSet::new(),
                };

                res = res.union(&this_res).cloned().collect();
                self.free_bindings_cache.insert((t.clone(), b), this_res);
            }
        }
        res
    }
}

#[derive(Debug, Clone)]
pub struct Theorem {
    pub val: Term,
    pub ty: Term,
    pub axioms: HashMap<String, Term>,
    pub inductives: HashMap<String, Inductive>,
}

impl Theorem {
    pub fn new(
        val: Term,
        ty: Term,
        axioms: &HashMap<String, Term>,
        inductives: &HashMap<String, Inductive>,
    ) -> Theorem {
        let mut eval = Evaluator::new(axioms, inductives.clone());
        let mut inductives = inductives.clone();

        // simplify inductives and axioms...
        for (name, inductive) in inductives.iter_mut() {
            for rule in &mut inductive.rules {
                let new_val = eval
                    .eval(rule.ty.clone())
                    .map_err(|e| format!("Simplify val err: {}", e))
                    .unwrap();
                let mut cache = Some(HConMap::default());
                eprintln!(
                    "simplified {}.{} from size {} to size {}",
                    inductive.name,
                    rule.name,
                    rule.ty.size(&mut cache),
                    new_val.size(&mut cache)
                );
                rule.ty = new_val;
            }
        }

        Theorem {
            val,
            ty,
            axioms: axioms.clone(),
            inductives: inductives.clone(),
        }
    }

    pub fn size(&self, cache: &mut Option<HConMap<Term, usize>>) -> usize {
        self.val.size(cache) + self.ty.size(cache)
    }

    pub fn prove(&self) -> Result<(), String> {
        let mut eval = Evaluator::new(&self.axioms, self.inductives.clone());
        println!("original term: {:?}", self.val);
        println!("original ty: {:?}", self.ty);
        println!("simplifying...");
        let test = propagate_flag(&self.val);
        let test2 = sum_unflagged_sizes(&test, &mut Some(HConMap::default()));
        let test3 = test.size(&mut Some(HConMap::default()));
        println!(
            "FLAG: {}, size unflagged: {}, total size: {}",
            test.flag, test2, test3
        );
        let test_val = {
            let test = eval
                .eval(test.clone())
                .map_err(|e| format!("Simplify val err: {}", e))?;
            garbage_collect();
            let mut cache = Some(HConMap::default());
            println!(
                "simplified from size {} to size {}",
                self.val.size(&mut cache),
                test.size(&mut cache)
            );
            test
        };
        let test = propagate_flag(&test_val);
        let test2 = sum_unflagged_sizes(&test, &mut Some(HConMap::default()));
        let test3 = test.size(&mut Some(HConMap::default()));
        println!(
            "SIMPLIFIED FLAG: {}, size unflagged: {}, total size: {}",
            test.flag, test2, test3
        );

        //OK: WHAT I WILL DO:
        //    - output mapping between terms and the expr number to find bad expr number
        //    - check that it actually is bad ----> then fix it!
        //garbage_collect();
        //println!("typing term {}...", test_val);
        println!("gc...");
        //garbage_collect();
        let simplified_ty = eval
            .eval(self.ty.clone())
            .map_err(|e| format!("Simplify Type error: {}", e))?;
        {
            let mut cache = Some(HConMap::default());
            println!(
                "simplified type from size {} to size {}",
                self.ty.size(&mut cache),
                simplified_ty.size(&mut cache)
            );
        }
        println!("simpl term: {:?}", test_val);
        println!("simpl ty: {:?}", simplified_ty);
        //println!("typing term {}...", test_val);
        //println!("expect type {}...", simplified_ty);
        let computed_ty = eval
            .ty(test_val.clone())
            .map_err(|e| format!("Typing error: {}", e))?;
        //println!("simplify type...");
        //println!("expect type {}...", simplified_ty);
        //println!("def eq...");
        if !eval.def_equals(computed_ty.clone(), simplified_ty.clone()) {
            Err(format!(
                "Theorem prove fail: Expected type: {:?} (simplified to {:?}) , Got type: {:?}",
                self.ty, simplified_ty, computed_ty
            ))
        } else {
            //println!("{:?}\n :: {:?}\n\n{:?}\n => {:?}\n", self.val, computed_ty, self.ty, simplified_ty);
            Ok(())
        }
    }
}

pub struct Context {
    bindings: Vec<Option<Term>>,
}

impl Context {
    pub fn new() -> Context {
        Context {
            bindings: Vec::new(),
        }
    }

    pub fn push(&mut self, term: Term) {
        self.bindings.push(Some(term.clone()));
    }

    pub fn null_bind(&mut self) {
        self.bindings.push(None);
    }

    pub fn pop(&mut self) {
        self.bindings.pop();
    }

    pub fn get_bound(&self, index: usize) -> Option<Term> {
        let index = self.bindings.len().checked_sub(index + 1)?;
        self.bindings.get(index).map(|x| x.clone()).flatten()
    }

    fn hash(&self) -> u64 {
        let mut hash = DefaultHasher::new();
        self.bindings.hash(&mut hash);
        hash.finish()
    }

    pub fn len(&self) -> usize {
        self.bindings.len()
    }
}

impl std::fmt::Debug for Context {
    fn fmt(&self, fmt: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        if self.bindings.len() < 3 {
            write!(fmt, "{:?}", self.bindings)
        } else {
            write!(fmt, "[\n")?;
            let max_len = std::cmp::min(self.bindings.len(), 20);

            for item in &self.bindings {
                if let Some(expr) = item {
                    write!(fmt, "\t{:?},\n", expr)?;
                } else {
                    write!(fmt, "\t_,\n")?;
                }
            }

            write!(fmt, "]")?;
            Ok(())
        }
    }
}

// Lean4 Changes!:
// - non_dependent ind recursors now include the type as an
//    arg to the motive
//   e.g. And.rec = a, b: prop, motive: (And a b, Sort u), ....  motive (And a b)...
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct Inductive {
    pub name: String,
    pub num_params: usize,
    pub ty: Term,
    pub rules: Vec<InductiveRule>,
    rule_lookup: BTreeMap<String, usize>,

    pub non_dependent: bool,
    pub is_family: bool,

    /// Cached Eliminator body (without global params or motive)
    pub elim_body: Term,
    pub projector: Option<Term>, // exists for structs...easier typing
}

impl Inductive {
    pub fn new(
        name: &str,
        num_params: usize,
        ty: Term,
        rules: &[InductiveRule],
        non_dependent: bool,
    ) -> Inductive {
        let rule_lookup = rules
            .iter()
            .enumerate()
            .map(|(index, term)| (term.name.clone(), index))
            .collect();

        // TODO: check consistency
        let mut res = Inductive {
            name: name.to_string(),
            num_params,
            ty: ty.clone(),
            rules: rules.to_vec(),
            rule_lookup,
            non_dependent,
            is_family: false,
            elim_body: sort(0),
            projector: None,
        };

        if ty.params().len() != num_params {
            // !name.starts_with("eq") && !name.starts_with("heq") && ty.params().len() != num_params {
            for rule in rules {
                if rule.num_recs(&res) != 0 {
                    res.is_family = true;
                }
            }
        }

        res.generate_elim_body();
        res
    }

    fn deps(&self) -> HashSet<String> {
        let mut inds = self.ty.inds();
        for rule in &self.rules {
            inds = inds.union(&rule.ty.inds()).cloned().collect();
        }
        inds.remove(&self.name);
        inds
    }

    fn ty_body(&self) -> Term {
        let mut res = &self.ty;
        for i in 0..self.num_params {
            if let TermData::Binding(BindingData { body, .. }) = &***res {
                res = body;
            } else {
                panic!("Para isn't a binding in Inductive!");
            }
        }
        res.clone()
    }

    fn global_params(&self) -> Vec<Term> {
        self.ty.params()[..self.num_params].to_vec()
    }

    fn index_params(&self) -> Vec<Term> {
        let params = self.ty.params();
        params[self.num_params..params.len()].to_vec()
    }

    // TODO: fix...
    pub fn num_nonrecursive_args_for_rule(&self, idx: usize) -> usize {
        let rule_ty = self.rules[idx].ty.clone();
        let rule_params = rule_ty.params();
        let mut res = 0;

        for param in rule_params {
            match &**param.top_level_func() {
                TermData::Ind(name) if name == &self.name => {
                    break;
                }
                _ => res += 1,
            }
        }

        res
    }

    pub fn num_recursive_args_for_rule(&self, idx: usize) -> usize {
        let rule_ty = self.rules[idx].ty.clone();
        let rule_params = rule_ty.params();
        rule_params.len() - self.num_nonrecursive_args_for_rule(idx)
    }

    // TODO: only Prop inductives or all?
    pub fn is_subsingleton(&self) -> bool {
        if self.rules.len() > 1 {
            return false;
        }

        // for now... just do
        for rule in &self.rules {
            // TODO: check the ctor arg is an index
        }

        return true;
    }

    /// See:
    /// https://leanprover.github.io/theorem_proving_in_lean/inductive_types.html
    ///
    /// We are allowed to eliminate from an inductively defined Prop to an arbitrary Sort
    /// when there is only one constructor and each constructor argument is either in Prop or an index
    /// TODO:
    /*pub fn use_singleton_elim(&self) -> bool {
        if self.rules.len() > 1 {
            return false;
        }

        for rule in &self.rules {
            // check that the constructor arg is either in Prop or an index
            for arg in rule.ty.params() {
                let arg_ty = // get the arg type...
                if arg
            }
        }

        false
    }*/

    /// Generates an eliminator for the inductive type.
    ///
    /// For example, given an Inductive type:
    ///
    /// Inductuve Ind (ind_params...) : Sort.{u}
    /// | c0 : (ind_params...) -> (non_rec_params...) -> (rec_params...) -> Ind
    /// | c1 : ...
    /// | ...
    ///
    /// The universe levels of arguments non_rec_params and rec_params must be smaller than or equal to l_k in I.
    /// The universe parameter {l} is elided (and becomes 0) when all of the following are true:
    /// 1. Sort.{u} could be 0 (i.e. Prop)
    /// 2. There is more than one induction rule
    ///
    /// The eliminator is generated as:
    ///
    /// ```
    /// Ind.{u}.rec.{l} : (ind_params...) ->
    ///                   (motive : ((Ind ind_params...) -> Sort.{l})) ->
    ///                   (minor_premises...) ->
    ///                   (n : Ind ind_params...) ->
    ///                   motive n
    /// ```
    ///
    /// Where each minor premise is:
    ///
    /// ```
    /// minor_premise_i : (non_rec_params...) ->
    ///                 (rec_params...) ->
    ///                 motive (rule_i ind_params... non_rec_params... rec_params...)
    /// ```
    /// Where motive_params is a bound variable of the type of applying the motive to each bound
    /// rec_param.
    ///
    /// Just like Lean, when Sort.{u} == Sort.{0}, we use nondependent elimination. This means the
    /// motive and minor premises become:
    ///
    /// ```
    /// motive : Sort.{l}
    /// minor_premise_i : (non_rec_params...) ->
    ///                   (rec_params...) ->
    ///                   motive
    /// ```
    // TODO: to speed this up, cache a version and use substitution to replace the universe level
    pub fn elim(&self, motive_universe_level: usize) -> Term {
        let body = self.ty_body();
        // TODO: this seems somewhat wrong....
        //       See inductive nat.less_than_or_equal, which still must apply the motive
        let use_nondependent =
            //if matches!(*body, TermData::Sort(0)) && self.num_params == self.ty.params().len() {
            //if let Ok(TermData::Sort(1)) = body_ty {
            if matches!(**body.body(), TermData::Sort(0)) {
                true
            } else {
                false
            };
        //println!("use_nondependent: {:?}", use_nondependent);
        let elide_universe_param = if self.non_dependent && self.rules.len() > 1 {
            true
        } else {
            false
        };

        //println!("elide_universe_param: {:?}", elide_universe_param);
        if elide_universe_param && motive_universe_level != 0 {
            panic!("Attempted to instantiate eliminator universe when it should be elided!");
        }

        let mut res = Vec::new();

        // add inductive type params
        let params = &self.ty.params()[..self.num_params];
        res.extend(params.iter().cloned());

        // add motive
        let motive = self.generate_motive(motive_universe_level);
        res.push(motive);

        res.push(self.elim_body.clone());

        let res = pi_list(&res);

        res
    }

    fn nondependent(&self) -> bool {
        let body = self.ty_body();

        //if matches!(*body, TermData::Sort(0)) && self.num_params == self.ty.params().len() {
        //if let Ok(TermData::Sort(1)) = body_ty {
        if matches!(**body.body(), TermData::Sort(0)) {
            true
        } else {
            false
        }
    }

    pub fn generate_elim_body(&mut self) {
        //println!("GENERATING ELIM BODY FOR {}", self.name);
        let mut eval = Evaluator::empty();

        // When the environment is impredicative and l_k is zero, then we use nondependent elimination, and we omit
        // the argument c in C, and v in the minor premises. That is, C becomes
        //    (C :: (a :: \alpha[A]), Type.{l'})
        // and \epsilon_i_j[A]
        //    \epsilon_i_j[A] : (b :: \beta[A]) (u :: \gama[A, b]), C p[A, b]
        let body = self.ty_body();

        let use_nondependent =
            //if matches!(*body, TermData::Sort(0)) && self.num_params == self.ty.params().len() {
            //if let Ok(TermData::Sort(1)) = body_ty {
            if matches!(**body.body(), TermData::Sort(0)) {
                true
            } else {
                false
            };
        let elide_universe_param = if self.non_dependent && self.rules.len() > 1 {
            true
        } else {
            false
        };

        //println!(
        //    "generating elim for {}: nondep? {}, elide_uni? {}, index params len: {}",
        //    self.name,
        //    use_nondependent,
        //    elide_universe_param,
        //    self.index_params().len()
        //);

        let mut res = Vec::new();
        // minor_premise_i : (non_rec_params...) ->
        //                 (rec_params...) ->
        //                 (motive_params...) ->
        //                 motive (minor_premise_i ind_params... non_rec_params... rec_params...)
        for (rule_index, rule) in self.rules.iter().enumerate() {
            //println!("generating minor premise: {}", rule_index);
            //if use_nondependent {
            //    res.push(self.generate_minor_premise_nondependent(rule_index, rule));
            //} else {
            //    res.push(self.generate_minor_premise_dependent(rule_index, rule));
            //}
            res.push(self.generate_minor_premise(rule_index, rule, !self.non_dependent, &mut eval));
            //println!("got premise {:?}", self.generate_minor_premise(rule_index, rule, !use_nondependent, &mut eval));
        }

        // generate the major premise
        //println!("generating major premise");

        // push index params
        let mut major_premise_pis = Vec::new();
        for (i, param) in self.index_params().iter().enumerate() {
            //println!("PARAM: {}", param);
            major_premise_pis.push(
                eval.lift_inner(param.clone(), (self.rules.len() + 1) as isize, i)
                    .unwrap(),
            )
        }

        let mut ind_ty_apps = vec![ind(self.name.clone())];
        let global_param_bindings = (0..self.global_params().len()).map(|i| {
            bound(
                self.global_params().len() - 1 - i
                    + 1
                    + self.rules.len()
                    + self.index_params().len(),
            )
        });
        let index_param_bindings =
            (0..self.index_params().len()).map(|i| bound(self.index_params().len() - 1 - i));
        //println!("IND FOR {}", self.name);
        //println!(
        //    "index_param_bindings: {:?}",
        //    index_param_bindings.clone().collect::<Vec<_>>()
        //);
        //println!(
        //    "global param bindings: {:?}",
        //    global_param_bindings.collect::<Vec<_>>()
        //);
        //println!(
        //    "index param bindings: {:?}",
        //    index_param_bindings.collect::<Vec<_>>()
        //);
        //println!("major_premise_pis: {:?}", major_premise_pis);
        ind_ty_apps.extend(global_param_bindings);
        ind_ty_apps.extend(index_param_bindings);
        let ind_ty = app_list(&ind_ty_apps);
        major_premise_pis.push(ind_ty);
        //println!("major premise: {:?}", major_premise_pis);

        let motive_binding = bound(major_premise_pis.len() + self.rules.len());
        let mut final_motive_apps = vec![motive_binding];

        // skip actual major premise inductive type if we are non-dependent
        let motive_args_len = if true {
            major_premise_pis.len()
        } else {
            major_premise_pis.len() - 1
        };
        final_motive_apps
            .extend((0..motive_args_len).map(|i| bound(major_premise_pis.len() - 1 - i)));
        //println!("final motive apps: {:?}", final_motive_apps);
        major_premise_pis.push(app_list(&final_motive_apps));

        let major_premise = pi_list(&major_premise_pis);
        res.push(major_premise);
        //println!("got elim {:?}", pi_list(&res));
        //println!("elim done");

        self.elim_body = pi_list(&res);
        //println!("elim body: {:?}", self.elim_body);
    }

    pub fn generate_motive(&self, motive_universe_level: usize) -> Term {
        let mut res_pi_list = self.index_params();

        //if !self.non_dependent {
        // construct the recursive param
        let mut ind_app_list = vec![ind(self.name.clone())];
        let global_bindings = (0..self.global_params().len())
            .map(|i| bound(self.global_params().len() - 1 - i + res_pi_list.len()));
        ind_app_list.extend(global_bindings);
        let index_bindings =
            (0..self.index_params().len()).map(|i| bound(self.index_params().len() - 1 - i));
        ind_app_list.extend(index_bindings);
        let ind = app_list(&ind_app_list);
        res_pi_list.push(ind);
        //}
        res_pi_list.push(sort(motive_universe_level));
        pi_list(&res_pi_list)
    }

    fn generate_minor_premise(
        &self,
        rule_index: usize,
        rule: &InductiveRule,
        dependent: bool,
        eval: &mut Evaluator,
    ) -> Term {
        let mut minor_premise_args = Vec::new();
        let mut minor_premise_motive_args = Vec::new();
        let rule_params = &rule.ty.params()[self.num_params..];
        //println!("rule_params: {:?}", rule_params);

        for (param_index, param) in rule_params.iter().enumerate() {
            minor_premise_args.push(
                eval.lift_inner(param.clone(), rule_index as isize + 1, param_index)
                    .unwrap(),
            );

            // if param is recursive, also push (motive arg) to rec params
            // due to ind type rules, may only be recursive in the body of
            // the param
            let param_func = param.body().top_level_func();
            match &**param_func {
                TermData::Ind(name) if name == &self.name => {
                    let mut params = param.params();
                    let motive_binding = bound(
                        rule_params.len()
                            + minor_premise_motive_args.len()
                            + params.len()
                            + rule_index,
                    );
                    let mut motive_apps = vec![motive_binding];
                    // gross.... try to consolidate lifting later...
                    motive_apps.extend_from_slice(
                        &eval
                            .lift_inner(
                                param.body().clone(),
                                (rule_params.len() - 1 - param_index
                                    + 1
                                    + minor_premise_motive_args.len())
                                    as isize,
                                params.len(),
                            )
                            .unwrap()
                            .app_args()[self.num_params..],
                    );
                    // if dependent, add recursive arg to motive
                    // if it is a function, need to pass corresponding args...
                    let mut orig_param_binding = vec![bound(
                        rule_params.len() - 1 - param_index
                                + minor_premise_motive_args.len()
                                // TODO: check
                                + params.len(),
                    )];
                    orig_param_binding
                        .extend((0..params.len()).map(|i| bound(params.len() - i - 1)));
                    motive_apps.push(app_list(&orig_param_binding));
                    //}

                    //let mut params_lifted = params;
                    //println!("minor premise args len: {}", minor_premise_args.len());
                    //println!(
                    //    "minor premise motive args len: {}",
                    //    minor_premise_motive_args.len()
                    //);
                    // lift each param
                    let mut params_lifted = params
                        .iter()
                        .enumerate()
                        .map(|(i, p)| {
                            eval.lift_inner(
                                p.clone(),
                                (rule_params.len() - 1 - param_index
                                    + 1
                                    + minor_premise_motive_args.len())
                                    as isize,
                                i + minor_premise_args.len() - minor_premise_motive_args.len() - 1,
                            )
                            .unwrap()
                        })
                        .collect::<Vec<_>>()
                        .iter()
                        .enumerate()
                        .map(|(i, p)| eval.lift_inner(p.clone(), 1 as isize, i).unwrap())
                        .collect::<Vec<_>>();

                    // parameters if the param is a Pi
                    params_lifted.push(app_list(&motive_apps));
                    minor_premise_motive_args.push(pi_list(&params_lifted));
                }
                _ => {}
            }
        }

        let motive_binding =
            bound(minor_premise_args.len() + minor_premise_motive_args.len() + rule_index);
        let mut premise_body_apps = vec![motive_binding];

        // lift any args that refer to global params out byond the motive
        // and prior minor premises (e.g. this is usually a global sort param)
        let result_args = &eval
            .lift_inner(
                rule.ty.body(),
                (rule_index + 1) as isize,
                rule_params.len(),
                //rule_params.len(),
            )
            .unwrap();
        // lift args beyond the new motive params we introduced
        let result_args = &eval
            .lift_inner(
                result_args.clone(),
                (minor_premise_motive_args.len()) as isize,
                0,
            )
            .unwrap()
            .app_args()[self.num_params..];

        premise_body_apps.extend_from_slice(result_args);

        // inductive arg for the minor_premise body
        //if dependent {
        let inductive_arg = {
            let mut recursive_arg_apps = vec![ind_ctor(self.name.clone(), rule.name.clone())];
            let global_param_bindings = (0..self.global_params().len()).map(|i| {
                bound(
                    self.global_params().len() - 1 - i
                        + minor_premise_args.len()
                        + minor_premise_motive_args.len()
                        + rule_index
                        + 1,
                )
            });
            recursive_arg_apps.extend(global_param_bindings);
            let rule_param_bindings = (0..rule_params.len())
                .map(|i| bound(rule_params.len() - 1 - i + minor_premise_motive_args.len()));
            recursive_arg_apps.extend(rule_param_bindings);
            app_list(&recursive_arg_apps)
        };
        premise_body_apps.push(inductive_arg);
        //}

        let premise_body = app_list(&premise_body_apps);

        let mut result = minor_premise_args;
        result.extend(minor_premise_motive_args);
        result.push(premise_body);
        let result = pi_list(&result);
        result
        //let mut ind_app_list = vec![axiom(rule.name.clone())];
        //for param_index in 0..self.ty.params().len() {
        //    ind_app_list.push(bound(
        //        self.ty.params().len() - param_index
        //            + rule_index
        //            + minor_premise_args.len()
        //            + minor_premise_motive_args.len(),
        //    ))
        //}
        //for param_index in 0..minor_premise_args.len() {
        //    ind_app_list.push(bound(
        //        minor_premise_args.len() - 1 - param_index + minor_premise_motive_args.len(),
        //    ));
        //}
        //let result_ind = app_list(&ind_app_list);
        //let result = app(motive, result_ind);

        //let mut full_pi_list = minor_premise_args;
        //full_pi_list.extend(minor_premise_motive_args);
        //full_pi_list.push(result);
        //let res = pi_list(&full_pi_list);
        //res
    }

    fn axioms(&self) -> impl Iterator<Item = (String, Term)> + '_ {
        [
            (self.name.clone(), self.ty.clone()),
            //(format!("{}.rec", self.name), self.elim()),
        ]
        .into_iter()
        .chain(
            self.rules
                .iter()
                .map(|rule| (rule.name.clone(), rule.ty.clone())),
        )
    }
}

impl std::fmt::Debug for Inductive {
    fn fmt(&self, fmt: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        writeln!(fmt, "Inductive {} : {:?}", self.name, self.ty)?;
        for rule in &self.rules {
            writeln!(fmt, "\t{:?}", rule)?;
        }
        Ok(())
    }
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct InductiveRule {
    pub name: String,
    pub ty: Term,
}

impl InductiveRule {
    pub fn new(name: &str, ty: Term) -> InductiveRule {
        InductiveRule {
            name: name.to_string(),
            ty,
        }
    }

    pub fn num_recs(&self, inductive: &Inductive) -> usize {
        let mut count = 0;
        for arg in self.ty.params().iter().rev() {
            if matches!(**arg.body().top_level_func(), TermData::Ind(ref name) if name == &inductive.name)
            {
                count += 1;
            } else {
                break;
            }
        }
        return count;
    }
}

impl std::fmt::Debug for InductiveRule {
    fn fmt(&self, fmt: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(fmt, "{} : {:?}", self.name, self.ty)
    }
}

consign! {
    let FACTORY = consign(0) for TaggedTermData;
}
static gc_counter: RwLock<usize> = RwLock::new(0);

#[derive(Debug, Hash, Copy, Clone, PartialEq, Eq)]
pub enum BindingType {
    Lam,
    Pi,
}

#[derive(Debug, Hash, Clone, PartialEq, Eq)]
pub struct BindingData {
    /// Whether this is a Lam or Pi
    pub ty: BindingType,

    /// Type of the bound variable
    pub domain: Term,

    /// The body of the term
    pub body: Term,
}

#[derive(Hash, Clone, PartialEq, Eq)]
pub enum TermData {
    Bound(usize),
    Sort(usize),
    Binding(BindingData),
    App(Term, Term),
    Axiom(String),
    Defn(String, Term, Term),

    // new induction things...
    Ind(String),
    IndCtor(String, String),
    IndRec(String, usize),

    // Lean4 extensions
    // Primitive Projection
    Proj(String, usize, Term),
    ProjTyper(String),
    String(String),
}

impl TermData {
    pub fn inds(&self) -> HashSet<String> {
        match self {
            TermData::Binding(BindingData { domain, body, .. }) => {
                domain.inds().union(&body.inds()).cloned().collect()
            }
            TermData::App(f, e) => f.inds().union(&e.inds()).cloned().collect(),
            TermData::Proj(name, _, t) => {
                let mut res = t.inds();
                res
            }
            TermData::Ind(ind) => {
                let mut h = HashSet::new();
                h.insert(ind.to_string());
                h
            }
            TermData::IndCtor(ind, ..) => {
                let mut h = HashSet::new();
                h.insert(ind.to_string());
                h
            }
            TermData::IndRec(ind, ..) => {
                let mut h = HashSet::new();
                h.insert(ind.to_string());
                h
            }
            _ => HashSet::new(),
        }
    }

    pub fn params(&self) -> Vec<Term> {
        let mut res = vec![];
        let mut curr_ty = self;
        loop {
            match curr_ty {
                TermData::Binding(BindingData {
                    ty: _,
                    domain,
                    body,
                }) => {
                    res.push(domain.clone());
                    curr_ty = body;
                }
                _ => {
                    break;
                }
            }
        }
        res
    }

    fn app_args(&self) -> Vec<Term> {
        let mut res = vec![];
        let mut curr = self;
        loop {
            match curr {
                TermData::App(f, e) => {
                    res.push(e.clone());
                    curr = f;
                }
                _ => {
                    break;
                }
            }
        }
        res.reverse();
        res
    }

    pub fn body(&self) -> Term {
        let mut curr_ty = self;
        loop {
            match curr_ty {
                TermData::Binding(BindingData {
                    ty: _,
                    domain,
                    body,
                }) => {
                    curr_ty = &*body;
                }
                _ => break,
            }
        }
        // meh
        raw_term(curr_ty.clone())
    }

    /// From a term of the form ((((f e1) e2) e3) .... ), will return 'f'
    fn top_level_func(&self) -> Term {
        let mut curr_ty = self;
        loop {
            match curr_ty {
                TermData::App(f, e) => {
                    curr_ty = &*f;
                }
                _ => break,
            }
        }
        // meh
        raw_term(curr_ty.clone())
    }

    fn size(&self, cache: &mut Option<HConMap<Term, usize>>) -> usize {
        let res = match self {
            TermData::Bound(_) | TermData::Sort(_) | TermData::Axiom(_) | TermData::String(_) => 0,
            TermData::Binding(BindingData { domain, body, .. }) => {
                domain.size(cache).saturating_add(body.size(cache))
            }
            TermData::App(f, e) => f.size(cache).saturating_add(e.size(cache)),
            TermData::Proj(_, _, expr) => expr.size(cache),
            TermData::Defn(_, ty, value) => value.size(cache),
            TermData::Ind(_) | TermData::IndCtor(_, _) | TermData::IndRec(_, _) => 0,
            TermData::ProjTyper(_) => 0,
        };
        let res = res + 1;

        if let Some(c) = cache {
            c.insert(raw_term(self.clone()), res);
        }
        res
    }

    fn is_lambda(&self) -> bool {
        matches!(
            self,
            TermData::Binding(BindingData {
                ty: BindingType::Lam,
                ..
            })
        )
    }

    fn is_pi(&self) -> bool {
        matches!(
            self,
            TermData::Binding(BindingData {
                ty: BindingType::Pi,
                ..
            })
        )
    }
}

impl std::fmt::Debug for TermData {
    fn fmt(&self, fmt: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        //match self {
        //    TermData::Bound(index) => {
        //        write!(fmt, "Bound({})", index)
        //    }
        //    TermData::Sort(index) => {
        //        write!(fmt, "Sort({})", index)
        //    }
        //    TermData::Binding(BindingData { ty, domain, body }) => {
        //        write!(fmt, "{:?}({:?}, {:?})", ty, domain, body)
        //    }
        //    TermData::App(f, e) => {
        //        write!(fmt, "App({:?}, {:?})", f, e)
        //    }
        //    TermData::Axiom(name) => {
        //        write!(fmt, "Axiom({})", name)
        //    }
        //}
        write!(fmt, "{}", self);
        Ok(())
    }
}

impl std::fmt::Display for TermData {
    fn fmt(&self, fmt: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        match self {
            TermData::Bound(index) => {
                write!(fmt, "Bound({})", index)
            }
            TermData::Sort(level) => {
                write!(fmt, "Sort({})", level)
            }
            TermData::Binding(BindingData { ty, domain, body }) => {
                write!(fmt, "{:?}({}, {})", ty, ***domain, ***body)
            }
            TermData::App(f, e) => {
                write!(fmt, "App({}, {})", ***f, ***e)
            }
            TermData::Ind(name) => {
                write!(fmt, "Ind({})", name)
            }
            TermData::IndCtor(name, ctor) => {
                write!(fmt, "IndCtor({}.{})", name, ctor)
            }
            TermData::IndRec(name, motive_sort) => {
                write!(fmt, "IndRec({}, {})", name, motive_sort)
            }
            TermData::Axiom(name) => {
                write!(fmt, "Axiom({})", name)
            }
            TermData::Proj(name, index, expr) => {
                write!(fmt, "Proj({}, {}, {})", name, index, ***expr)
            }
            TermData::ProjTyper(name) => {
                write!(fmt, "ProjTyper({})", name)
            }
            TermData::Defn(name, ty, value) => {
                write!(fmt, "Defn({}, {}, {})", name, ***ty, ***value)
            }
            TermData::String(value) => {
                write!(fmt, "String({})", value)
            }
        }
    }
}

#[derive(Hash, Clone, PartialEq, Eq)]
pub struct TaggedTermData {
    pub data: TermData,
    pub flag: bool,
}

impl TaggedTermData {
    pub fn new(data: TermData, flag: bool) -> Self {
        TaggedTermData { data, flag }
    }
}

pub fn propagate_flag(term: &Term) -> Term {
    match &***term {
        TermData::Binding(BindingData { ty, domain, body }) => {
            let new_domain = propagate_flag(domain);
            let new_body = propagate_flag(body);
            let new_flag = term.flag || new_domain.flag || new_body.flag;
            FACTORY.mk(TaggedTermData::new(
                TermData::Binding(BindingData {
                    ty: *ty,
                    domain: new_domain,
                    body: new_body,
                }),
                new_flag,
            ))
        }
        TermData::App(f, e) => {
            let new_f = propagate_flag(f);
            let new_e = propagate_flag(e);
            let new_flag = term.flag || new_f.flag || new_e.flag;
            FACTORY.mk(TaggedTermData::new(TermData::App(new_f, new_e), new_flag))
        }
        TermData::Proj(name, index, expr) => {
            let new_expr = propagate_flag(expr);
            let new_flag = term.flag || new_expr.flag;
            FACTORY.mk(TaggedTermData::new(
                TermData::Proj(name.clone(), *index, new_expr),
                new_flag,
            ))
        }
        _ => {
            if term.flag {
                term.clone()
            } else {
                FACTORY.mk(TaggedTermData::new(term.data.clone(), false))
            }
        }
    }
}

pub fn sum_unflagged_sizes(term: &Term, cache: &mut Option<HConMap<Term, usize>>) -> usize {
    // If the term is not flagged, include its size; otherwise, skip it.
    let term_size = if !term.flag { 1_usize } else { 0_usize };

    // Recursively process child terms based on the term's structure.
    let children_size = match &***term {
        TermData::Bound(_) | TermData::Sort(_) | TermData::Axiom(_) | TermData::String(_) => 0,
        TermData::Binding(BindingData { domain, body, .. }) => {
            sum_unflagged_sizes(domain, cache).saturating_add(sum_unflagged_sizes(body, cache))
        }
        TermData::App(f, e) => {
            sum_unflagged_sizes(f, cache).saturating_add(sum_unflagged_sizes(e, cache))
        }
        TermData::Proj(_, _, expr) => sum_unflagged_sizes(expr, cache),
        TermData::Defn(_, ty, value) => sum_unflagged_sizes(value, cache),
        TermData::Ind(_) | TermData::IndCtor(_, _) | TermData::IndRec(_, _) => 0,
        TermData::ProjTyper(_) => 0,
    };

    term_size.saturating_add(children_size)
}

pub type Term = HConsed<TaggedTermData>;

pub fn raw_term(data: TermData) -> Term {
    FACTORY.mk(TaggedTermData::new(data, false)) // Default flag to false
}

impl std::ops::Deref for TaggedTermData {
    type Target = TermData;

    fn deref(&self) -> &Self::Target {
        &self.data
    }
}

impl std::fmt::Debug for TaggedTermData {
    fn fmt(&self, fmt: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(fmt, "{:?} (flag: {})", self.data, self.flag)
    }
}

pub fn bound(index: usize) -> Term {
    raw_term(TermData::Bound(index))
}

pub fn sort(level: usize) -> Term {
    raw_term(TermData::Sort(level))
}

pub fn binding(ty: BindingType, domain: Term, body: Term) -> Term {
    raw_term(TermData::Binding(BindingData { ty, domain, body }))
}

pub fn lam(domain: Term, body: Term) -> Term {
    raw_term(TermData::Binding(BindingData {
        ty: BindingType::Lam,
        domain,
        body,
    }))
}

pub fn pi(domain: Term, body: Term) -> Term {
    raw_term(TermData::Binding(BindingData {
        ty: BindingType::Pi,
        domain,
        body,
    }))
}

pub fn pi_list(terms: &[Term]) -> Term {
    let mut curr = terms[terms.len() - 1].clone();
    for term in terms[..terms.len() - 1].iter().rev() {
        curr = pi(term.clone(), curr);
    }
    curr
}

pub fn lam_list(terms: &[Term]) -> Term {
    let mut curr = terms[terms.len() - 1].clone();
    for term in terms[..terms.len() - 1].iter().rev() {
        curr = lam(term.clone(), curr);
    }
    curr
}

pub fn proj(name: String, index: usize, e: Term) -> Term {
    raw_term(TermData::Proj(name, index, e))
}

pub fn app(f: Term, e: Term) -> Term {
    raw_term(TermData::App(f, e))
}

pub fn app_list(terms: &[Term]) -> Term {
    let mut curr = terms[0].clone();
    for term in &terms[1..] {
        curr = app(curr.clone(), term.clone());
    }
    curr
}

pub fn axiom<S: AsRef<str>>(name: S) -> Term {
    raw_term(TermData::Axiom(name.as_ref().into()))
}

pub fn defn<S: AsRef<str>>(name: S, ty: &Term, value: &Term) -> Term {
    raw_term(TermData::Defn(
        name.as_ref().into(),
        ty.clone(),
        value.clone(),
    ))
}

pub fn defn_witness<S: AsRef<str>>(name: S, ty: &Term, value: &Term, witness: bool) -> Term {
    FACTORY.mk(TaggedTermData::new(
        TermData::Defn(name.as_ref().into(), ty.clone(), value.clone()),
        witness,
    ))
}

pub fn string<S: AsRef<str>>(value: S) -> Term {
    raw_term(TermData::String(value.as_ref().into()))
}

pub fn ind<S: AsRef<str>>(name: S) -> Term {
    raw_term(TermData::Ind(name.as_ref().into()))
}

pub fn ind_ctor<S: AsRef<str>, SP: AsRef<str>>(ind_name: S, ind_ctor: SP) -> Term {
    raw_term(TermData::IndCtor(
        ind_name.as_ref().into(),
        ind_ctor.as_ref().into(),
    ))
}

pub fn ind_rec<S: AsRef<str>>(ind_name: S, motive_sort: usize) -> Term {
    raw_term(TermData::IndRec(ind_name.as_ref().into(), motive_sort))
}

pub fn proj_typer<S: AsRef<str>>(ind_name: S) -> Term {
    raw_term(TermData::ProjTyper(ind_name.as_ref().into()))
}

pub fn garbage_collect() {
    let old_len = FACTORY.read().unwrap().len();
    //if old_len >= *gc_counter.read().unwrap() + 10000 {
    FACTORY.collect_to_fit();
    let collected = old_len - FACTORY.read().unwrap().len();
    if collected > 0 {
        println!(
            "garbage collected {} terms (new_len {})",
            collected,
            FACTORY.read().unwrap().len()
        );
    }
    //*gc_counter.write().unwrap() = FACTORY.read().unwrap().len();
    //}
}

pub struct Evaluator {
    pub inductives: HashMap<String, Inductive>,
    axioms: BTreeMap<String, Term>,

    eval_cache: EvaluationCache,
    ty_cache: EvaluationCache,
    eq_cache: HashMap<(Term, Term), bool>,
    elim_cache: HConMap<Term, Term>,
    lift_cache: HashMap<(Term, isize, usize), Term>,

    tmp_test_cache: HashSet<Vec<Term>>,
}

impl Evaluator {
    pub fn new<S: Into<String>, I: Clone + Into<HashMap<S, Term>>>(
        axioms: &I,
        inductives: HashMap<String, Inductive>,
    ) -> Self {
        let axioms: HashMap<S, Term> = (*axioms).clone().into();
        let mut axioms: BTreeMap<String, Term> =
            axioms.into_iter().map(|(k, v)| (k.into(), v)).collect();
        inductives
            .iter()
            .map(|(s, i)| i.axioms())
            .flatten()
            .for_each(|(name, ty)| {
                axioms.insert(name, ty);
            });

        let mut res = Evaluator {
            inductives,
            axioms,

            eval_cache: EvaluationCache::new(),
            ty_cache: EvaluationCache::new(),
            eq_cache: HashMap::new(),
            elim_cache: HConMap::default(),
            lift_cache: HashMap::new(),

            tmp_test_cache: HashSet::new(),
        };

        for (name, inds) in res.inductives.clone().drain() {
            res.generate_projector(inds);
        }

        res
    }

    pub fn generate_projector(&mut self, inductive: Inductive) {
        for name in inductive.deps() {
            let ind = self.inductives[&name].clone();
            self.generate_projector(ind);
        }

        if inductive.rules.len() != 1
            || self
                .inductives
                .get(&inductive.name)
                .unwrap()
                .projector
                .is_some()
        {
            return;
        }

        let mut ind_ctor = inductive.rules[0].clone();
        let mut ty = inductive.rules[0].ty.clone();
        let params = inductive.rules[0].ty.params();
        let mut ctor_params = params[inductive.num_params..]
            .iter()
            .cloned()
            .collect::<Vec<_>>();
        ctor_params.push(ind_ctor.ty.body().clone());

        let ind_ctor_no_type_params = self.lift(pi_list(&ctor_params), 1).unwrap();
        //let mut param_tys = vec![];
        //let mut params = vec![];
        //let mut args = vec![];

        //let mut idx = 0;
        //let mut context = Context::new();
        //while true {
        //    if let TermData::Binding(BindingData { domain, body, .. }) = &*ty {
        //        let domain_ty = self.ty_with_context(domain.clone(), &mut context).unwrap();
        //        param_tys.push(domain_ty.clone());
        //        context.push(domain.clone());
        //        println!("{}: {}", idx, domain_ty);
        //        if idx < ind.num_params {
        //            params.push(domain.clone())
        //        }
        //        ty = body.clone();
        //    } else {
        //        break;
        //    }
        //    idx += 1;
        //}

        // a b | c d pc2 pd3 4
        let mut proj_context = Context::new();
        let mut apps = vec![proj_typer(&inductive.name)];
        // need to remove universe instantation because lean exporter
        // doesn't know about them...so we deal with them at runtime
        let mut ind_name_parts = inductive.name.split('.').collect::<Vec<_>>();
        let mut ind_name_no_unis = ind_name_parts[0..(ind_name_parts.len() - 1)].join(".");
        let type_args = inductive.ty.params();
        for i in 0..params.len() - inductive.num_params {
            // if we reference another arg, that arg is a proj!
            let projection_arg = ind_ctor_no_type_params.params()[i].clone();
            let res = self
                .eval_with_context(
                    projection_arg,
                    &mut proj_context,
                    &mut Context::new(),
                    true,
                    10,
                )
                .unwrap();
            proj_context.push(proj(ind_name_no_unis.clone(), i, bound(i)));
            apps.push(self.lift(res, -((i) as isize)).unwrap());
        }

        //let apps = self
        //    .lift(
        //        app_list(&apps),
        //        -((params.len() - inductive.num_params) as isize),
        //    )
        //    .unwrap();
        let apps = app_list(&apps);
        let mut ind_type = vec![ind(inductive.name.clone())];
        ind_type.extend((0..inductive.num_params).map(|i| bound(inductive.num_params - i - 1)));
        let ind_type = app_list(&ind_type);
        let mut type_args = inductive.ty.params();
        type_args.push(ind_type);
        type_args.push(apps);
        let projection_typer = pi_list(&type_args);

        self.inductives.get_mut(&inductive.name).unwrap().projector = Some(projection_typer);
    }

    fn empty() -> Evaluator {
        Evaluator {
            inductives: HashMap::new(),
            axioms: BTreeMap::new(),

            eval_cache: EvaluationCache::new(),
            ty_cache: EvaluationCache::new(),
            eq_cache: HashMap::new(),
            elim_cache: HConMap::default(),
            lift_cache: HashMap::new(),

            tmp_test_cache: HashSet::new(),
        }
    }

    pub fn eval(&mut self, term: Term) -> Result<Term, String> {
        self.eval_with_context(term, &mut Context::new(), &mut Context::new(), true, 100)
    }

    //pub fn eval_iter_wrapper(&mut self, term: Term, context: &mut Context) -> Result<Term, String> {
    //    if let Some(res) = self.eval_cache.get(term.clone(), context) {
    //        return Ok(res.clone());
    //    }

    //    let mut stack = Vec::new();
    //    stack.push((term, context.clone(), 0));

    //    while !stack.is_empty() {
    //        let (t, c, children_pushed) = stack.pop();
    //
    //    }
    //}

    pub fn eval_with_context(
        &mut self,
        term: Term,
        context: &mut Context,
        typing_context: &mut Context,
        rec: bool,
        max_depth: usize,
    ) -> Result<Term, String> {
        if let Some(res) = self.eval_cache.get(term.clone(), context) {
            return Ok(res.clone());
        }

        let res = match &**term {
            TermData::Bound(index) => {
                if let Some(bound_term) = context.get_bound(*index) {
                    let res = self
                        .lift(bound_term, *index as isize + 1)
                        .map_err(|s| format!("{} when evaling term {:?}", s, term))?;
                    // We added an eval here because we could replace with a term with an
                    // unresolved recursion
                    self.eval_with_context(res, context, typing_context, rec, max_depth)?
                } else {
                    term.clone()
                }
            }
            TermData::Binding(BindingData { ty, domain, body }) => {
                let domain_value = self.eval_with_context(
                    domain.clone(),
                    context,
                    typing_context,
                    rec,
                    max_depth,
                )?;

                // push a null binding, so we can continue pushing in the body
                context.null_bind();
                typing_context.push(domain_value.clone());
                let body_value =
                    self.eval_with_context(body.clone(), context, typing_context, rec, max_depth)?;
                typing_context.pop();
                context.pop();

                binding(*ty, domain_value, body_value)
            }
            TermData::App(f, e) => {
                let t1_len = typing_context.len();
                let f_value =
                    self.eval_with_context(f.clone(), context, typing_context, rec, max_depth)?;
                let t2_len = typing_context.len();
                let e_value =
                    self.eval_with_context(e.clone(), context, typing_context, rec, max_depth)?;
                let t3_len = typing_context.len();
                assert!(t1_len == t2_len && t2_len == t3_len);

                if let TermData::Binding(BindingData {
                    ty: _,
                    domain,
                    body,
                }) = &**f_value
                {
                    context.push(e_value.clone());
                    typing_context.push(domain.clone());
                    let res = self.eval_with_context(
                        body.clone(),
                        context,
                        typing_context,
                        rec,
                        max_depth,
                    )?;
                    context.pop();
                    typing_context.pop();
                    self.lift(res.clone(), -1).map_err(|s| {
                        format!(
                            "{} when evaling term {:?} (with f_value {:?}, e_value {:?}, body_eval {:?})",
                            s, term, f_value, e_value, res
                        )
                    })?
                } else {
                    app(f_value, e_value)
                }
            }
            // TODO: better debugging for unimplemented terms?
            TermData::Proj(name, index, expr) => {
                let eval_expr =
                    self.eval_with_context(expr.clone(), context, typing_context, rec, max_depth)?;

                // Attempt to evaluate it...
                let res = match &**eval_expr.top_level_func() {
                    TermData::IndCtor(ind_name, rule_name) if ind_name.starts_with(name) => {
                        let ind = self.inductives.get(ind_name).clone().unwrap_or_else(|| {
                            // cant find inductive...fail
                            panic!("Cant find inductive for proj!");
                        });
                        if ind.rules.len() != 1 {
                            return Err("Projection only supported on singletons".to_string());
                        }
                        let args = eval_expr.app_args();
                        args[ind.num_params + *index].clone()
                    }
                    TermData::ProjTyper(ind_name) if ind_name.starts_with(name) => {
                        let ind = self.inductives.get(ind_name).clone().unwrap_or_else(|| {
                            // cant find inductive...fail
                            panic!("Cant find inductive for proj!");
                        });
                        if ind.rules.len() != 1 {
                            return Err("Projection only supported on singletons".to_string());
                        }
                        let args = eval_expr.app_args();
                        args[*index].clone()
                    }
                    _ => proj(name.to_string(), *index, eval_expr),
                };
                res
            }
            TermData::Defn(name, ty, value) => {
                let eval_expr =
                    self.eval_with_context(value.clone(), context, typing_context, rec, max_depth)?;
                eval_expr
            }
            _ => term.clone(),
        };

        let res = //if rec {
            //&& max_depth > 0 {
            if let Some(rec_res) =
                self.try_eval_rec(res.clone(), context, typing_context, max_depth)
            {
                rec_res
            } else {
                res
            };

        // Ensure the returned term is tagged if the input term is tagged.
        let tagged_res = FACTORY.mk(TaggedTermData::new(res.data.clone(), term.flag || res.flag));

        // Cache the result.
        self.eval_cache
            .insert(term.clone(), context, tagged_res.clone());

        debug!(
            "\n C = {:?}\n T = {:?}\n |- {:?} => {:?}",
            context, typing_context, term, tagged_res
        );
        Ok(tagged_res)
    }

    // unwrap apps from a term untill there are only num left.
    // This is used to get the rec correctly...
    fn get_inner_apps(&mut self, term: Term, num: usize) -> Term {
        // get the number of apps for this term
        let mut curr_term = term.clone();
        let mut num_apps = 0;
        while let TermData::App(f, _) = &**curr_term {
            num_apps += 1;
            curr_term = f.clone();
        }
        let mut curr_term = term.clone();
        let mut num_to_remove = num_apps - num;
        while num_to_remove > 0
            && let TermData::App(f, _) = &**curr_term
        {
            num_to_remove -= 1;
            curr_term = f.clone();
        }

        return curr_term;
    }

    // TODO: this is disgusting
    // TODOO: add recursion limit...
    fn try_eval_rec(
        &mut self,
        term: Term,
        context: &mut Context,
        typing_context: &mut Context,
        max_depth: usize,
    ) -> Option<Term> {
        if let TermData::IndRec(rec_ind_name, motive_sort) = &**term.top_level_func() {
            let args = term.app_args();
            let inductive = self.inductives.get(rec_ind_name).unwrap().clone();
            if args.len() == inductive.elim(*motive_sort).params().len() {
                let argument = &args[args.len() - 1];

                if let TermData::IndCtor(ctor_ind_name, rule_name) = &**argument.top_level_func() {
                    if rec_ind_name == ctor_ind_name {
                        if inductive.is_family {
                            panic!(
                                "Recursing on inductive families with recursive params are unsupported (inductive {} : {:?}, {} global params)",
                                inductive.name, inductive.ty, inductive.num_params
                            );
                        }

                        // OK...here is what we will do...
                        // So we will just restrict the inductive definitions a bit
                        // Any index family params that are passed into the type constructor
                        // should come LAST in the rule....
                        // that way we should be able to get them correctly...
                        let rec = self.get_inner_apps(
                            term.clone(),
                            inductive.num_params + 1 + inductive.rules.len(),
                        );

                        let rule_num = inductive.rule_lookup.get(rule_name).expect(&format!(
                            "Couldn't find rule {} in inductive {}",
                            rule_name, ctor_ind_name
                        ));
                        let elim = &args[1 + inductive.global_params().len() + rule_num];

                        let rule_args =
                            argument.app_args()[inductive.global_params().len()..].to_vec();
                        let mut rec_args = Vec::new();
                        let num_rule_args = inductive.rules[*rule_num].ty.params()
                            [inductive.global_params().len()..]
                            .len();
                        let num_index_params = inductive.ty.params().len();
                        for (i, ty) in inductive.rules[*rule_num].ty.params()
                            [inductive.global_params().len()..]
                            .iter()
                            .enumerate()
                        {
                            // if recursive, apply the eliminator again...
                            if let TermData::Ind(ind_name) = &**ty.body().top_level_func() {
                                if ind_name == &inductive.name {
                                    let mut params = rule_args[i].params();
                                    let ind_args =
                                        &ty.body().app_args()[inductive.global_params().len()..];
                                    let rec_lifted =
                                        self.lift(rec.clone(), params.len() as isize).unwrap();
                                    let mut motive_app = vec![rec_lifted];
                                    motive_app.extend(ind_args.iter().cloned());
                                    motive_app.push(rule_args[i].body().clone());
                                    let motive_app = app_list(&motive_app);
                                    params.push(motive_app.clone());
                                    rec_args.push(lam_list(&params));
                                    self.ty_with_context(lam_list(&params), typing_context)
                                        .unwrap();
                                }
                            }
                        }

                        let mut elim_app = vec![elim.clone()];
                        elim_app.extend_from_slice(&rule_args);
                        elim_app.extend_from_slice(&rec_args);

                        let elim = app_list(&elim_app);
                        let res = self
                            .eval_with_context(elim.clone(), context, typing_context, true, 1000)
                            .expect(&format!("FAILED ELIM for {}: {}", inductive.name, **elim));

                        return Some(res);
                    }
                }

                // wts: if a is def equal to a', then we are good...
                if inductive.is_subsingleton() && inductive.name.starts_with("Eq") {
                    // try to convert the arg to "eq" intro....

                    let arg_type = self
                        .ty_with_context(argument.clone(), typing_context)
                        .unwrap();

                    if !matches!(&**arg_type.top_level_func(), TermData::Ind(name) if name == &inductive.name)
                    {
                        return None;
                    }

                    // grab the args we need from the type
                    let type_args = arg_type.app_args();

                    let ctor = &inductive.rules[0];
                    let num_params = ctor.ty.params().len();
                    let ty_params = inductive.num_params;

                    // ensure the ctor has no args except type args, see
                    // https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/K-like.20inductives.20don't.20take.20arguments
                    if num_params != ty_params {
                        return None;
                    }

                    // construct the type using these args
                    let mut ctor_app = ind_ctor(inductive.name.clone(), ctor.name.clone());
                    for i in 0..num_params {
                        ctor_app = app(ctor_app, type_args[i].clone());
                    }
                    // check if the constructed type is definitionally equal to
                    // the arg
                    if !self.def_equals_with_context(
                        ctor_app.clone(),
                        argument.clone(),
                        typing_context,
                    ) {
                        return None;
                    }

                    // simply return the elim... because it is a subsingleton it
                    // it doesn't depend on anything else
                    let elim = &args[1 + inductive.global_params().len()];
                    return Some(elim.clone());
                }
            }
        }

        None
    }

    pub fn ty(&mut self, term: Term) -> Result<Term, String> {
        self.ty_with_context(term, &mut Context::new())
    }

    pub fn ty_with_context(&mut self, term: Term, context: &mut Context) -> Result<Term, String> {
        if let Some(res) = self.ty_cache.get(term.clone(), context) {
            return Ok(res.clone());
        }

        let res = match &**term {
            TermData::Bound(index) => {
                if let Some(bound_term) = context.get_bound(*index) {
                    self.lift(bound_term, *index as isize + 1)?
                } else {
                    return Err(format!(
                        "bound var out of range: {:?}, ctx: {:?}, {:?}",
                        index, context, term
                    ));
                    //Ok(term.clone())
                }
            }
            TermData::Sort(level) => sort(level + 1),
            TermData::Binding(BindingData { ty, domain, body }) => {
                let domain_ty = self.eval_with_context(
                    domain.clone(),
                    &mut Context::new(),
                    context,
                    false,
                    10,
                )?;
                self.ty_with_context(domain_ty.clone(), context)?;
                context.push(domain_ty.clone());
                let body_ty = self.ty_with_context(body.clone(), context)?;
                context.pop();

                match ty {
                    BindingType::Lam => {
                        // TODO: ensure domain_value and body_ty are types
                        pi(domain_ty, body_ty)
                    }
                    BindingType::Pi => {
                        let domain_sort = self.ty_with_context(domain_ty.clone(), context)?;
                        // TODO: ensure domain_value and body ty are sorts
                        let i = if let TermData::Sort(level) = **domain_sort {
                            Ok(level)
                        } else {
                            Err(format!(
                                "Domain {:?} of Pi is not a sort! Got: {:?}",
                                domain, domain_sort
                            ))
                        }?;
                        //context.push(domain_ty.clone());
                        //let body_sort = ty_with_context(body_ty.clone(), axioms, context)?;
                        //context.pop();
                        let j = if let TermData::Sort(level) = **body_ty {
                            Ok(level)
                        } else {
                            // may need to fully evaluate due to impredicative sort.
                            // For example, a term of type
                            // Let B :: Sort(0),
                            // (Pi x: Sort(0).B) a => B :: Sort(0)
                            // However, (Pi x: Sort(0).B) :: Sort(0)
                            //      and B :: Sort(0)
                            // implying that (Pi x: Sort(0).B) a :: app(Sort(0), Sort(0)) which
                            // will fail

                            let body_eval = self.eval_with_context(
                                body.clone(),
                                &mut Context::new(),
                                context,
                                true,
                                10,
                            )?;
                            let evaled_ty = self.ty_with_context(body_eval, context)?;

                            if let TermData::Sort(level) = **evaled_ty {
                                Ok(level)
                            } else {
                                println!(
                                    "Axioms: {:?}\nInductives: {:?}\nContext: {:?}\nTerm: {:?}",
                                    self.axioms, self.inductives, context, term,
                                );
                                assert!(
                                    false,
                                    "{}",
                                    format!(
                                        "Body type {:?} of Pi is not a sort! Got: {:?} (in {:?})",
                                        body, body_ty, term
                                    )
                                );
                                Err(format!(
                                    "Body type {:?} of Pi is not a sort! Got: {:?} (in {:?})",
                                    body, body_ty, term
                                ))
                            }
                        }?;
                        sort(imax(i, j))
                    }
                }
            }
            TermData::App(f, e) => {
                let f_ty = self.ty_with_context(f.clone(), context)?;
                let e_ty = self.ty_with_context(e.clone(), context)?;

                if let TermData::Binding(BindingData {
                    ty: _,
                    domain,
                    body,
                }) = &**f_ty
                {
                    let domain_value = self.eval_with_context(
                        domain.clone(),
                        &mut Context::new(),
                        context,
                        true,
                        10,
                    )?;
                    self.ty_with_context(domain_value.clone(), context).unwrap();
                    let e_ty_value = self.eval_with_context(
                        e_ty.clone(),
                        &mut Context::new(),
                        context,
                        true,
                        10,
                    )?;
                    self.ty_with_context(e_ty_value.clone(), context).unwrap();

                    //if domain_value != e_ty {
                    if !self.def_equals_with_context(
                        domain_value.clone(),
                        e_ty_value.clone(),
                        context,
                    ) {
                        println!("term: {}", **term);
                        println!("f_ty: {}", **f_ty);
                        println!("e: {}", ***e);
                        println!("context: {:?}", context);
                        println!("e_ty: {}", **e_ty);
                        println!("domain: {}", **domain_value);
                        return Err(format!(
                            "Type mismatch: got {}, expected: {}",
                            **e_ty_value, **domain_value
                        ));
                        //return Err("".to_string());
                    }

                    let e_value =
                        self.eval_with_context(e.clone(), &mut Context::new(), context, false, 10)?;
                    self.ty_with_context(e_value.clone(), context)?;
                    context.push(e_value.clone());

                    // TODO: is this right?
                    // Why we need this:
                    // Consider:
                    // ((((Sort(0) => Bound(0) => Bound(1) => Bound(2)) (Bound(8))) Bound(9)) Bound(10))
                    // where everything is the correct type
                    // First step:
                    // ((Sort(0) => Bound(0) => Bound(1) => Bound(2)) (Bound(8))) evals to
                    // (Bound(8) => Bound(9) => Bound(10))... great
                    // BUT:
                    // next step, we want
                    // (Bound(8) => Bound(9) => Bound(10)) (Bound(9)) evals to
                    // Bound(9) => Bound(10)
                    // If we don't restrict substitution to only the
                    // current substitution, we will resolve this to:
                    // (Bound(8) => Bound(9) => Bound(10)) (Bound(9)) evals to
                    // (Sort(0) => Sort(0))
                    let mut test = Context::new();
                    test.push(e_value);
                    // TODO: typing context right?
                    let body_ty =
                        self.eval_with_context(body.clone(), &mut test, context, false, 10)?;
                    self.ty_with_context(body_ty.clone(), context)?;
                    test.pop();
                    context.pop();
                    self.lift(body_ty, -1)?
                } else {
                    app(f_ty, e_ty)
                }
            }
            TermData::Axiom(name) => {
                let axiom = self
                    .axioms
                    .get(name)
                    .cloned()
                    .ok_or(format!("Undefined axiom: '{}'", name))?;
                if !matches!(
                    &**self.ty_with_context(axiom.clone(), context)?,
                    TermData::Sort(_)
                ) {
                    return Err(format!("Axiom {} is not a sort!", name));
                }
                axiom
            }
            TermData::Ind(name) => {
                let ind = self
                    .inductives
                    .get(name)
                    .ok_or(format!("Undefined inductive: {}", name))?;
                ind.ty.clone()
            }
            TermData::IndCtor(name, ctor) => {
                let ind = self
                    .inductives
                    .get(name)
                    .ok_or(format!("Undefined inductive: {}", name))?;
                let ctor_idx = ind.rule_lookup.get(ctor).ok_or(format!(
                    "Undefined ctor {}, for inductive {} (got: {:?})",
                    ctor, name, ind.rule_lookup
                ))?;
                ind.rules[*ctor_idx].ty.clone()
            }
            TermData::IndRec(ind_name, motive_sort) => {
                let ind = self
                    .inductives
                    .get(ind_name)
                    .ok_or(format!("Undefined inductive: {}", ind_name))?;
                let term = ind.elim(*motive_sort);
                term
            }
            TermData::Proj(name, index, expr) => {
                // TODO: proj maybe only works on singletons?
                // LETS TEST>.. fresh assumption: proj only works on singletons...
                // or maybe this is a special case?

                let expr_ty = self.ty_with_context(expr.clone(), context)?;
                let ind = expr_ty.top_level_func();

                if let TermData::Ind(ind_full_name) = &**ind
                    && ind_full_name.starts_with(name)
                {
                    let projector = self.inductives[ind_full_name]
                        .projector
                        .clone()
                        .expect(&format!("Could not unwrap proj: {}", ind_full_name));
                    let mut apps = vec![projector];
                    apps.extend(expr_ty.app_args());
                    apps.push(expr.clone());
                    let proj_term = proj(name.clone(), *index, app_list(&apps));
                    let res = self.eval_with_context(
                        proj_term,
                        &mut Context::new(),
                        &mut Context::new(),
                        true,
                        10,
                    );
                    return res;
                } else {
                    return Err("Proj has ind name which doesn't match expr type!".to_string());
                }
            }
            TermData::ProjTyper(name) => {
                assert!(false, "Should never type a projtyper...");
                unimplemented!();
            }
            TermData::Defn(name, ty, value) => ty.clone(),
            TermData::String(value) => panic!("Cannot operate on strings yet"),
        };

        self.ty_cache.insert(term.clone(), context, res.clone());

        debug!("\n C = {:?}\n |- {:?} :: {:?}", context, term, res);
        Ok(res)
    }

    pub fn def_equals(&mut self, a: Term, b: Term) -> bool {
        self.def_equals_with_context(a, b, &mut Context::new())
    }

    pub fn def_equals_with_context(&mut self, a: Term, b: Term, context: &mut Context) -> bool {
        // fast case
        if a == b {
            return true;
        }

        let a = self
            .eval_with_context(a.clone(), &mut Context::new(), context, true, 10)
            .unwrap();
        let b = self
            .eval_with_context(b.clone(), &mut Context::new(), context, true, 10)
            .unwrap();

        if a == b {
            return true;
        }

        if let Ok(a_ty) = self.ty_with_context(a.clone(), context) {
            if let Ok(b_ty) = self.ty_with_context(b.clone(), context) {
                // proof-irrelevance of prop
                // if a ty and b ty are both p :: Prop, then true
                if let Ok(ty_ty) = self.ty_with_context(a_ty.clone(), context) {
                    if ty_ty == sort(0) && a_ty == b_ty {
                        return true;
                    }
                }

                // eta-expansion
                // TODO: remove redundancy by enforcing one way or the other...
                // if a ty is \x:D -> E and b is not, try eta expansion on b
                if a.is_lambda() && !b.is_lambda() {
                    if let TermData::Binding(BindingData {
                        ty: BindingType::Pi,
                        domain,
                        ..
                    }) = &**b_ty
                    {
                        let expanded_b = lam(
                            domain.clone(),
                            app(self.lift(b.clone(), 1).unwrap(), bound(0)),
                        );
                        if self.def_equals_with_context(a.clone(), expanded_b, context) {
                            return true;
                        }
                    }
                }
                if b.is_lambda() && !a.is_lambda() {
                    if let TermData::Binding(BindingData {
                        ty: BindingType::Pi,
                        domain,
                        ..
                    }) = &**a_ty
                    {
                        let expanded_a = lam(domain.clone(), app(a.clone(), bound(0)));
                        if self.def_equals_with_context(b.clone(), expanded_a, context) {
                            return true;
                        }
                    }
                }
            }
        }

        // otherwise, recurse structurally
        match (&**a, &**b) {
            (
                TermData::Binding(BindingData {
                    ty: a_ty,
                    domain: a_domain,
                    body: a_body,
                }),
                TermData::Binding(BindingData {
                    ty: b_ty,
                    domain: b_domain,
                    body: b_body,
                }),
            ) => {
                let mut res = true;
                res &= a_ty == b_ty
                    && self.def_equals_with_context(a_domain.clone(), b_domain.clone(), context);
                context.push(a_domain.clone());
                res &= self.def_equals_with_context(a_body.clone(), b_body.clone(), context);
                context.pop();
                res
            }
            (TermData::App(a_f, a_e), TermData::App(b_f, b_e)) => {
                self.def_equals_with_context(a_f.clone(), b_f.clone(), context)
                    && self.def_equals_with_context(a_e.clone(), b_e.clone(), context)
            }
            _ => false,
        }
    }

    pub fn lift(&mut self, term: Term, amount: isize) -> Result<Term, String> {
        self.lift_inner(term, amount, 0)
    }

    fn lift_inner(&mut self, term: Term, amount: isize, depth: usize) -> Result<Term, String> {
        if let Some(res) = self.lift_cache.get(&(term.clone(), amount, depth)) {
            return Ok(res.clone());
        }

        let res = match &**term {
            TermData::Bound(index) if *index >= depth => {
                bound(index.checked_add_signed(amount).ok_or(&format!(
                    "Lifting over/underflow evaluating term: {:?}",
                    term
                ))?)
            }
            TermData::Binding(BindingData { ty, domain, body }) => {
                let lifted_domain = self.lift_inner(domain.clone(), amount, depth)?;
                let lifted_body = self.lift_inner(body.clone(), amount, depth + 1)?;
                binding(*ty, lifted_domain, lifted_body)
            }
            TermData::App(f, e) => app(
                self.lift_inner(f.clone(), amount, depth)?,
                self.lift_inner(e.clone(), amount, depth)?,
            ),
            TermData::Proj(name, index, expr) => proj(
                name.clone(),
                *index,
                self.lift_inner(expr.clone(), amount, depth)?,
            ),
            _ => term.clone(),
        };

        self.lift_cache
            .insert((term.clone(), amount, depth), res.clone());
        Ok(res)
    }
}
