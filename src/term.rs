use hashconsing::{consign, hash_coll::HConMap, HConsed, HConsign, HashConsign};
use log::debug;
use std::collections::hash_map::DefaultHasher;
use std::collections::{BTreeMap, HashMap};
use std::hash::{Hash, Hasher};

pub fn imax(i: usize, j: usize) -> usize {
    if j == 0 {
        0
    } else {
        std::cmp::max(i, j)
    }
}

#[derive(Debug)]
pub struct Theorem {
    pub val: Term,
    pub ty: Term,
    pub axioms: BTreeMap<String, Term>,
    pub inductives: HashMap<String, Inductive>,
}

impl Theorem {
    pub fn new(
        val: Term,
        ty: Term,
        axioms: &BTreeMap<String, Term>,
        inductives: &HashMap<String, Inductive>,
    ) -> Theorem {
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
        //let inds: Vec<Inductive> = self.inductives.values().cloned().collect();
        //println!("statement: {:?}\n :: {:?}", self.val, self.ty);
        let mut eval = Evaluator::new(&self.axioms, self.inductives.clone());
        //let test = eval
        //    .eval(self.val.clone())
        //    .map_err(|e| format!("Simplify val err: {}", e))?;
        //println!("simplified {:?}\n ===> {:?}", self.val, test);
        let computed_ty = eval
            .ty(self.val.clone())
            .map_err(|e| format!("Typing error: {}", e))?;
        let simplified_ty = eval
            .eval(self.ty.clone())
            .map_err(|e| format!("Simplify Type error: {}", e))?;
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
}

impl std::fmt::Debug for Context {
    fn fmt(&self, fmt: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        if self.bindings.len() < 3 {
            write!(fmt, "{:?}", self.bindings)
        } else {
            write!(fmt, "[\n")?;
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

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct Inductive {
    name: String,
    num_params: usize,
    ty: Term,
    rules: Vec<InductiveRule>,
    rule_lookup: BTreeMap<String, usize>,

    /// Cached Eliminator body (without global params or motive)
    elim_body: Term,
}

impl Inductive {
    pub fn new(name: &str, num_params: usize, ty: Term, rules: &[InductiveRule]) -> Inductive {
        let rule_lookup = rules
            .iter()
            .enumerate()
            .map(|(index, term)| (term.name.clone(), index))
            .collect();

        // TODO: check consistency
        let mut res = Inductive {
            name: name.to_string(),
            num_params,
            ty,
            rules: rules.to_vec(),
            rule_lookup,
            elim_body: sort(0),
        };

        res.generate_elim_body();
        res
    }

    fn ty_body(&self) -> Term {
        let mut res = &self.ty;
        for i in 0..self.num_params {
            if let TermData::Binding(BindingData { body, .. }) = &**res {
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
            if matches!(*body.body(), TermData::Sort(0)) {
                true
            } else {
                false
            };
        let elide_universe_param = if use_nondependent && self.rules.len() > 1 {
            true
        } else {
            false
        };

        if elide_universe_param && motive_universe_level != 0 {
            panic!("Attempted to instantiate eliminator universe when it should be elided!");
        }

        let mut res = Vec::new();

        // add inductive type params
        let params = &self.ty.params()[..self.num_params];
        res.extend(params.iter().cloned());

        // add motive
        let motive = self.generate_motive(motive_universe_level, use_nondependent);
        res.push(motive);

        res.push(self.elim_body.clone());

        pi_list(&res)
    }

    fn generate_elim_body(&mut self) {
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
            if matches!(*body.body(), TermData::Sort(0)) {
                true
            } else {
                false
            };
        let elide_universe_param = if use_nondependent && self.rules.len() > 1 {
            true
        } else {
            false
        };

        println!(
            "generating elim for {}: nondep? {}, elide_uni? {}, index params len: {}",
            self.name,
            use_nondependent,
            elide_universe_param,
            self.index_params().len()
        );

        let mut res = Vec::new();
        // minor_premise_i : (non_rec_params...) ->
        //                 (rec_params...) ->
        //                 (motive_params...) ->
        //                 motive (minor_premise_i ind_params... non_rec_params... rec_params...)
        for (rule_index, rule) in self.rules.iter().enumerate() {
            println!("generating minor premise: {}", rule_index);
            //if use_nondependent {
            //    res.push(self.generate_minor_premise_nondependent(rule_index, rule));
            //} else {
            //    res.push(self.generate_minor_premise_dependent(rule_index, rule));
            //}
            res.push(self.generate_minor_premise(rule_index, rule, !use_nondependent, &mut eval));
            //println!("got premise {:?}", self.generate_minor_premise(rule_index, rule, !use_nondependent, &mut eval));
        }

        // generate the major premise
        println!("generating major premise");

        // push index params
        let mut major_premise_pis = Vec::new();
        for param in self.index_params() {
            major_premise_pis.push(eval.lift(param, (self.rules.len() + 1) as isize).unwrap())
        }

        let mut ind_ty_apps = vec![axiom(self.name.clone())];
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
        //println!(
        //    "global param bindings: {:?}",
        //    global_param_bindings.collect::<Vec<_>>()
        //);
        //println!(
        //    "index param bindings: {:?}",
        //    index_param_bindings.collect::<Vec<_>>()
        //);
        ind_ty_apps.extend(global_param_bindings);
        ind_ty_apps.extend(index_param_bindings);
        let ind_ty = app_list(&ind_ty_apps);
        major_premise_pis.push(ind_ty);

        let motive_binding = bound(major_premise_pis.len() + self.rules.len());
        let mut final_motive_apps = vec![motive_binding];

        // skip actual major premise inductive type if we are non-dependent
        let motive_args_len = if !use_nondependent {
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
        println!("elim done");

        self.elim_body = pi_list(&res);
    }

    fn generate_motive(&self, motive_universe_level: usize, use_nondependent: bool) -> Term {
        let mut res_pi_list = self.index_params();

        if !use_nondependent {
            // construct the recursive param
            let mut ind_app_list = vec![axiom(self.name.clone())];
            let global_bindings = (0..self.global_params().len())
                .map(|i| bound(self.global_params().len() - 1 - i + res_pi_list.len()));
            ind_app_list.extend(global_bindings);
            let index_bindings =
                (0..self.index_params().len()).map(|i| bound(self.global_params().len() - 1 - i));
            ind_app_list.extend(index_bindings);
            let ind = app_list(&ind_app_list);
            res_pi_list.push(ind);
        }
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
            println!("generating premise param: {}", param_index);
            minor_premise_args.push(
                eval.lift_inner(param.clone(), rule_index as isize + 1, param_index)
                    .unwrap(),
            );

            // if param is recursive, also push (motive arg) to rec params
            let param_func = param.top_level_func();
            match &*param_func {
                TermData::Axiom(name) if name == &self.name => {
                    let motive_binding =
                        bound(rule_params.len() + minor_premise_motive_args.len() + rule_index);
                    let mut motive_params = vec![motive_binding];
                    motive_params.extend_from_slice(
                        &eval
                            .lift(
                                param.clone(),
                                (rule_params.len() - 1 - param_index
                                    + 1
                                    + minor_premise_motive_args.len())
                                    as isize,
                            )
                            .unwrap()
                            .app_args()[self.num_params..],
                    );
                    // if dependent, add recursive arg to motive
                    if dependent {
                        let orig_param_binding = bound(
                            rule_params.len() - 1 - param_index + minor_premise_motive_args.len(),
                        );
                        motive_params.push(orig_param_binding);
                    }
                    //println!("motive param {}: {:?}", param_index, motive_params);
                    minor_premise_motive_args.push(app_list(&motive_params));
                }
                _ => {}
            }
        }

        println!("generating premise body");
        //println!("rule body: {:?}", rule.ty.body());
        //println!("num params: {:?}", self.num_params);
        let motive_binding =
            bound(minor_premise_args.len() + minor_premise_motive_args.len() + rule_index);
        let mut premise_body_apps = vec![motive_binding];
        // lift global params
        // TODO: do I need to separately lift global params? No right?
        let result_args = &eval
            .lift_inner(
                rule.ty.body(),
                (minor_premise_args.len() + minor_premise_motive_args.len() + rule_index + 1)
                    as isize,
                rule_params.len(),
                //rule_params.len(),
            )
            .unwrap();
        let result_args = &eval
            .lift_inner(
                result_args.clone(),
                (minor_premise_motive_args.len()) as isize,
                0,
                //rule_params.len(),
            )
            .unwrap()
            .app_args()[self.num_params..];
        //println!("got result args: {:?}", result_args);
        premise_body_apps.extend_from_slice(result_args);

        // inductive arg for the minor_premise body
        if dependent {
            let inductive_arg = {
                let mut recursive_arg_apps = vec![axiom(rule.name.clone())];
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
            //println!("inductive arg: {:?}", inductive_arg);
            premise_body_apps.push(inductive_arg);
        }

        let premise_body = app_list(&premise_body_apps);

        let mut result = minor_premise_args;
        result.extend(minor_premise_motive_args);
        result.push(premise_body);
        let result = pi_list(&result);
        //println!("minor premise for {:?}: \n\t{:?}", rule.ty, result);
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
        //println!("minor premise for {:?}: \n\t{:?}", rule.ty, res);
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
    name: String,
    ty: Term,
}

impl InductiveRule {
    pub fn new(name: &str, ty: Term) -> InductiveRule {
        InductiveRule {
            name: name.to_string(),
            ty,
        }
    }
}

impl std::fmt::Debug for InductiveRule {
    fn fmt(&self, fmt: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(fmt, "{} : {:?}", self.name, self.ty)
    }
}

consign! {
    let FACTORY = consign(0) for TermData;
}

pub type Term = HConsed<TermData>;

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
}

impl TermData {
    fn params(&self) -> Vec<Term> {
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

    fn body(&self) -> Term {
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
        if let Some(size) = cache
            .as_ref()
            .map(|c| c.get(&raw_term(self.clone())))
            .flatten()
        {
            return *size;
        }
        let res = match self {
            TermData::Bound(_) | TermData::Sort(_) | TermData::Axiom(_) => 1,
            TermData::Binding(BindingData { domain, body, .. }) => {
                domain.size(cache) + body.size(cache)
            }
            TermData::App(f, e) => f.size(cache) + e.size(cache),
        };
        cache
            .as_mut()
            .map(|c| c.insert(raw_term(self.clone()), res));
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
        match self {
            TermData::Bound(index) => {
                write!(fmt, "Bound({})", index)
            }
            TermData::Sort(index) => {
                write!(fmt, "Sort({})", index)
            }
            TermData::Binding(BindingData { ty, domain, body }) => {
                write!(fmt, "{:?}({:?}, {:?})", ty, domain, body)
            }
            TermData::App(f, e) => {
                write!(fmt, "App({:?}, {:?})", f, e)
            }
            TermData::Axiom(name) => {
                write!(fmt, "Axiom({})", name)
            }
        }
    }
}

pub fn raw_term(data: TermData) -> Term {
    FACTORY.mk(data)
}

pub fn bound(index: usize) -> Term {
    FACTORY.mk(TermData::Bound(index))
}

pub fn sort(level: usize) -> Term {
    FACTORY.mk(TermData::Sort(level))
}

pub fn binding(ty: BindingType, domain: Term, body: Term) -> Term {
    let binding_data = BindingData { ty, domain, body };
    FACTORY.mk(TermData::Binding(binding_data))
}

pub fn lam(domain: Term, body: Term) -> Term {
    let binding_data = BindingData {
        ty: BindingType::Lam,
        domain,
        body,
    };
    FACTORY.mk(TermData::Binding(binding_data))
}

pub fn pi(domain: Term, body: Term) -> Term {
    let binding_data = BindingData {
        ty: BindingType::Pi,
        domain,
        body,
    };
    FACTORY.mk(TermData::Binding(binding_data))
}

pub fn pi_list(terms: &[Term]) -> Term {
    let mut curr = terms[terms.len() - 1].clone();
    for term in terms[..terms.len() - 1].iter().rev() {
        curr = pi(term.clone(), curr);
    }
    curr
}

pub fn app(f: Term, e: Term) -> Term {
    FACTORY.mk(TermData::App(f, e))
}

pub fn app_list(terms: &[Term]) -> Term {
    let mut curr = terms[0].clone();
    for term in &terms[1..] {
        curr = app(curr.clone(), term.clone());
    }
    curr
}

pub fn axiom<S: AsRef<str>>(name: S) -> Term {
    FACTORY.mk(TermData::Axiom(name.as_ref().into()))
}

pub struct Evaluator {
    inductives: HashMap<String, Inductive>,
    axioms: BTreeMap<String, Term>,

    eval_cache: HashMap<(Term, u64), Term>,
    ty_cache: HashMap<(Term, u64), Term>,
    eq_cache: HashMap<(Term, Term), bool>,
    lift_cache: HashMap<(Term, isize, usize), Term>,
}

impl Evaluator {
    pub fn new<S: Into<String>, I: Clone + Into<BTreeMap<S, Term>>>(
        axioms: &I,
        inductives: HashMap<String, Inductive>,
    ) -> Self {
        let axioms: BTreeMap<S, Term> = (*axioms).clone().into();
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

            eval_cache: HashMap::new(),
            ty_cache: HashMap::new(),
            eq_cache: HashMap::new(),
            lift_cache: HashMap::new(),
        };

        //println!("------------------ Checking axioms ------------------");
        //for (name, axiom) in res.axioms.clone() {
        //    println!("checking axiom {:?}", name);
        //    res.ty(axiom.clone()).map_err(|s| format!("While checking axiom {} of type {:?}\nGot error: {}", name, axiom, s)).unwrap();
        //}
        //println!("------------------ Done Checking axioms ------------------");
        res
    }

    fn empty() -> Evaluator {
        Evaluator {
            inductives: HashMap::new(),
            axioms: BTreeMap::new(),

            eval_cache: HashMap::new(),
            ty_cache: HashMap::new(),
            eq_cache: HashMap::new(),
            lift_cache: HashMap::new(),
        }
    }

    pub fn eval(&mut self, term: Term) -> Result<Term, String> {
        self.eval_with_context(term, &mut Context::new(), &mut Context::new())
    }

    pub fn eval_with_context(
        &mut self,
        term: Term,
        context: &mut Context,
        types: &mut Context,
    ) -> Result<Term, String> {
        if let Some(res) = self.eval_cache.get(&(term.clone(), context.hash())) {
            return Ok(res.clone());
        }

        let res = match &*term {
            TermData::Bound(index) => {
                if let Some(bound_term) = context.get_bound(*index) {
                    self.lift(bound_term, *index as isize + 1)
                        .map_err(|s| format!("{} when evaling term {:?}", s, term))?
                } else {
                    term.clone()
                }
            }
            TermData::Binding(BindingData { ty, domain, body }) => {
                let domain_value = self.eval_with_context(domain.clone(), context, types)?;

                // push a null binding, so we can continue pushing in the body
                context.null_bind();
                types.push(domain.clone());
                let body_value = self.eval_with_context(body.clone(), context, types)?;
                types.pop();
                context.pop();

                binding(*ty, domain_value, body_value)
            }
            TermData::App(f, e) => {
                let f_value = self.eval_with_context(f.clone(), context, types)?;
                let e_value = self.eval_with_context(e.clone(), context, types)?;

                if let TermData::Binding(BindingData {
                    ty: _,
                    domain,
                    body,
                }) = &*f_value
                {
                    context.push(e_value.clone());
                    types.push(domain.clone());
                    let res = self.eval_with_context(body.clone(), context, types)?;
                    types.pop();
                    context.pop();
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
            _ => term.clone(),
        };

        let res = if let Some(rec_res) = self.try_eval_rec(res.clone(), context, types) {
            rec_res
        } else {
            res
        };

        self.eval_cache
            .insert((term.clone(), context.hash()), res.clone());

        debug!("\n C = {:?}\n |- {:?} => {:?}", context, term, res);
        Ok(res)
    }

    fn try_eval_rec(
        &mut self,
        term: Term,
        context: &mut Context,
        types: &mut Context,
    ) -> Option<Term> {
        if let TermData::Axiom(name) = &*term.top_level_func() {
            if name.contains(".rec") {
                let args = term.app_args();
                let inductive_name = name.split(".rec").next().unwrap();
                let inductive = self.inductives.get(inductive_name).unwrap().clone();
                if args.len() == inductive.elim(0).params().len() {
                    let argument = &args[args.len() - 1];
                    if let TermData::Axiom(rule) = &*argument.top_level_func() {
                        let (ind_base_name, ind_universe_string) =
                            inductive_name.rsplit_once(".").unwrap();

                        // match rec with the inductive name
                        if rule.starts_with(ind_base_name)
                            && rule.ends_with(ind_universe_string)
                            && rule != inductive_name
                            && !rule.contains("rec")
                        {
                            let rec = match &*term {
                                TermData::App(f, _) => f,
                                _ => {
                                    panic!("Not an app");
                                }
                            };

                            let rule_num = inductive.rule_lookup.get(rule).expect(&format!("Couldn't find rule number {} of inductive {:?} inside expr {:?} (ind_base_name {}, ind_universe_string {})", rule, inductive_name, argument, ind_base_name, ind_universe_string));
                            let elim = &args[1 + inductive.global_params().len() + rule_num];

                            let rule_args =
                                argument.app_args()[inductive.global_params().len()..].to_vec();
                            let mut rec_args = Vec::new();
                            for (i, ty) in inductive.rules[*rule_num].ty.params()
                                [inductive.global_params().len()..]
                                .iter()
                                .enumerate()
                            {
                                // if recursive, apply the eliminator again...
                                if let TermData::Axiom(name) = &*ty.top_level_func() {
                                    if name == &inductive.name {
                                        // TODO: can do eval later or even better lazily
                                        rec_args.push(app(rec.clone(), rule_args[i].clone()));
                                    }
                                }
                            }

                            let mut elim_app = vec![elim.clone()];
                            elim_app.extend_from_slice(&rule_args);
                            elim_app.extend_from_slice(&rec_args);

                            let elim = app_list(&elim_app);
                            let new_res = self
                                .eval_with_context(elim.clone(), context, types)
                                .unwrap();
                            println!("got eval {:?}\n\t=> {:?}", term, new_res);
                            return Some(new_res);
                        }
                    }
                }
            }
        }

        None
    }

    pub fn ty(&mut self, term: Term) -> Result<Term, String> {
        self.ty_with_context(term, &mut Context::new())
    }

    pub fn ty_with_context(&mut self, term: Term, context: &mut Context) -> Result<Term, String> {
        if let Some(res) = self.ty_cache.get(&(term.clone(), context.hash())) {
            return Ok(res.clone());
        }

        debug!("\n C = {:?}\n Typing {:?}", context, term);
        let res = match &*term {
            TermData::Bound(index) => {
                if let Some(bound_term) = context.get_bound(*index) {
                    self.lift(bound_term, *index as isize + 1)?
                } else {
                    panic!("bound var test");
                    //Ok(term.clone())
                }
            }
            TermData::Sort(level) => sort(level + 1),
            TermData::Binding(BindingData { ty, domain, body }) => {
                let domain_ty =
                    self.eval_with_context(domain.clone(), &mut Context::new(), context)?;
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
                        let i = if let TermData::Sort(level) = *domain_sort {
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
                        let j = if let TermData::Sort(level) = *body_ty {
                            Ok(level)
                        } else {
                            //println!(
                            //    "Axioms: {:?}\nInductives: {:?}\nContext: {:?}\nTerm: {:?}",
                            //    self.axioms, self.inductives, context, term,
                            //);
                            Err(format!(
                                "Body type {:?} of Pi is not a sort! Got: {:?} (in {:?})",
                                body, body_ty, term
                            ))
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
                }) = &*f_ty
                {
                    let domain_value =
                        self.eval_with_context(domain.clone(), &mut Context::new(), context)?;
                    self.ty_with_context(domain_value.clone(), context).unwrap();
                    let e_ty_value =
                        self.eval_with_context(e_ty.clone(), &mut Context::new(), context)?;
                    self.ty_with_context(e_ty.clone(), context).unwrap();

                    //if domain_value != e_ty {
                    if !self.def_equals_with_context(
                        domain_value.clone(),
                        e_ty_value.clone(),
                        context,
                    ) {
                        //println!(
                        //    "Axioms: {:?}\nInductives: {:?}\nContext: {:?}\nTerm: {:?}\nFunc Type: {:?}\nArg Type: {:?}",
                        //    self.axioms, self.inductives, context, term, f_ty, e_ty
                        //);
                        //println!(
                        //    "Type mismatch: got {:?}, expected: {:?}",
                        //    e_ty, domain_value
                        //);
                        println!("pprod: {:?}", self.inductives.get("pprod.{1,2}"));
                        println!(
                            "Context: {:?}\nTerm: {:?}\nFunc Type: {:?}\nArg Type: {:?}, e_ty_value: {:?}\n",
                            context, term, f_ty, e_ty, e_ty_value
                        );
                        //println!(
                        //    "acc.{{1}}.rec.{{1}}: {:?}",
                        //    self.axioms.get("acc.{1}.rec.{1}")
                        //);
                        return Err(format!(
                            "Type mismatch: got {:?}, expected: {:?}",
                            e_ty, domain_value
                        ));
                    }

                    let e_value =
                        self.eval_with_context(e.clone(), &mut Context::new(), context)?;
                    self.ty_with_context(e_value.clone(), context).unwrap();
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
                    let body_ty = self.eval_with_context(body.clone(), &mut test, context)?;
                    self.ty_with_context(body_ty.clone(), context).unwrap();
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
                    &*self.ty_with_context(axiom.clone(), context)?,
                    TermData::Sort(_)
                ) {
                    return Err(format!("Axiom {} is not a sort!", name));
                }
                axiom
            }
        };

        self.ty_cache
            .insert((term.clone(), context.hash()), res.clone());

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

        //match (*a, *b) {
        //    (
        //        TermData::Binding(BindingData {
        //            ty: a_ty,
        //            domain: a_domain,
        //            body: a_body,
        //        }),
        //        TermData::Binding(BindingData {
        //            ty: b_ty,
        //            domain: b_domain,
        //            body: b_body,
        //        }),
        //    ) => {
        //        let mut res = true;
        //        res &= a_ty == b_ty
        //            && self.def_equals_with_context(a_domain.clone(), b_domain, context);
        //        context.push(a_domain);
        //        res &= self.def_equals_with_context(a_body, b_body, context);
        //        context.pop();
        //        res
        //    }
        //    (TermData::App(a_f, a_e), TermData::App(b_f, b_e)) => {
        //        self.def_equals_with_context(a_f, b_f, context)
        //            && self.def_equals_with_context(a_e, b_e, context)
        //    },
        //    (TermData::
        //}

        //println!("def eq: {:?} {:?}", a, b);
        if let Ok(a_ty) = self.ty_with_context(a.clone(), context) {
            if let Ok(b_ty) = self.ty_with_context(b.clone(), context) {
                //println!("a ty: {:?}, b ty: {:?}", a_ty, b_ty);
                // if a ty and b ty are both p :: Prop, then true
                if let Ok(ty_ty) = self.ty_with_context(a_ty.clone(), context) {
                    if ty_ty == sort(0) && a_ty == b_ty {
                        return true;
                    }
                }

                // TODO: remove redundancy by enforcing one way or the other...
                // if a ty is \x:D -> E and b is not, try eta expansion on b
                if a.is_lambda() && !b.is_lambda() {
                    if let TermData::Binding(BindingData {
                        ty: BindingType::Pi,
                        domain,
                        ..
                    }) = &*b_ty
                    {
                        let expanded_b = lam(
                            domain.clone(),
                            app(self.lift(b.clone(), 1).unwrap(), bound(0)),
                        );
                        //println!("expanded b: {:?}", expanded_b);
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
                    }) = &*a_ty
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
        match (&*a, &*b) {
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

        // TODO: eta reduction
    }

    pub fn lift(&mut self, term: Term, amount: isize) -> Result<Term, String> {
        self.lift_inner(term, amount, 0)
    }

    fn lift_inner(&mut self, term: Term, amount: isize, depth: usize) -> Result<Term, String> {
        if let Some(res) = self.lift_cache.get(&(term.clone(), amount, depth)) {
            return Ok(res.clone());
        }

        let res = match &*term {
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
            _ => term.clone(),
        };

        self.lift_cache
            .insert((term.clone(), amount, depth), res.clone());
        Ok(res)
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn eval_simple_app() {
        let mut eval = Evaluator::empty();
        let expr = app(lam(sort(0), bound(0)), bound(1));
        assert_eq!(eval.eval(expr), Ok(bound(1)));
    }

    #[test]
    fn eval_lift() {
        let mut eval = Evaluator::empty();
        let expr = app(lam(sort(0), lam(sort(0), bound(1))), bound(2));
        assert_eq!(eval.eval(expr), Ok(lam(sort(0), bound(3))));

        let expr = app(
            lam(sort(0), lam(sort(0), bound(1))),
            app(bound(2), bound(3)),
        );
        assert_eq!(eval.eval(expr), Ok(lam(sort(0), app(bound(3), bound(4)))));
    }

    #[test]
    fn eval_unlift() {
        let mut eval = Evaluator::empty();
        let expr = app(
            lam(sort(0), lam(sort(0), app(bound(1), bound(3)))),
            bound(2),
        );
        assert_eq!(eval.eval(expr), Ok(lam(sort(0), app(bound(3), bound(2)))));
    }

    #[test]
    fn eval_arith_basic() {
        let mut eval = Evaluator::empty();
        let sum = lam(
            sort(0),
            lam(
                sort(0),
                lam(
                    sort(0),
                    lam(
                        sort(0),
                        app(
                            app(bound(3), bound(1)),
                            app(app(bound(2), bound(1)), bound(0)),
                        ),
                    ),
                ),
            ),
        );
        let zero = lam(sort(0), lam(sort(0), bound(0)));
        let soln = lam(
            sort(0),
            lam(
                sort(0),
                lam(sort(0), app(app(bound(2), bound(1)), bound(0))),
            ),
        );
        let one = lam(sort(0), lam(sort(0), app(bound(1), bound(0))));
        assert_eq!(eval.eval(app(sum.clone(), zero.clone())), Ok(soln.clone()));
        assert_eq!(eval.eval(app(soln.clone(), zero.clone())), Ok(zero.clone()));
        assert_eq!(eval.eval(app(soln.clone(), one.clone())), Ok(one.clone()));

        let soln = lam(
            sort(0),
            lam(
                sort(0),
                lam(
                    sort(0),
                    app(bound(1), app(app(bound(2), bound(1)), bound(0))),
                ),
            ),
        );
        assert_eq!(eval.eval(app(sum, one.clone())), Ok(soln.clone()));
        assert_eq!(eval.eval(app(soln, zero)), Ok(one));
    }

    #[test]
    fn eval_arith() {
        for m in 0..10 {
            for n in 0..10 {
                do_eval_arith(m, n);
            }
        }
    }

    fn do_eval_arith(m: isize, n: isize) {
        let mut eval = Evaluator::empty();
        let applications = |x: isize| {
            let mut res = bound(0);
            for _ in 0..x {
                res = app(bound(1), res);
            }
            res
        };

        let m_enc = lam(sort(0), lam(sort(0), applications(m)));
        let n_enc = lam(sort(0), lam(sort(0), applications(n)));
        let sum_enc = lam(
            sort(0),
            lam(
                sort(0),
                lam(
                    sort(0),
                    lam(
                        sort(0),
                        app(
                            app(bound(3), bound(1)),
                            app(app(bound(2), bound(1)), bound(0)),
                        ),
                    ),
                ),
            ),
        );
        let soln = lam(sort(0), lam(sort(0), applications(m + n)));
        let res = eval.eval(app(app(sum_enc, m_enc), n_enc));

        assert_eq!(res, Ok(soln));
    }

    #[test]
    fn type_int() {
        let axioms = [("int", sort(0)), ("x", axiom("int"))];
        let mut eval = Evaluator::new(&axioms, HashMap::new());

        assert_eq!(eval.ty(axiom("int")), Ok(sort(0)));
        assert_eq!(eval.ty(axiom("x")), Ok(axiom("int")));
    }

    #[test]
    fn type_undefined_axiom() {
        let axioms = [("x", axiom("int"))];
        let mut eval = Evaluator::new(&axioms, HashMap::new());
        assert_eq!(
            eval.ty(axiom("x")),
            Err("Undefined axiom: 'int'".to_string())
        );
    }

    #[test]
    fn type_lam() {
        let mut eval = Evaluator::empty();
        assert_eq!(
            eval.ty(lam(sort(0), lam(bound(0), bound(0)))),
            Ok(pi(sort(0), pi(bound(0), bound(1))))
        );
        assert_eq!(
            eval.ty(lam(sort(0), lam(bound(0), bound(1)))),
            Ok(pi(sort(0), pi(bound(0), sort(0))))
        );
        // assert_eq!(
        //     eval.ty(lam(sort(0), pi(bound(0), bound(0)))),
        //     Err("Body type Bound(0) of Pi is not a sort! Got: Bound(1)".to_string())
        // );
    }

    #[test]
    fn type_prop() {
        let axioms = [
            ("depFunc", pi(sort(0), pi(bound(0), bound(1)))),
            ("func", pi(sort(0), bound(0))),
            ("p", sort(0)),
            ("proofP", axiom("p")),
        ];
        let mut eval = Evaluator::new(&axioms, HashMap::new());

        assert_eq!(eval.ty(axiom("p")), Ok(sort(0)));
        assert_eq!(eval.ty(axiom("proofP")), Ok(axiom("p")));
        assert_eq!(eval.ty(app(axiom("func"), axiom("p"))), Ok(axiom("p")));
        assert_eq!(
            eval.ty(axiom("depFunc")),
            Ok(pi(sort(0), pi(bound(0), bound(1))))
        );
        // TODO: is this wrong?
        assert_eq!(
            eval.ty(app(axiom("depFunc"), axiom("p"))),
            Ok(pi(axiom("p"), axiom("p")))
        );
        let expr = app(app(axiom("depFunc"), axiom("p")), axiom("proofP"));
        assert_eq!(eval.ty(expr), Ok(axiom("p")));
    }

    #[test]
    fn type_vec() {
        let axioms = [
            ("one", axiom("nat")),
            ("nat", sort(1)),
            ("vector", pi(axiom("nat"), sort(1))),
        ];
        let mut eval = Evaluator::new(&axioms, HashMap::new());

        let expr = app(axiom("vector"), axiom("one"));
        assert_eq!(eval.ty(expr), Ok(sort(1)));
    }

    #[test]
    fn test_type_impred() {
        let axioms = [("p", sort(0))];
        let mut eval = Evaluator::new(&axioms, HashMap::new());

        let expr = pi(sort(2), axiom("p"));
        assert_eq!(eval.ty(expr), Ok(sort(0)));
    }

    #[test]
    fn test_type_and() {
        let axioms = [
            ("and", pi(sort(0), pi(sort(0), sort(0)))),
            ("p", sort(0)),
            ("q", sort(0)),
            ("proofP", axiom("p")),
            ("proofQ", axiom("q")),
            ("pImplQ", pi(axiom("p"), axiom("q"))),
            (
                "andIntro",
                (pi(
                    sort(0),
                    pi(
                        sort(0),
                        pi(
                            bound(1),
                            pi(bound(1), app(app(axiom("and"), bound(3)), bound(2))),
                        ),
                    ),
                )),
            ),
        ];
        let mut eval = Evaluator::new(&axioms, HashMap::new());

        let expr = app(axiom("pImplQ"), axiom("p"));
        assert_eq!(
            eval.ty(expr),
            Err("Type mismatch: got Sort(0), expected: Axiom(p)".to_string())
        );

        let expr = app(axiom("pImplQ"), axiom("proofP"));
        assert_eq!(eval.ty(expr), Ok(axiom("q")));

        let expr = app(
            app(
                app(app(axiom("andIntro"), axiom("p")), axiom("q")),
                axiom("proofP"),
            ),
            axiom("proofQ"),
        );
        assert_eq!(
            eval.ty(expr),
            Ok(app(app(axiom("and"), axiom("p")), axiom("q")))
        );
    }

    #[test]
    fn test_type_dist() {
        let axioms = [
            ("and", pi(sort(0), pi(sort(0), sort(0)))),
            ("or", pi(sort(0), pi(sort(0), sort(0)))),
            ("p", sort(0)),
            ("q", sort(0)),
            ("proofP", axiom("p")),
            ("proofQ", axiom("q")),
            ("pImplQ", pi(axiom("p"), axiom("q"))),
            (
                "andIntro",
                (pi(
                    sort(0),
                    pi(
                        sort(0),
                        pi(
                            pi(bound(0), bound(1)),
                            app(app(axiom("and"), bound(0)), bound(1)),
                        ),
                    ),
                )),
            ),
            (
                "ori1",
                pi(
                    sort(0),
                    pi(
                        sort(0),
                        pi(bound(1), app(app(axiom("or"), bound(2)), bound(1))),
                    ),
                ),
            ),
        ];
        let mut eval = Evaluator::new(&axioms, HashMap::new());

        let expr = app(axiom("ori1"), axiom("p"));
        let res = pi(
            sort(0),
            pi(axiom("p"), app(app(axiom("or"), axiom("p")), bound(1))),
        );
        assert_eq!(eval.ty(expr), Ok(res));

        let expr = app(
            app(app(axiom("ori1"), axiom("p")), axiom("q")),
            axiom("proofP"),
        );
        let res = app(app(axiom("or"), axiom("p")), axiom("q"));
        assert_eq!(eval.ty(expr), Ok(res));
    }

    #[test]
    fn type_induction_elim_simple() {
        let rules = [
            InductiveRule {
                name: "or.inr".to_string(),
                ty: pi(
                    sort(0),
                    pi(
                        sort(0),
                        pi(bound(0), app(app(axiom("or"), bound(1)), bound(2))),
                    ),
                ),
            },
            InductiveRule {
                name: "or.inl".to_string(),
                ty: pi(
                    sort(0),
                    pi(
                        sort(0),
                        pi(bound(1), app(app(axiom("or"), bound(1)), bound(2))),
                    ),
                ),
            },
        ];
        let or = Inductive::new("or", 2, pi(sort(0), pi(sort(0), sort(0))), &rules);

        let correct_motive = sort(0);
        assert_eq!(or.generate_motive(0, true), correct_motive);

        let correct_elim = pi(
            sort(0),
            pi(
                sort(0),
                pi(
                    sort(0),
                    pi(
                        pi(bound(1), bound(1)),
                        pi(
                            pi(bound(3), bound(2)),
                            pi(app(app(axiom("or"), bound(4)), bound(3)), bound(3)),
                        ),
                    ),
                ),
            ),
        );

        assert_eq!(or.elim(0), correct_elim);

        let axioms = [
            ("a", sort(0)),
            ("b", sort(0)),
            ("bImpla", pi(axiom("b"), axiom("a"))),
            ("or.rec", or.elim(0)),
        ];
        let inductives = HashMap::from([("or".into(), or)]);
        let mut eval = Evaluator::new(&axioms, inductives);
        assert_eq!(eval.ty(axiom("or.rec")), Ok(correct_elim));

        assert_eq!(
            eval.ty(app(
                app(
                    app(
                        app(app(axiom("or.rec"), axiom("a")), axiom("b")),
                        axiom("a")
                    ),
                    axiom("bImpla")
                ),
                lam(axiom("a"), bound(0))
            )),
            Ok(pi(
                app(app(axiom("or"), axiom("a")), axiom("b")),
                axiom("a")
            ))
        );
    }

    // Test with a Type and single recursive constructor
    #[test]
    fn type_induction_elim_nat() {
        let rules = [
            InductiveRule {
                name: "nat.zero".to_string(),
                ty: axiom("nat"),
            },
            InductiveRule {
                name: "nat.succ".to_string(),
                ty: pi(axiom("nat"), axiom("nat")),
            },
        ];
        let nat = Inductive::new("nat", 0, sort(1), &rules);
        let correct_elim = pi(
            pi(axiom("nat"), sort(1)),
            pi(
                app(bound(0), axiom("nat.zero")),
                pi(
                    pi(
                        axiom("nat"),
                        pi(
                            app(bound(2), bound(0)),
                            app(bound(3), app(axiom("nat.succ"), bound(1))),
                        ),
                    ),
                    pi(axiom("nat"), app(bound(3), bound(0))),
                ),
            ),
        );

        assert_eq!(nat.elim(1), correct_elim);
        let inductives = HashMap::from([("nat".into(), nat.clone())]);
        let mut eval = Evaluator::new(&[("nat.rec", nat.elim(1))], inductives);
        assert_eq!(eval.ty(axiom("nat.rec")), Ok(correct_elim));

        assert_eq!(
            eval.ty(app(
                app(
                    app(axiom("nat.rec"), lam(axiom("nat"), axiom("nat"))),
                    axiom("nat.zero")
                ),
                lam(
                    axiom("nat"),
                    lam(axiom("nat"), app(axiom("nat.succ"), bound(1)))
                )
            )),
            Ok(pi(axiom("nat"), axiom("nat")))
        );
    }

    // Test with a Type and multiple recursive constructors
    #[test]
    fn type_induction_elim_bintree() {
        let rules = [
            InductiveRule {
                name: "bintree.empty".to_string(),
                ty: pi(sort(1), app(axiom("bintree"), bound(0))),
            },
            InductiveRule {
                name: "bintree.leaf".to_string(),
                ty: pi(sort(1), pi(bound(0), app(axiom("bintree"), bound(1)))),
            },
            InductiveRule {
                name: "bintree.node".to_string(),
                ty: pi(
                    sort(1),
                    pi(
                        app(axiom("bintree"), bound(0)),
                        pi(
                            app(axiom("bintree"), bound(1)),
                            app(axiom("bintree"), bound(2)),
                        ),
                    ),
                ),
            },
        ];
        let bintree = Inductive::new("bintree", 1, pi(sort(1), sort(1)), &rules);
        let correct_elim = pi_list(&[
            sort(1),
            pi(app(axiom("bintree"), bound(0)), sort(1)),
            app(bound(0), app(axiom("bintree.empty"), bound(1))),
            pi(
                bound(2),
                app(
                    bound(2),
                    app(app(axiom("bintree.leaf"), bound(3)), bound(0)),
                ),
            ),
            pi(
                app(axiom("bintree"), bound(3)),
                pi(
                    app(axiom("bintree"), bound(4)),
                    pi(
                        app(bound(4), bound(1)),
                        pi(
                            app(bound(5), bound(1)),
                            app(
                                bound(6),
                                app(
                                    app(app(axiom("bintree.node"), bound(7)), bound(3)),
                                    bound(2),
                                ),
                            ),
                        ),
                    ),
                ),
            ),
            pi(app(axiom("bintree"), bound(4)), app(bound(4), bound(0))),
        ]);

        // println!("bintree.elim: {:?}", bintree.elim());
        assert_eq!(bintree.elim(1), correct_elim);

        let nat_rules = [
            InductiveRule {
                name: "nat.zero".to_string(),
                ty: axiom("nat"),
            },
            InductiveRule {
                name: "nat.succ".to_string(),
                ty: pi(axiom("nat"), axiom("nat")),
            },
        ];
        let nat = Inductive::new("nat", 0, sort(1), &nat_rules);

        let inductives = HashMap::from([("nat".into(), nat), ("bintree".into(), bintree.clone())]);
        let mut eval = Evaluator::new(&[("bintree.rec", bintree.elim(1))], inductives); //, nat]);
        assert_eq!(eval.ty(correct_elim), Ok(sort(2)),);

        // Almost a summation of nodes in the tree....
        // Test that once evaluation of recursion is done
        assert_eq!(
            eval.ty(app(
                app(
                    app(
                        app(
                            app(axiom("bintree.rec"), axiom("nat")),
                            lam(app(axiom("bintree"), axiom("nat")), axiom("nat"))
                        ),
                        axiom("nat.zero")
                    ),
                    lam(axiom("nat"), bound(0)),
                ),
                lam(
                    app(axiom("bintree"), axiom("nat")),
                    lam(
                        app(axiom("bintree"), axiom("nat")),
                        lam(axiom("nat"), lam(axiom("nat"), axiom("nat.zero")))
                    )
                )
            )),
            Ok(pi(app(axiom("bintree"), axiom("nat")), axiom("nat"))),
        );
    }

    // Test with a Prop and takes a universe param
    #[test]
    fn type_induction_elim_and() {
        let rules = [InductiveRule {
            name: "and.intro".to_string(),
            ty: pi(
                sort(0),
                pi(
                    sort(0),
                    pi(
                        bound(1),
                        pi(bound(1), app(app(axiom("and"), bound(3)), bound(2))),
                    ),
                ),
            ),
        }];
        let and = Inductive::new("and", 2, pi(sort(0), pi(sort(0), sort(0))), &rules);
        // TODO: add universe params
        let correct_elim = pi_list(&[
            sort(0),
            sort(0),
            sort(1),
            pi(bound(2), pi(bound(2), bound(2))),
            app(app(axiom("and"), bound(3)), bound(2)),
            bound(2),
        ]);
        assert_eq!(and.elim(1), correct_elim);
    }

    #[test]
    fn type_induction_elim_leq_rec_prop() {
        let rules = [
            InductiveRule {
                name: "nat.less_than_or_equal.refl".to_string(),
                ty: pi(
                    axiom("nat"),
                    app(app(axiom("nat.less_than_or_equal"), bound(0)), bound(0)),
                ),
            },
            InductiveRule {
                name: "nat.less_than_or_equal.step".to_string(),
                ty: pi(
                    axiom("nat"),
                    pi(
                        axiom("nat"),
                        pi(
                            app(app(axiom("nat.less_than_or_equal"), bound(1)), bound(0)),
                            app(
                                app(axiom("nat.less_than_or_equal"), bound(2)),
                                app(axiom("nat.succ"), bound(1)),
                            ),
                        ),
                    ),
                ),
            },
        ];
        let leq = Inductive::new(
            "nat.less_than_or_equal",
            1,
            pi(axiom("nat"), pi(axiom("nat"), sort(0))),
            &rules,
        );

        let correct_motive = pi(axiom("nat"), sort(0));

        assert_eq!(leq.generate_motive(0, true), correct_motive);

        let correct_elim = pi_list(&[
            axiom("nat"),
            pi(axiom("nat"), sort(0)),
            app(bound(0), bound(1)),
            pi(
                axiom("nat"),
                pi(
                    app(app(axiom("nat.less_than_or_equal"), bound(3)), bound(0)),
                    pi(
                        app(bound(3), bound(1)),
                        app(bound(4), app(axiom("nat.succ"), bound(2))),
                    ),
                ),
            ),
            pi(
                axiom("nat"),
                pi(
                    app(app(axiom("nat.less_than_or_equal"), bound(4)), bound(0)),
                    app(bound(4), bound(1)),
                ),
            ),
        ]);
        assert_eq!(leq.elim(0), correct_elim);
        //assert_eq!(leq.

        //let rec_on = lam(
        //    axiom("nat"),
        //    lam(
        //        pi(axiom("nat"), sort(0)),
        //        lam(
        //            axiom("nat"),
        //            lam(
        //                app(app(axiom("nat.less_than_or_equal"), bound(2)), bound(0)),
        //                lam(
        //                    app(bound(2), bound(3)),
        //                    lam(
        //                        pi(
        //                            axiom("nat"),
        //                            pi(
        //                                app(
        //                                    app(axiom("nat.less_than_or_equal"), bound(5)),
        //                                    bound(0),
        //                                ),
        //                                pi(
        //                                    app(bound(5), bound(1)),
        //                                    app(bound(6), app(axiom("nat.succ"), bound(2))),
        //                                ),
        //                            ),
        //                        ),
        //                        app(
        //                            app(
        //                                app(
        //                                    app(
        //                                        app(
        //                                            app(
        //                                                axiom("nat.less_than_or_equal.rec.{0}"),
        //                                                bound(5),
        //                                            ),
        //                                            bound(4),
        //                                        ),
        //                                        bound(1),
        //                                    ),
        //                                    bound(0),
        //                                ),
        //                                bound(3),
        //                            ),
        //                            bound(2),
        //                        ),
        //                    ),
        //                ),
        //            ),
        //        ),
        //    ),
        //);
    }

    #[test]
    fn type_induction_elim_leq_rec_sort() {
        let rules = [
            InductiveRule {
                name: "nat.less_than_or_equal.refl".to_string(),
                ty: pi(
                    axiom("nat"),
                    app(app(axiom("nat.less_than_or_equal"), bound(0)), bound(0)),
                ),
            },
            InductiveRule {
                name: "nat.less_than_or_equal.step".to_string(),
                ty: pi(
                    axiom("nat"),
                    pi(
                        axiom("nat"),
                        pi(
                            app(app(axiom("nat.less_than_or_equal"), bound(1)), bound(0)),
                            app(
                                app(axiom("nat.less_than_or_equal"), bound(2)),
                                app(axiom("nat.succ"), bound(1)),
                            ),
                        ),
                    ),
                ),
            },
        ];
        let leq = Inductive::new(
            "nat.less_than_or_equal",
            1,
            pi(axiom("nat"), pi(axiom("nat"), sort(1))),
            &rules,
        );

        let correct_motive = pi(
            axiom("nat"),
            pi(
                app(app(axiom("nat.less_than_or_equal"), bound(1)), bound(0)),
                sort(1),
            ),
        );

        assert_eq!(leq.generate_motive(1, false), correct_motive);

        let correct_elim = pi_list(&[
            axiom("nat"),
            pi(
                axiom("nat"),
                pi(
                    app(app(axiom("nat.less_than_or_equal"), bound(1)), bound(0)),
                    sort(0),
                ),
            ),
            app(
                app(bound(0), bound(1)),
                app(axiom("nat.less_than_or_equal.refl"), bound(1)),
            ),
            pi(
                axiom("nat"),
                pi(
                    app(app(axiom("nat.less_than_or_equal"), bound(3)), bound(0)),
                    pi(
                        app(app(bound(3), bound(1)), bound(0)),
                        app(
                            app(bound(4), app(axiom("nat.succ"), bound(2))),
                            app(
                                app(
                                    app(axiom("nat.less_than_or_equal.step"), bound(5)),
                                    bound(2),
                                ),
                                bound(1),
                            ),
                        ),
                    ),
                ),
            ),
            pi(
                axiom("nat"),
                pi(
                    app(app(axiom("nat.less_than_or_equal"), bound(4)), bound(0)),
                    app(app(bound(4), bound(1)), bound(0)),
                ),
            ),
        ]);
        assert_eq!(leq.elim(0), correct_elim);
        //assert_eq!(leq.

        //let rec_on = lam(
        //    axiom("nat"),
        //    lam(
        //        pi(axiom("nat"), sort(0)),
        //        lam(
        //            axiom("nat"),
        //            lam(
        //                app(app(axiom("nat.less_than_or_equal"), bound(2)), bound(0)),
        //                lam(
        //                    app(bound(2), bound(3)),
        //                    lam(
        //                        pi(
        //                            axiom("nat"),
        //                            pi(
        //                                app(
        //                                    app(axiom("nat.less_than_or_equal"), bound(5)),
        //                                    bound(0),
        //                                ),
        //                                pi(
        //                                    app(bound(5), bound(1)),
        //                                    app(bound(6), app(axiom("nat.succ"), bound(2))),
        //                                ),
        //                            ),
        //                        ),
        //                        app(
        //                            app(
        //                                app(
        //                                    app(
        //                                        app(
        //                                            app(
        //                                                axiom("nat.less_than_or_equal.rec.{0}"),
        //                                                bound(5),
        //                                            ),
        //                                            bound(4),
        //                                        ),
        //                                        bound(1),
        //                                    ),
        //                                    bound(0),
        //                                ),
        //                                bound(3),
        //                            ),
        //                            bound(2),
        //                        ),
        //                    ),
        //                ),
        //            ),
        //        ),
        //    ),
        //);
    }

    #[test]
    fn type_induction_elim_has_le_regression() {
        // TODO:
        let rules = [InductiveRule {
            name: "has_le.mk".to_string(),
            ty: pi(
                sort(1),
                pi(
                    pi(bound(0), pi(bound(1), sort(0))),
                    app(axiom("has_le"), bound(1)),
                ),
            ),
        }];
        let has_le = Inductive::new("has_le", 1, pi(sort(0), sort(0)), &rules);

        // TODO:
        //let correct_elim = pi_list(
        //    &[
        //        sort(kkk
        //    ]
        //);
    }

    #[test]
    fn type_induction_elim_pprod_regression() {
        // TODO:
        let rules = [InductiveRule {
            name: "pprod.mk".to_string(),
            ty: pi(
                sort(9),
                pi(
                    sort(9),
                    pi(
                        bound(1),
                        pi(bound(1), app(app(axiom("pprod"), bound(3)), bound(2))),
                    ),
                ),
            ),
        }];
        let pprod = Inductive::new("pprod", 2, pi(sort(9), pi(sort(9), sort(9))), &rules);
        println!("pprod elim: {:?}", pprod.elim(9));
        //let correct_elim = pi_list(&[
        //    sort(1),
        //    pi(app(axiom("bintree"), bound(0)), sort(1)),
        //    app(bound(0), app(axiom("bintree.empty"), bound(1))),
        //    pi(
        //        bound(2),
        //        app(
        //            bound(2),
        //            app(app(axiom("bintree.leaf"), bound(3)), bound(0)),
        //        ),
        //    ),
        //    pi(
        //        app(axiom("bintree"), bound(3)),
        //        pi(
        //            app(axiom("bintree"), bound(4)),
        //            pi(
        //                app(bound(4), bound(1)),
        //                pi(
        //                    app(bound(5), bound(1)),
        //                    app(
        //                        bound(6),
        //                        app(
        //                            app(app(axiom("bintree.node"), bound(7)), bound(3)),
        //                            bound(2),
        //                        ),
        //                    ),
        //                ),
        //            ),
        //        ),
        //    ),
        //    pi(app(axiom("bintree"), bound(4)), app(bound(4), bound(0))),
        //]);

        //// println!("bintree.elim: {:?}", bintree.elim());
        //assert_eq!(bintree.elim(), correct_elim);

        //let nat_rules = [
        //    InductiveRule {
        //        name: "nat.zero".to_string(),
        //        ty: axiom("nat"),
        //    },
        //    InductiveRule {
        //        name: "nat.succ".to_string(),
        //        ty: pi(axiom("nat"), axiom("nat")),
        //    },
        //];
        //let nat = Inductive::new("nat", sort(1), &nat_rules);

        //let expr = lam(
        //    app(app(axiom("pprod"), bound(1)), bound(0)),
        //    app(
        //        app(
        //            app(
        //                app(app(axiom("pprod.rec"), bound(2)), bound(1)),
        //                lam(app(app(axiom("pprod"), bound(2)), bound(1)), bound(3)),
        //            ),
        //            lam(bound(2), lam(bound(2), bound(1))),
        //        ),
        //        bound(0),
        //    ),
        //);
    }

    #[test]
    fn elim_eval_le_succ_of_le_regression() {
        let nat_rules = [
            InductiveRule {
                name: "nat.zero.{}".to_string(),
                ty: axiom("nat.{}"),
            },
            InductiveRule {
                name: "nat.succ.{}".to_string(),
                ty: pi(axiom("nat.{}"), axiom("nat.{}")),
            },
        ];
        let nat = Inductive::new("nat.{}", 0, sort(1), &nat_rules);

        let nat_le_rules = [
            InductiveRule {
                name: "nat.less_than_or_equal.refl.{}".to_string(),
                ty: pi(
                    axiom("nat.{}"),
                    app(app(axiom("nat.less_than_or_equal.{}"), bound(0)), bound(0)),
                ),
            },
            InductiveRule {
                name: "nat.less_than_or_equal.step.{}".to_string(),
                ty: pi(
                    axiom("nat.{}"),
                    pi(
                        axiom("nat.{}"),
                        pi(
                            app(app(axiom("nat.less_than_or_equal.{}"), bound(1)), bound(0)),
                            app(
                                app(axiom("nat.less_than_or_equal.{}"), bound(2)),
                                app(axiom("nat.succ.{}"), bound(1)),
                            ),
                        ),
                    ),
                ),
            },
        ];
        let nat_le = Inductive::new(
            "nat.less_than_or_equal.{}",
            1,
            pi(axiom("nat.{}"), pi(axiom("nat.{}"), sort(0))),
            &nat_le_rules,
        );

        let has_le_rules = [InductiveRule {
            name: "has_le.mk.{0}".to_string(),
            ty: pi(
                sort(1),
                pi(
                    pi(bound(0), pi(bound(1), sort(0))),
                    app(axiom("has_le.{0}"), bound(1)),
                ),
            ),
        }];
        let has_le = Inductive::new("has_le.{0}", 1, pi(sort(1), sort(1)), &has_le_rules);

        let axioms = [
            ("has_le.{0}.rec.{1}", has_le.elim(1)),
            ("nat.less_than_or_equal.{}.rec.{0}", nat_le.elim(0)),
        ];
        let inductives = HashMap::from([
            ("nat.{}".into(), nat),
            ("nat.less_than_or_equal.{}".into(), nat_le),
            ("has_le.{0}".into(), has_le),
        ]);
        let mut eval = Evaluator::new(&axioms, inductives); //, nat]);
                                                            //
        let expected_ty = pi(
            axiom("nat.{}"),
            pi(
                axiom("nat.{}"),
                pi(
                    app(app(axiom("nat.less_than_or_equal.{}"), bound(1)), bound(0)),
                    app(
                        app(axiom("nat.less_than_or_equal.{}"), bound(2)),
                        app(axiom("nat.succ.{}"), bound(1)),
                    ),
                ),
            ),
        );
        // minimized test case
        let minimized_expr = lam(
            axiom("nat.{}"),
            lam(
                axiom("nat.{}"),
                lam(
                    app(app(axiom("nat.less_than_or_equal.{}"), bound(1)), bound(0)),
                    app(
                        app(
                            app(
                                app(
                                    app(
                                        app(axiom("nat.less_than_or_equal.{}.rec.{0}"), bound(1)),
                                        app(axiom("nat.less_than_or_equal.{}"), bound(2)),
                                    ),
                                    bound(0),
                                ),
                                lam(
                                    axiom("nat.{}"),
                                    lam(
                                        app(
                                            app(axiom("nat.less_than_or_equal.{}"), bound(2)),
                                            bound(0),
                                        ),
                                        app(
                                            app(axiom("nat.less_than_or_equal.step.{}"), bound(4)),
                                            bound(1),
                                        ),
                                    ),
                                ),
                            ),
                            app(axiom("nat.succ.{}"), bound(1)),
                        ),
                        app(
                            app(
                                app(axiom("nat.less_than_or_equal.step.{}"), bound(1)),
                                bound(1),
                            ),
                            app(axiom("nat.less_than_or_equal.refl.{}"), bound(1)),
                        ),
                    ),
                ),
            ),
        );
        assert_eq!(eval.ty(minimized_expr.clone()), Ok(expected_ty.clone()));
        let evaled_expr = eval.eval(minimized_expr.clone());
        assert_eq!(
            eval.ty(evaled_expr.clone().unwrap()),
            Ok(expected_ty.clone())
        );

        let expr = lam(axiom("nat.{}"), lam(axiom("nat.{}"), lam(app(app(axiom("nat.less_than_or_equal.{}"), bound(1)), bound(0)), app(app(app(app(app(lam(axiom("nat.{}"), lam(axiom("nat.{}"), lam(axiom("nat.{}"), lam(app(app(app(app(lam(sort(1), lam(app(axiom("has_le.{0}"), bound(0)), app(app(app(app(axiom("has_le.{0}.rec.{1}"), bound(1)), lam(app(axiom("has_le.{0}"), bound(1)), pi(bound(2), pi(bound(3), sort(0))))), lam(pi(bound(1), pi(bound(2), sort(0))), bound(0))), bound(0)))), axiom("nat.{}")), app(app(axiom("has_le.mk.{0}"), axiom("nat.{}")), axiom("nat.less_than_or_equal.{}"))), bound(2)), bound(1)), app(app(app(app(app(axiom("nat.less_than_or_equal.{}.rec.{0}"), bound(2)), app(app(app(lam(sort(1), lam(app(axiom("has_le.{0}"), bound(0)), app(app(app(app(axiom("has_le.{0}.rec.{1}"), bound(1)), lam(app(axiom("has_le.{0}"), bound(1)), pi(bound(2), pi(bound(3), sort(0))))), lam(pi(bound(1), pi(bound(2), sort(0))), bound(0))), bound(0)))), axiom("nat.{}")), app(app(axiom("has_le.mk.{0}"), axiom("nat.{}")), axiom("nat.less_than_or_equal.{}"))), bound(3))), bound(0)), lam(axiom("nat.{}"), lam(app(app(axiom("nat.less_than_or_equal.{}"), bound(3)), bound(0)), app(app(axiom("nat.less_than_or_equal.step.{}"), bound(5)), bound(1))))), bound(1)))))), bound(2)), bound(1)), app(axiom("nat.succ.{}"), bound(1))), bound(0)), app(lam(axiom("nat.{}"), app(app(app(axiom("nat.less_than_or_equal.step.{}"), bound(0)), bound(0)), app(lam(axiom("nat.{}"), app(axiom("nat.less_than_or_equal.refl.{}"), bound(0))), bound(0)))), bound(1))))));
        assert_eq!(eval.ty(expr.clone()), Ok(expected_ty.clone()));
        let evaled_expr = eval.eval(expr.clone());
        assert_eq!(
            eval.ty(evaled_expr.clone().unwrap()),
            Ok(expected_ty.clone())
        );
    }
}
