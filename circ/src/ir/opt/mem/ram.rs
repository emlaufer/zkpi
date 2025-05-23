/// RAM extraction
///
/// See the documentation for [extract]
use log::debug;

use crate::ir::opt::visit::RewritePass;
use crate::ir::term::extras::Letified;
use crate::ir::term::*;
use std::collections::VecDeque;

#[derive(Debug)]
/// An access to a RAM
pub struct Access {
    /// Whether this is a read or a write.
    pub is_write: Term,
    /// The index/address.
    pub idx: Term,
    /// The value written or read.
    pub val: Term,
}

impl Access {
    fn new_read(idx: Term, val: Term) -> Self {
        Self {
            idx,
            val,
            is_write: bool_lit(false),
        }
    }
    fn new_write(idx: Term, val: Term, guard: Term) -> Self {
        Self {
            idx,
            val,
            is_write: guard,
        }
    }
    fn to_tuple(&self, idx_sort: Sort, i: Option<usize>) -> Term {
        let idx_field = match idx_sort {
            Sort::Field(field) => field,
            _ => panic!("Cannot use RAM on non-field index type!"),
        };
        if let Some(i) = i {
            term![Op::Tuple; self.idx.clone(), pf_lit(idx_field.new_v::<usize>(i)), self.val.clone()]
        } else {
            term![Op::Tuple; self.idx.clone(),  self.val.clone()]
        }
    }
}

fn multiset_hash(terms: impl IntoIterator<Item = Term>, alpha: &Term) -> Term {
    let field = match check(alpha) {
        Sort::Field(field) => field,
        _ => panic!("Alpha value for universal hash isn't a field!"),
    };

    let factors = terms
        .into_iter()
        .map(|t| {
            // construct (alpha - t) for each term
            assert_eq!(
                check(&t),
                Sort::Field(field.clone()),
                "Term in multiset hash doesn't have correct field type!"
            );
            term![PF_ADD; alpha.clone(), term![PF_NEG; t.clone()]]
        })
        .collect();

    term(PF_MUL, factors)
}

fn waksman(ram: &Ram, computation: &mut Computation, epoch_cache: &mut TermMap<u8>) -> Ram {
    let idx_field = match &ram.idx_sort {
        Sort::Field(field) => field,
        _ => panic!("Cannot use RAM on non-field index type!"),
    };

    let field_tuples: Vec<Term> = ram
        .accesses
        .iter()
        .enumerate()
        .map(|(i, a)| a.to_tuple(ram.idx_sort.clone(), Some(i)))
        .collect();
    let tuple_array = make_array(
        ram.idx_sort.clone(),
        check(&field_tuples[0]),
        field_tuples.clone(),
    );
    let switch_settings_tuple = term![Op::Waksman; tuple_array];
    let n = check(&switch_settings_tuple).as_tuple().len();

    let mut switch_settings: VecDeque<Term> = (0..n)
        .map(|i| {
            computation.new_var(
                &format!("__ram_switch_{}_{}", ram.id, i),
                Sort::Bool,
                Some(crate::ir::proof::PROVER_ID),
                ram.epoch, // TODO
                false,
                Some(term![Op::Field(i); switch_settings_tuple.clone()]),
            )
        })
        .collect();

    let sorted_field_tuple_values: Vec<Term> =
        circ_waksman::symbolic_apply(field_tuples, &mut switch_settings, &mut crossbar);

    assert!(switch_settings.is_empty());

    let mut sorted_accesses = Vec::new();
    for i in 0..ram.accesses.len() {
        // create an input for each field
        // TODO: create a check + stronger opt where we elide all writes
        //       when we have a pattern of "all writes" -> "all reads",
        //       where val is the value from the last write
        //let is_write_name = format!("__ram_srow_{}_{}.is_write", ramid, i);
        let idx_name = format!("__ram_srow_{}_{}.idx", ram.id, i);
        let val_name = format!("__ram_srow_{}_{}.val", ram.id, i);

        let idx_term = term_c![Op::Field(0); sorted_field_tuple_values[i]];
        let val_term = term_c![Op::Field(2); sorted_field_tuple_values[i]];
        let access = Access {
            is_write: bool_lit(false),
            idx: idx_term,
            val: val_term,
        };
        sorted_accesses.push(access);
    }

    Ram {
        id: ram.id,
        init_val: ram.init_val.clone(),
        size: ram.size,
        accesses: sorted_accesses,
        idx_sort: ram.idx_sort.clone(),
        val_sort: ram.val_sort.clone(),
        epoch: ram.epoch,
    }
}

fn crossbar(top: &Term, bot: &Term, switch: Term) -> (Term, Term) {
    debug_assert_eq!(check(top), check(bot));
    (
        term_c![Op::Ite; &switch, bot, top],
        term_c![Op::Ite; &switch, top, bot],
    )
}

/// Constructs a term representing the unviersal hash of all terms passed in.
/// Tuples and Arrays are handled recursively
fn universal_hash(terms: impl IntoIterator<Item = Term>, beta: &Term) -> Term {
    let field = match check(beta) {
        Sort::Field(field) => field,
        _ => panic!("Beta value for universal hash isn't a field!"),
    };

    // TODO: is extending the iterator here better?
    let mut stack: Vec<Term> = terms.into_iter().collect();
    let mut results: Vec<Term> = Vec::new();
    let mut factor_index = 0;
    while !stack.is_empty() {
        let curr_term = stack.pop().unwrap();
        match check(&curr_term) {
            Sort::Tuple(sorts) => {
                stack.extend((0..sorts.len()).map(|i| term![Op::Field(i); curr_term.clone()]));
            }
            Sort::Array(k, _, n) => {
                stack.extend((0..n).map(|i| {
                    let idx = match k.as_ref() {
                        Sort::Field(field_typ) => Value::Field(field_typ.new_v(i)),
                        Sort::BitVector(width) => {
                            Value::BitVector(BitVector::new(rug::Integer::from(i), *width))
                        }
                        _ => panic!("RAM: We don't support arrays with indices other than Field or Bitvector"),
                    };
                    term![Op::Select; curr_term.clone(), term![Op::Const(idx)]]
                }));
            }
            _ => {
                //let mut factors = vec![beta.clone(); factor_index];
                if factor_index != 0 {
                    let beta_power = term(PF_MUL, vec![beta.clone(); factor_index]);
                    results.push(term![PF_MUL; beta_power, cast_to_field(&curr_term, &field)]);
                } else {
                    results.push(cast_to_field(&curr_term, &field));
                }
                //factors.push(cast_to_field(&curr_term, &field));
                factor_index += 1;
            }
        }
    }
    //println!("Universal hash factors: {:?}", results);
    term(PF_ADD, results)
}

fn cast_to_field(term: &Term, field: &circ_fields::FieldT) -> Term {
    match check(term) {
        Sort::Field(_) => term.clone(),
        Sort::BitVector(_) => term![Op::UbvToPf(field.clone()); term.clone()],
        Sort::Bool => term![Op::UbvToPf(field.clone()); term![Op::BoolToBv; term.clone()]],
        _ => panic!("Cannot cast term of type {:?} to field!", check(term)),
    }
}

#[derive(Debug)]
/// A RAM transcript
pub struct Ram {
    /// The unique id of this RAM
    pub id: usize,
    /// The starting value of all cells
    pub init_val: Value,
    /// The size
    pub size: usize,
    /// The list of accesses (in access order)
    pub accesses: Vec<Access>,
    /// The index sort
    pub idx_sort: Sort,
    /// The value sort
    pub val_sort: Sort,
    /// Epoch,
    pub epoch: u8,
}

impl Ram {
    fn new(id: usize, const_: Array) -> Self {
        //assert_eq!(const_.map.len(), 0, "Map? {:?}", const_.map);
        Ram {
            id,
            val_sort: const_.default.sort(),
            idx_sort: const_.key_sort,
            accesses: vec![],
            size: const_.size,
            init_val: *const_.default,
            epoch: 0,
        }
    }
    fn new_read(
        &mut self,
        idx: Term,
        computation: &mut Computation,
        read_value: Term,
        epoch_cache: &mut TermMap<u8>,
    ) -> Term {
        let val_name = format!("__ram_{}_{}", self.id, self.accesses.len());
        debug_assert_eq!(&check(&idx), &self.idx_sort);
        let epoch = extras::epoch(read_value.clone(), computation, epoch_cache);
        // Ram epoch is max of all values
        self.epoch = std::cmp::max(self.epoch, epoch);
        let var = computation.new_var(
            &val_name,
            check(&read_value),
            Some(crate::ir::proof::PROVER_ID),
            epoch, // TODO: correct?
            false,
            Some(read_value),
        );
        self.accesses.push(Access::new_read(idx, var.clone()));
        var
    }

    fn new_write(&mut self, idx: Term, val: Term, guard: Term) {
        debug_assert_eq!(&check(&idx), &self.idx_sort);
        debug_assert_eq!(&check(&val), &self.val_sort);
        debug_assert_eq!(&check(&guard), &Sort::Bool);
        self.accesses.push(Access::new_write(idx, val, guard));
    }

    fn sorted_by_index(&self, computation: &mut Computation, epoch_cache: &mut TermMap<u8>) -> Ram {
        let idx_terms: Vec<Term> = self
            .accesses
            .iter()
            .map(|access| access.idx.clone())
            .collect();
        let idx_field = match &self.idx_sort {
            Sort::Field(field) => field,
            _ => panic!("Cannot use RAM on non-field index type!"),
        };

        // construct array for precompute of ram indices
        //let idx_tuples = self.accesses.iter()
        //    .enumerate()
        //    .map(|(i, a)| term![Op::Tuple; pf_lit(idx_field.new_v::<usize>(i)), a.idx.clone()])
        //    .collect();
        //let idx_array_term = term(Op::Array(self.idx_sort.clone(), self.idx_sort.clone()), idx_tuples);
        //let idx_array_name = format!("__ram_idxs_{}", self.id);
        //let idx_array_epoch = extras::epoch(
        //    idx_array_term.clone(),
        //    computation,
        //    epoch_cache,
        //);
        //let idx_array_var = computation.new_var(
        //    &idx_array_name,
        //    Sort::Array(Box::new(self.idx_sort.clone()), Box::new(self.idx_sort.clone()), self.accesses.len()),
        //    Some(crate::ir::proof::PROVER_ID),
        //    idx_array_epoch,
        //    false,
        //    Some(idx_array_term),
        //);

        // create array from i->(idx,val) to precompute correct values from sorted idxs
        let empty_arr = leaf_term(Op::Const(Value::Array(Array::default(
            self.idx_sort.clone(),
            &self.val_sort,
            self.size,
        ))));
        let val_tuples = self
            .accesses
            .iter()
            .map(|a| a.to_tuple(self.idx_sort.clone(), None))
            .collect();
        let val_array_term = term(
            Op::Array(
                self.idx_sort.clone(),
                Sort::Tuple(Box::new([self.idx_sort.clone(), self.val_sort.clone()])),
            ),
            val_tuples,
        );
        let val_array_name = format!("__ram_vals_{}", self.id);
        let val_array_epoch = extras::epoch(val_array_term.clone(), computation, epoch_cache);
        let val_array_var = computation.new_var(
            &val_array_name,
            Sort::Array(
                Box::new(self.idx_sort.clone()),
                Box::new(Sort::Tuple(Box::new([
                    self.idx_sort.clone(),
                    self.val_sort.clone(),
                ]))),
                self.accesses.len(),
            ),
            Some(crate::ir::proof::PROVER_ID),
            val_array_epoch,
            false,
            Some(val_array_term),
        );
        // TODO: add vars for both arrays, maybe will be better?

        // sort array by index
        let sorted_idx_array_term = term![Op::Sort; val_array_var.clone()];
        let sorted_idx_array_name = format!("__ram_sorted_array_{}", self.id);
        let sorted_idx_array_var = computation.new_var(
            &sorted_idx_array_name,
            Sort::Array(
                Box::new(self.idx_sort.clone()),
                Box::new(Sort::Tuple(Box::new([
                    self.idx_sort.clone(),
                    self.val_sort.clone(),
                ]))),
                self.accesses.len(),
            ),
            Some(crate::ir::proof::PROVER_ID),
            val_array_epoch,
            false,
            Some(sorted_idx_array_term),
        );
        // construct a term that ensures __ram_srows are a witness to the ordering
        // constraints on __ram values
        let mut sorted_accesses = Vec::new();
        for i in 0..self.accesses.len() {
            // create an input for each field
            // TODO: create a check + stronger opt where we elide all writes
            //       when we have a pattern of "all writes" -> "all reads",
            //       where val is the value from the last write
            //let is_write_name = format!("__ram_srow_{}_{}.is_write", ramid, i);
            let idx_name = format!("__ram_srow_{}_{}.idx", self.id, i);
            let val_name = format!("__ram_srow_{}_{}.val", self.id, i);

            let idx_term = term![Op::Field(0); term![Op::Select; sorted_idx_array_var.clone(), pf_lit(idx_field.new_v::<usize>(i))]];
            let val_term = term![Op::Field(1); term![Op::Select; sorted_idx_array_var.clone(), pf_lit(idx_field.new_v::<usize>(i))]];
            let idx_epoch = extras::epoch(idx_term.clone(), computation, epoch_cache);
            let val_epoch = extras::epoch(val_term.clone(), computation, epoch_cache);
            let idx = computation.new_var(
                &idx_name,
                self.idx_sort.clone(),
                Some(crate::ir::proof::PROVER_ID),
                idx_epoch, // TODO
                false,
                Some(idx_term),
            );
            let val = computation.new_var(
                &val_name,
                self.val_sort.clone(),
                Some(crate::ir::proof::PROVER_ID),
                val_epoch, // TODO
                false,
                Some(val_term),
            );
            let access = Access {
                is_write: bool_lit(false),
                idx,
                val,
            };
            sorted_accesses.push(access);
        }

        Ram {
            id: self.id,
            init_val: self.init_val.clone(),
            size: self.size,
            accesses: sorted_accesses,
            idx_sort: self.idx_sort.clone(),
            val_sort: self.val_sort.clone(),
            epoch: 0,
        }
    }
}

/// Parse `ite` as a conditional store (arr, idx, val, guard)
fn parse_cond_store(ite: &Term) -> Option<ConditionalStore> {
    if ite.op == Op::Ite && ite.cs[1].op == Op::Store && ite.cs[1].cs[0] == ite.cs[2] {
        Some(ConditionalStore {
            arr: ite.cs[2].clone(),
            idx: ite.cs[1].cs[1].clone(),
            val: ite.cs[1].cs[2].clone(),
            guard: ite.cs[0].clone(),
            store: ite.cs[1].clone(),
        })
    } else {
        None
    }
}

#[derive(Debug)]
/// Data about a conditional store: term = (ite guard (store arr idx val) arr)
///
/// The store field is (store arr idx val)
struct ConditionalStore {
    arr: Term,
    idx: Term,
    val: Term,
    guard: Term,
    store: Term,
}

/// Graph of the *arrays* in the computation.
///
/// Nodes are *most* of the array-sorted terms (see "subsumed store" for the exception).
///
/// Edges go from dependent arrays to their dependencies and represent stores,
/// ITEs, and conditional stores.
///
/// A conditional store has form T = (ite C (store A I V) A).
///
/// It is regarded as a single edge from T to A, so long as the interior store
/// (store A I V) has no other dependents. In this case, the interior store is
/// called a "subsumed store", and is not part of the array graph itself.
///
/// The "constant-free" graph has constant arrays removed.
///
/// An array term in the graph is non-RAM if is is connected (undirectedly) in
/// the constant-free graph to any node with multiple parents or children in the
/// constant-free graph.
///
#[derive(Debug)]
struct ArrayGraph {
    /// Map from array terms to their children (dependencies)
    children: TermMap<Vec<Term>>,
    /// Set of all array terms.
    array_terms: TermSet,
    /// Set of non-RAM array terms.
    non_ram: TermSet,
}

impl ArrayGraph {
    fn new(c: &Computation) -> Self {
        let term_parents = extras::parents_map(c);
        let mut c_stores = TermMap::default();
        let mut ps = TermMap::default();
        let mut cs = TermMap::default();
        let mut arrs = TermSet::default();
        let mut subsumed = TermSet::default();
        // TODO: This is only extracitng arrays with stores...
        //       need to also get array terms...
        // TODO: I assume we only want arrays here that also have
        //       conditional selects? or indirect selects? not sure.

        // We go parent->children to see conditional stores before their subsumed stores.
        // clippy thinks this is needless, but we need it for the reverse iteration.
        #[allow(clippy::needless_collect)]
        let terms: Vec<_> = c.terms_postorder().collect();
        for t in terms.into_iter().rev() {
            let mut is_c_store = false;
            if let Some(c_store) = parse_cond_store(&t) {
                if term_parents.get(&c_store.store).unwrap().len() == 1 {
                    debug!("cond store: {}", Letified(t.clone()));
                    subsumed.insert(c_store.store.clone());
                    ps.entry(c_store.arr.clone())
                        .or_insert_with(Vec::new)
                        .push(t.clone());
                    cs.entry(t.clone())
                        .or_insert_with(Vec::new)
                        .push(c_store.arr.clone());
                    arrs.insert(t.clone());
                    c_stores.insert(t.clone(), c_store);
                    is_c_store = true;
                }
            }
            if !is_c_store && !subsumed.contains(&t) {
                if let Sort::Array(..) = check(&t) {
                    for c in &t.cs {
                        if let Sort::Array(..) = check(c) {
                            arrs.insert(t.clone());
                            ps.entry(c.clone()).or_insert_with(Vec::new).push(t.clone());
                            cs.entry(t.clone()).or_insert_with(Vec::new).push(c.clone());
                        }
                    }
                }
            }
            if let Op::Array(..) = t.op {
                arrs.insert(t.clone());
            }
        }
        let mut non_ram: TermSet = TermSet::default();
        {
            let mut stack: Vec<Term> = arrs
                .iter()
                .filter(|a| {
                    !a.is_const()
                        && (ps.get(a).map(|ps| ps.len() > 1).unwrap_or(false)
                            || cs.get(a).map(|cs| cs.len() > 1).unwrap_or(false))
                })
                .cloned()
                .collect();
            while let Some(t) = stack.pop() {
                if !t.is_const() && !non_ram.contains(&t) {
                    non_ram.insert(t.clone());
                    for t in ps.get(&t).into_iter().flatten() {
                        stack.push(t.clone());
                    }
                    for t in cs.get(&t).into_iter().flatten() {
                        stack.push(t.clone());
                    }
                }
            }
        }
        Self {
            children: cs,
            array_terms: arrs,
            non_ram,
        }
    }
    fn is_ram(&self, t: &Term) -> bool {
        !t.is_const() && self.array_terms.contains(t) && !self.non_ram.contains(t)
    }
    fn is_ram_read(&self, t: &Term) -> bool {
        match t.op {
            Op::Field(idx) => {
                // recursively check if the field of t is a ram
                if t.cs[0].get().cs.len() > idx {
                    self.is_ram_read(&t.cs[0].get().cs[idx])
                } else {
                    false
                }
            }
            _ => !t.is_const() && self.array_terms.contains(t) && !self.non_ram.contains(t),
        }
    }
}

#[derive(Debug)]
struct Extactor<'a> {
    rams: Vec<Ram>,
    term_ram: TermMap<RamId>,
    read_terms: TermMap<Term>,
    graph: ArrayGraph,
    cache: &'a mut TermMap<u8>,
    const_arrs: usize,
}

type RamId = usize;

impl<'a> Extactor<'a> {
    fn new(c: &Computation, cache: &'a mut TermMap<u8>) -> Self {
        let graph = ArrayGraph::new(c);
        Self {
            rams: Vec::new(),
            term_ram: TermMap::default(),
            read_terms: TermMap::default(),
            graph,
            cache,
            const_arrs: 0,
        }
    }
    // If this term is a constant array, start a new RAM. Otherwise, look this term up.
    fn get_or_start(&mut self, t: &Term) -> RamId {
        match &t.op {
            Op::Const(Value::Array(a)) => {
                let id = self.rams.len();
                self.rams.push(Ram::new(id, a.clone()));
                id
            }
            Op::Array(..) => {
                if let Some(id) = self.term_ram.get(t) {
                    return *id;
                }

                self.const_arrs += 1;
                let id = self.rams.len();
                self.term_ram.insert(t.clone(), id);
                let t_sort = check(t);
                let (key_sort, val_sort, size) = t_sort.as_array();
                let val = Array::default(key_sort.clone(), &val_sort, size);
                self.rams.push(Ram::new(id, val));
                let mut ram = &mut self.rams[id];
                // for an array constructor: add writes (at constant indices)
                for (i, val) in t.cs.iter().enumerate() {
                    ram.new_write(key_sort.nth_elem(i), val.clone(), bool_lit(true));
                }
                id
            }
            Op::Field(idx) => self.get_or_start(&t.cs[0].get().cs[*idx]),
            _ => *self
                .term_ram
                .get(t)
                .unwrap_or_else(|| panic!("No RAM for term {}", extras::Letified(t.clone()))),
        }
    }

    fn rewrite_indices(&mut self) {
        // TODO: try to optimize this?
        let mut rams: Vec<Ram> = self.rams.drain(0..).collect();
        for ram in &mut rams {
            for access in &mut ram.accesses {
                access.idx = self.rewrite_index_term(access.idx.clone());
            }
        }
        self.rams = rams;
    }

    /// Rewrite a single index term recursivly. Uses the cache if we have already
    /// seen this term before
    fn rewrite_index_term(&mut self, t: Term) -> Term {
        if self.read_terms.contains_key(&t) {
            return self.read_terms.get(&t).unwrap().clone();
        }

        // rewrite all children
        let mut rewritten_children = Vec::new();
        for c in &t.get().cs {
            rewritten_children.push(self.rewrite_index_term(c.clone()));
        }
        let res = term(t.get().op.clone(), rewritten_children);
        self.read_terms.insert(t, res.clone());
        res
    }
}

impl<'a> RewritePass for Extactor<'a> {
    fn visit<F: Fn() -> Vec<Term>>(
        &mut self,
        computation: &mut Computation,
        t: &Term,
        rewritten_children: F,
    ) -> Option<Term> {
        // First, we rewrite RAM terms.
        if self.graph.is_ram(t) {
            if matches!(t.op, Op::Array(..)) && !self.term_ram.contains_key(&t) {
                let ram_id = self.get_or_start(&t);
                let ram = &mut self.rams[ram_id];
                self.term_ram.insert(t.clone(), ram_id);
                let new = term(t.op.clone(), rewritten_children());
                None
            } else {
                // Since this is a "RAM" term, it is non-constant and either a c-store or a store.
                assert!(matches!(t.op, Op::Store | Op::Ite), "OOOOOOF");
                assert!(self.graph.children.get(t).is_some(), "No children");
                assert_eq!(
                    1,
                    self.graph.children.get(t).unwrap().len(),
                    "Too many children"
                );
                // Get dependency's RAM
                let child = self.graph.children.get(t).unwrap()[0].clone();
                let ram_id = self.get_or_start(&child);
                let ram = &mut self.rams[ram_id];
                // Build new term, and parse as a c-store
                let new = term(t.op.clone(), rewritten_children());
                let c_store = parse_cond_store(&new).unwrap_or_else(|| {
                    // this is a plain store then, map it to a c-store
                    assert_eq!(Op::Store, new.op);
                    ConditionalStore {
                        arr: new.cs[0].clone(),
                        idx: new.cs[1].clone(),
                        val: new.cs[2].clone(),
                        guard: bool_lit(true),
                        store: bool_lit(false), // dummy; unused.
                    }
                });
                // Add the write to the RAM
                ram.new_write(c_store.idx, c_store.val, c_store.guard);
                let id = ram.id;
                self.term_ram.insert(t.clone(), id);
                None
            }
        } else {
            match &t.op {
                // Rewrite select's whose array is a RAM term
                Op::Select if self.graph.is_ram_read(&t.cs[0]) => {
                    if let Op::Field(_) = t.op {
                        println!("Field op in ram!: {:?}", t);
                    }
                    let ram_id = self.get_or_start(&t.cs[0]);
                    let ram = &mut self.rams[ram_id];
                    let read_value =
                        ram.new_read(t.cs[1].clone(), computation, t.clone(), self.cache);
                    self.read_terms.insert(t.clone(), read_value.clone());
                    Some(read_value)
                }
                _ => None,
            }
        }
    }
}

struct Encoder<'a> {
    rams: Vec<Ram>,
    cache: &'a mut TermMap<u8>,
}

impl<'a> Encoder<'a> {
    fn new(rams: Vec<Ram>, cache: &mut TermMap<u8>) -> Encoder {
        Encoder { rams, cache }
    }

    fn construct_permutation_check(ram1: &Ram, ram2: &Ram, alpha: Term, beta: Term) -> Term {
        assert!(ram1.epoch != 1);
        assert!(ram2.epoch != 1);
        // TODO: support non-field indices?
        //       Just do a cast on permuation check, and have correct type
        //       in sorted check

        // construct a term to check the __ram_srow values are the same as the
        // __ram values
        let orig_ms_hash = multiset_hash(
            ram1.accesses
                .iter()
                .map(|access| universal_hash(vec![access.idx.clone(), access.val.clone()], &beta)),
            &alpha,
        );

        let perm_ms_hash = multiset_hash(
            ram2.accesses
                .iter()
                .map(|access| universal_hash(vec![access.idx.clone(), access.val.clone()], &beta)),
            &alpha,
        );

        term![EQ; orig_ms_hash, perm_ms_hash]
    }

    fn construct_sorted_check(sorted_ram: &Ram, computation: &mut Computation) -> Term {
        // TODO: support non-field indices?
        //       Just do a cast on permuation check, and have correct type
        //       in sorted check
        let idx_field = match &sorted_ram.idx_sort {
            Sort::Field(field) => field,
            _ => panic!("Cannot use RAM on non-field index type!"),
        };

        let mut check_terms = Vec::new();
        for i in 1..sorted_ram.accesses.len() {
            // if idx == idx' then v == v' else idx == idx' + 1
            let check_term = term![
                ITE;
                term![
                    EQ;
                    sorted_ram.accesses[i].idx.clone(),
                    sorted_ram.accesses[i - 1].idx.clone()
                ],
                term![
                    Op::Eq;
                    sorted_ram.accesses[i].val.clone(),
                    sorted_ram.accesses[i - 1].val.clone()
                ],
                term![Op::Eq;
                    sorted_ram.accesses[i].idx.clone(),
                    term![PF_ADD; sorted_ram.accesses[i-1].idx.clone(), pf_lit(idx_field.new_v::<u32>(1))]
                ]
            ];
            computation.new_var(
                &format!("__TEST_SORTED_{}_{}", sorted_ram.id, i),
                Sort::Bool,
                Some(crate::ir::proof::PROVER_ID),
                0, // TODO
                false,
                Some(check_term.clone()),
            );
            check_terms.push(check_term);
        }
        term(AND, check_terms)
    }

    fn encode(&mut self, computation: &mut Computation) {
        if self.rams.len() < 2 {
            return;
        }
        assert_eq!(
            computation.outputs().len(),
            1,
            "Proofs using RAMs must have a single output!"
        );
        assert_eq!(
            check(&computation.outputs()[0]),
            Sort::Bool,
            "Proofs using RAMs must have a boolean output!"
        );

        // fix up writes in rams...
        // we don't actually use them, but makes the circuit simpler
        // so we will just fix up the values here
        for ram in self.rams.iter_mut() {
            ram.accesses
                .sort_by_key(|r| !eval(&r.is_write, &fxhash::FxHashMap::default()).as_bool());
            if ram.accesses.len() >= 2 * ram.size {
                let should_remove = ram.accesses[..2 * ram.size]
                    .iter()
                    .all(|r| eval(&r.is_write, &fxhash::FxHashMap::default()).as_bool());
                let mut i = 0;
                while should_remove && i < ram.size {
                    ram.accesses.remove(0);
                    i += 1;
                }
            }
        }

        // remove rams that are empty
        // TODO: maybe throw a warning here?
        self.rams = self
            .rams
            .drain(0..)
            .filter(|ram| !ram.accesses.is_empty())
            .collect();

        // TODO: actually check that the sorts for ram1 and ram2 are equal...
        // TODO: should this actually be verifier_id?
        // TODO: assumes that idx_sort is a field
        let alpha = computation.new_var(
            &format!("__alpha"),
            self.rams[0].idx_sort.clone(),
            None,
            0, // TODO
            true,
            None,
        );
        let beta = computation.new_var(
            &format!("__beta"),
            self.rams[0].idx_sort.clone(),
            None,
            0, // TODO
            true,
            None,
        );

        let mut checks = vec![];
        checks.push(computation.outputs()[0].clone());
        for ram in self.rams.iter() {
            let sorted_ram = if ram.epoch == 0 {
                let sorted_ram = ram.sorted_by_index(computation, self.cache);
                // TODO: better error handling
                // TODO: is there a cleaner way to get the field type?
                let permutation_check = Encoder::construct_permutation_check(
                    ram,
                    &sorted_ram,
                    alpha.clone(),
                    beta.clone(),
                );
                checks.push(permutation_check);
                sorted_ram
            } else {
                let mut count = 0;
                waksman(ram, computation, self.cache)
            };

            let sorted_check = Encoder::construct_sorted_check(&sorted_ram, computation);

            checks.push(sorted_check);
        }
        computation.outputs[0] = term(AND, checks);
    }
}

/// Find arrays which are RAMs (i.e., accessed with a linear sequences of
/// selects, stores, and conditional stores) and
///   1. Replaces reads from these RAMs with new variables.
///   2. Builds a transcript for each RAM.
///
/// A conditional store must have form (ite C (store A I V) I) to be detected.
///
/// Limitations:
/// * This pass doesn't handle shared stuff very well. If there are two
///   different RAMs with the same init sequence of instructions, this pass will
///   not extract **either**.
pub fn extract(c: &mut Computation, cache: &mut TermMap<u8>) -> Vec<Ram> {
    let mut extractor = Extactor::new(c, cache);
    extractor.traverse(c);
    extractor.rewrite_indices();
    //for ram in &extractor.rams {
    //    println!("------------");
    //    println!("ram id: {:?}, len: {:?}", ram.id, ram.accesses.len());
    //    println!(
    //        "ram val: {:?}",
    //        c.precomputes.outputs().get(&format!("__ram_{}_0", ram.id))
    //    );
    //}
    extractor.rams
}

/// Encodes the given RAMs into the computation, by ensuring there exist
/// a valid ordering of the RAM accesses
///
/// NOTE: This is currently broken for any ram that:
///       1. doesn't do a single write, then only reads
///       2. doesn't access every single element in the ram
pub fn encode(c: &mut Computation, rams: Vec<Ram>, cache: &mut TermMap<u8>) {
    let mut encoder = Encoder::new(rams, cache);
    encoder.encode(c);
}
