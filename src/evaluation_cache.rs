
use crate::term::{Term, TermData};
use fxhash::FxBuildHasher;
use lru::LruCache;
use std::collections::{HashMap, HashSet};
use std::num::NonZeroUsize;

pub struct EvaluationCache {
    cache: LruCache<(Term, u64), Term, FxBuildHasher>,
    term_set: HashSet<Term>,
    free_bindings_cache: HashMap<(Term, usize), HashSet<usize>, FxBuildHasher>,
}

impl EvaluationCache {
    pub fn new() -> Self {
        EvaluationCache {
            cache: LruCache::with_hasher(
                NonZeroUsize::new(100_000_000).unwrap(),
                FxBuildHasher::default(),
            ),
            term_set: HashSet::default(),
            free_bindings_cache: HashMap::default(),
        }
    }

    // Add other methods here...
}
      