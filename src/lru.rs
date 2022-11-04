use hashconsing::{hash_coll::hashers::p_hash, HConsed, HashConsed};
use std::{
    collections::{HashMap, HashSet},
    hash::{BuildHasher, Hash, Hasher},
    ops::{Deref, DerefMut},
};

//use lru_cache::LruCache;

pub struct HConLruCache<T, V>
where
    T: HashConsed,
    T::Inner: Hash + Eq,
{
    map: LruCache<HConsed<T::Inner>, V, p_hash::Builder>,
}

impl<T: HashConsed, V> HConLruCache<T, V>
where
    T::Inner: Hash + Eq,
{
    pub fn new(n: usize) -> Self {
        HConLruCache {
            map: LruCache::with_hasher(n, p_hash::Builder::new()),
        }
    }
}

impl<T: HashConsed, V> Deref for HConLruCache<T, V>
where
    T::Inner: Hash + Eq,
{
    type Target = LruCache<HConsed<T::Inner>, V, p_hash::Builder>;
    fn deref(&self) -> &Self::Target {
        &self.map
    }
}

impl<T: HashConsed, V> DerefMut for HConLruCache<T, V>
where
    T::Inner: Hash + Eq,
{
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.map
    }
}
