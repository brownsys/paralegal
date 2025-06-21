use std::{
    cell::RefCell,
    collections::{hash_map::Entry, HashMap},
    hash::Hash,
    pin::Pin,
};

/// Pretty much copies the cache from rustc_utils, but adds a second layer so we
/// can chech for recursion on only part of the key
pub struct TwoLevelCache<K1, K2, Out>(RefCell<TwoLevelCacheInner<K1, K2, Out>>);
#[doc(hidden)]
pub type TwoLevelCacheInner<K1, K2, Out> = HashMap<K1, TwolevelCacheValue<K2, Out>>;
#[doc(hidden)]
pub type TwolevelCacheValue<K2, Out> = (bool, HashMap<K2, Pin<Box<Out>>>);

impl<K1: Eq + Hash + Clone, K2: Eq + Hash + Clone, Out> TwoLevelCache<K1, K2, Out> {
    /// Size of the cache
    pub fn len(&self) -> usize {
        self.0.borrow().values().map(|(_, m)| m.len()).sum()
    }
    /// Returns the cached value for the given key, or runs `compute` if
    /// the value is not in cache.
    ///
    /// # Panics
    ///
    /// If this is a recursive invocation for this key.
    pub fn get(&self, key: (K1, K2), compute: impl FnOnce((K1, K2)) -> Out) -> &Out {
        self.get_maybe_recursive(key, compute)
            .unwrap_or_else(recursion_panic)
    }

    #[doc(hidden)]
    pub fn borrow(&self) -> std::cell::Ref<'_, TwoLevelCacheInner<K1, K2, Out>> {
        self.0.borrow()
    }
    /// Returns the cached value for the given key, or runs `compute` if
    /// the value is not in cache.
    ///
    /// Returns `None` if this is a recursive invocation of `get` for key `key`.
    pub fn get_maybe_recursive(
        &self,
        key: (K1, K2),
        compute: impl FnOnce((K1, K2)) -> Out,
    ) -> Option<&Out> {
        match self.try_retrieve(key, |in_| Some(compute(in_))) {
            Retrieval::Recursive => None,
            Retrieval::Success(v) => Some(v),
            Retrieval::Uncomputable => unreachable!(),
        }
    }

    /// Try to retrieve a value from the cache with a potentially fallible or
    /// recursive computation.
    pub fn try_retrieve<'a>(
        &'a self,
        key: (K1, K2),
        compute: impl FnOnce((K1, K2)) -> Option<Out>,
    ) -> Retrieval<&'a Out> {
        let k1 = key.0;
        let k2 = key.1;

        let is_present = {
            let mut b = self.0.borrow_mut();
            match b.entry(k1.clone()) {
                Entry::Vacant(v) => {
                    v.insert((true, HashMap::new()));
                    false
                }
                Entry::Occupied(o) if o.get().0 => {
                    return Retrieval::Recursive;
                }
                Entry::Occupied(mut o) if !o.get().1.contains_key(&k2) => {
                    o.get_mut().0 = true;
                    false
                }
                _ => true,
            }
        };

        if !is_present {
            let result = compute((k1.clone(), k2.clone()));
            let mut borrow = self.0.borrow_mut();
            let (constructing, entry) = &mut borrow.get_mut(&k1).unwrap();
            if let Some(out) = result {
                entry.insert(k2.clone(), Box::pin(out));
            } else {
                entry.remove(&k2);
            }
            *constructing = false;
        }

        let cache = self.0.borrow();
        let entry = cache.get(&k1).unwrap();
        match entry.1.get(&k2) {
            None => Retrieval::Uncomputable,
            Some(entry) => Retrieval::Success(
                // SAFETY: because the entry is pinned, it cannot move and this pointer will
                // only be invalidated if Cache is dropped. The returned reference has a lifetime
                // equal to Cache, so Cache cannot be dropped before this reference goes out of scope.
                unsafe { std::mem::transmute::<&'_ Out, &'a Out>(&**entry) },
            ),
        }
    }

    pub fn is_in_cache(&self, key: &(K1, K2)) -> bool {
        let k1 = &key.0;
        let k2 = &key.1;
        self.0
            .borrow()
            .get(k1)
            .is_some_and(|v| v.1.contains_key(k2))
    }

    #[allow(dead_code)]
    /// Safety: Invalidates all references
    pub(crate) unsafe fn clear(&self) {
        self.0.borrow_mut().clear()
    }
}

pub enum Retrieval<T> {
    Success(T),
    Recursive,
    Uncomputable,
}

impl<T> Retrieval<T> {
    pub fn as_success(self) -> Option<T> {
        match self {
            Retrieval::Success(v) => Some(v),
            _ => None,
        }
    }
}

fn recursion_panic<A>() -> A {
    panic!("Recursion detected! The computation of a value tried to retrieve the same from the cache. Using `get_maybe_recursive` to handle this case gracefully.")
}

impl<K1, K2, Out> Default for TwoLevelCache<K1, K2, Out> {
    fn default() -> Self {
        Self(RefCell::new(HashMap::default()))
    }
}
