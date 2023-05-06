#[derive(
    Clone, Eq, PartialEq, PartialOrd, Ord, Hash, Copy, serde::Serialize, serde::Deserialize,
)]
pub struct TinyBitSet(u16);

impl Default for TinyBitSet {
    fn default() -> Self {
        Self::new_empty()
    }
}

impl std::fmt::Debug for TinyBitSet {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.into_iter_set_in_domain().collect::<Vec<_>>().fmt(f)
    }
}

impl TinyBitSet {
    /// Creates a new, empty bitset.
    pub fn new_empty() -> Self {
        Self(0)
    }

    /// Sets the `index`th bit.
    pub fn set(&mut self, index: u32) {
        self.0 |= 1_u16.checked_shl(index).unwrap_or(0);
    }

    /// Unsets the `index`th bit.
    pub fn clear(&mut self, index: u32) {
        self.0 &= !1_u16.checked_shl(index).unwrap_or(0);
    }

    /// Sets the `i`th to `j`th bits.
    pub fn set_range(&mut self, range: std::ops::Range<u32>) {
        use std::ops::Not;
        let bits = u16::MAX
            .checked_shl(range.end - range.start)
            .unwrap_or(0)
            .not()
            .checked_shl(range.start)
            .unwrap_or(0);
        self.0 |= bits;
    }

    /// Is the set empty?
    pub fn is_empty(self) -> bool {
        self.0 == 0
    }

    /// Returns the domain size of the bitset.
    pub fn within_domain(self, index: u32) -> bool {
        index < 16
    }

    pub fn count(self) -> u32 {
        self.0.count_ones()
    }

    /// Returns if the `index`th bit is set.
    pub fn contains(self, index: u32) -> Option<bool> {
        self.within_domain(index)
            .then(|| ((self.0.checked_shr(index).unwrap_or(1)) & 1) == 1)
    }

    pub fn is_set(self, index: u32) -> bool {
        self.contains(index) == Some(true)
    }

    pub fn into_iter_set_in_domain(self) -> impl Iterator<Item = u32> {
        (0..16).filter(move |i| self.contains(*i).unwrap_or(false))
    }
}

impl FromIterator<u32> for TinyBitSet {
    fn from_iter<T: IntoIterator<Item = u32>>(iter: T) -> Self {
        let mut slf = Self::new_empty();
        for item in iter {
            slf.set(item)
        }
        slf
    }
}

impl std::ops::BitOrAssign for TinyBitSet {
    fn bitor_assign(&mut self, rhs: Self) {
        self.0.bitor_assign(rhs.0)
    }
}

impl std::ops::BitAndAssign for TinyBitSet {
    fn bitand_assign(&mut self, rhs: Self) {
        self.0.bitand_assign(rhs.0)
    }
}

impl std::ops::BitAnd for TinyBitSet {
    type Output = Self;
    fn bitand(self, rhs: Self) -> Self::Output {
        TinyBitSet(self.0.bitand(rhs.0))
    }
}

impl std::ops::BitOr for TinyBitSet {
    type Output = Self;
    fn bitor(self, rhs: Self) -> Self::Output {
        TinyBitSet(self.0.bitor(rhs.0))
    }
}

impl std::ops::BitXor for TinyBitSet {
    type Output = Self;
    fn bitxor(self, rhs: Self) -> Self::Output {
        Self(self.0.bitxor(rhs.0))
    }
}

impl std::ops::BitXorAssign for TinyBitSet {
    fn bitxor_assign(&mut self, rhs: Self) {
        self.0.bitxor_assign(rhs.0)
    }
}

pub mod pretty {
    use super::TinyBitSet;

    pub fn deserialize<'de, D>(deserializer: D) -> Result<TinyBitSet, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        <Vec<u32> as serde::Deserialize<'de>>::deserialize(deserializer)
            .map(|v| v.into_iter().collect())
    }

    pub fn serialize<S>(set: &TinyBitSet, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        serde::Serialize::serialize(
            &set.into_iter_set_in_domain().collect::<Vec<_>>(),
            serializer,
        )
    }
}
