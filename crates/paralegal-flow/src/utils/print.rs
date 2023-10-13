pub use paralegal_spdg::utils::write_sep;
use std::fmt::{Debug, Display, Formatter, Result};

pub use paralegal_spdg::utils::Print;

#[derive(Hash, Eq, Ord, PartialEq, PartialOrd, Clone, Copy)]
pub struct DisplayViaDebug<T>(pub T);

impl<T: Debug> Display for DisplayViaDebug<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        <T as Debug>::fmt(&self.0, f)
    }
}

impl<T: Debug> Debug for DisplayViaDebug<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        self.0.fmt(f)
    }
}

impl<T> std::ops::Deref for DisplayViaDebug<T> {
    type Target = T;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<T> From<T> for DisplayViaDebug<T> {
    fn from(t: T) -> Self {
        Self(t)
    }
}
