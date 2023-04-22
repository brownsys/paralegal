
use std::fmt::{Debug, Display, Formatter, Result};

pub struct Print<F: Fn(&mut Formatter<'_>) -> Result>(pub F);

impl<F: Fn(&mut Formatter<'_>) -> Result> Display for Print<F> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        (&self.0)(f)
    }
}
pub fn write_sep<
    E,
    I: IntoIterator<Item = E>,
    F: FnMut(E, &mut Formatter<'_>) -> Result,
>(
    fmt: &mut Formatter<'_>,
    sep: &str,
    it: I,
    mut f: F,
) -> Result {
    let mut first = true;
    for e in it {
        if first {
            first = false;
        } else {
            fmt.write_str(sep)?;
        }
        f(e, fmt)?;
    }
    Ok(())
}


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

