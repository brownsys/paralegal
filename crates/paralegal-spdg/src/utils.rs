use std::fmt;

pub fn write_sep<
    E,
    I: IntoIterator<Item = E>,
    F: FnMut(E, &mut fmt::Formatter<'_>) -> fmt::Result,
>(
    fmt: &mut fmt::Formatter<'_>,
    sep: &str,
    it: I,
    mut f: F,
) -> fmt::Result {
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
