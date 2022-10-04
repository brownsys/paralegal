pub fn print_flowistry_matrix<W: std::io::Write>(mut out: W, matrix: &crate::sah::Matrix) -> std::io::Result<()> {
    fn shortened(mut s: String, i: usize) -> String {
        s.truncate(i);
        s
    }
    use flowistry::indexed::IndexedDomain;
    let domain = &matrix.col_domain;
    let header_col_width = 10;
    let cell_width = 8;
    write!(out, "{:header_col_width$} |", ' ')?;

    for (_, v) in domain.as_vec().iter_enumerated() {
        write!(out, "{:^cell_width$}", format!("{:?}", v))?
    }
    writeln!(out, "")?;

    for (v, r) in matrix.rows() {
        write!(out, "{:header_col_width$} |", shortened(format!("{:?}", v), header_col_width))?;
        for (i, _) in domain.as_vec().iter_enumerated() {
            write!(out, "{:^cell_width$}", if r.contains(i) {
                "×"
            } else {
                " "
            })?
        }
        writeln!(out, "")?
    }
    Ok(())
}