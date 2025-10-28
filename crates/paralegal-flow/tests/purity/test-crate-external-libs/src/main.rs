use chrono::naive::NaiveDateTime;

#[paralegal::analyze]
pub fn date_format(v: NaiveDateTime) -> String {
    v.format("%Y-%m-%d %H:%M:%S").to_string()
}
