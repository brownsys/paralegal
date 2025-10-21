use chrono::naive::NaiveDateTime;

#[pear::scrutinizer_pure]
pub fn date_format(v: NaiveDateTime) -> String {
    v.format("%Y-%m-%d %H:%M:%S").to_string()
}
