#![feature(register_tool)]
#![register_tool(dfpp)]

use std::collections::HashMap;

#[dfpp::label(noinline)]
fn some_bool() -> bool {
    false
}

#[dfpp::analyze]
pub async fn survive_on_broken(
    metrics: Metrics,
)  {

    let mut tags = Tags::from_head();
    {
        tags.add_extra("audience_key", "");
        // Add/modify the existing request tags.
        // tags.clone().commit(&mut request.extensions_mut());
    }

    match get_result() {
        Ok(response) => {

        }
        Err(e) => {
            if e.kind == 0 {
                tags.extend(e.tags.clone());
                tags.add_tag("level", "warning");
                metrics.incr_with_tags("tiles.invalid", Some(&tags));

                return;
            }

            match e.kind {
                0 => tags.add_tag("reason", "timeout"),
                1 => tags.add_tag("reason", "connect"),
                _ => (),
            }
            if some_bool() {
                tags.add_tag("fallback", "true");
            }
            metrics.incr_with_tags("tiles.get.error", Some(&tags));
        }
    }
}
/// The metric wrapper
#[derive(Debug, Clone)]
pub struct Metrics {
    client: Option<Client>,
    tags: Option<Tags>,
    //timer: Option<MetricTimer>,
}

#[derive(Clone, Debug)]
struct Client;

impl Client {
    #[dfpp::label(noinline)]
    fn incr_with_tags(&self, label: &str) -> Builder {
        Builder
    }
}

struct Builder;

impl Builder { 
    #[dfpp::label(noinline)]
    fn with_tag(&mut self, key: &str, value: &str) -> Builder {
        Builder
    }

    #[dfpp::label(noinline)]
    fn try_send(&self) -> Result<String, String> {
        unimplemented!()
    }
}

impl Metrics {
    pub fn incr_with_tags(&self, label: &str, tags: Option<&Tags>) {
        if let Some(client) = self.client.as_ref() {
            let mut tagged = client.incr_with_tags(label);
            let mut mtags = self.tags.clone().unwrap_or_default();
            if let Some(tags) = tags {
                mtags.extend(tags.clone());
            }
            for key in mtags.tags.keys().clone() {
                if let Some(val) = mtags.tags.get(key) {
                    tagged = tagged.with_tag(key, val.as_ref());
                }
            }
            for (key, value) in mtags.extra.iter() {
                tagged = tagged.with_tag(key, value);
            }
            // Include any "hard coded" tags.
            // incr = incr.with_tag("version", env!("CARGO_PKG_VERSION"));
            match tagged.try_send() {
                Err(e) => {
                    // eat the metric, but log the error
                }
                Ok(v) => (),
            }
        }
    }
}

#[derive(Clone, Debug, Default)]
pub struct Tags {
    // All tags (both metric and sentry)
    pub tags: HashMap<String, String>,
    // Sentry only "extra" data.
    pub extra: HashMap<String, String>,
    // metric only supplemental tags.
    pub metric: HashMap<String, String>,
}

struct Err {
    tags: Tags,
    kind: usize,
}

#[dfpp::label(noinline)]
fn get_result() -> Result<(), Err> {
    unimplemented!()
}

impl Tags {
    fn from_head() -> Self {
        // Return an Option<> type because the later consumers (HandlerErrors) presume that
        // tags are optional and wrapped by an Option<> type.
        let mut tags = HashMap::new();
        let mut extra = HashMap::new();
        mark_sensitive(&mut extra);
        // if let Some(ua) = req_head.headers().get(USER_AGENT) {
        //     if let Ok(uas) = ua.to_str() {
        //         if let Ok(device_info) = get_device_info(uas) {
        //             tags.insert("ua.os.family".to_owned(), device_info.os_family.to_string());
        //             tags.insert(
        //                 "ua.form_factor".to_owned(),
        //                 device_info.form_factor.to_string(),
        //             );
        //         }
        //         extra.insert("ua".to_owned(), uas.to_string());
        //     }
        // }
        // if let Some(tracer) = settings.trace_header.clone() {
        //     if let Some(header) = req_head.headers().get(tracer) {
        //         if let Ok(val) = header.to_str() {
        //             if !val.is_empty() {
        //                 extra.insert("header.trace".to_owned(), val.to_owned());
        //             }
        //         }
        //     }
        // }
        // tags.insert("uri.method".to_owned(), req_head.method.to_string());
        // // `uri.path` causes too much cardinality for influx but keep it in
        // // extra for sentry
        // extra.insert("uri.path".to_owned(), req_head.uri.to_string());
        Tags {
            tags,
            extra,
            metric: HashMap::new(),
        }
    }

    pub fn extend(&mut self, tags: Self) {
        self.tags.extend(tags.tags);
        self.extra.extend(tags.extra);
        self.metric.extend(tags.metric);
    }
    pub fn add_tag(&mut self, key: &str, value: &str) {
        if !value.is_empty() {
            self.tags.insert(key.to_owned(), value.to_owned());
        }
    }
    pub fn add_extra(&mut self, key: &str, value: &str) {
        if !value.is_empty() {
            self.extra.insert(key.to_owned(), value.to_owned());
        }
    }

}

#[dfpp::label(sensitive, arguments = [0])]
fn mark_sensitive<T>(_: &mut T) {}

fn main() {}