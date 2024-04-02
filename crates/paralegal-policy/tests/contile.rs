use std::sync::Arc;

use anyhow::{Ok, Result};
use helpers::Test;
use paralegal_policy::{Context, Diagnostics, EdgeSelection, NodeQueries};
use paralegal_spdg::Identifier;

mod helpers;

const CODE: &str = stringify!(
    use actix_web::{HttpResponse, HttpRequest, web, http::header::HeaderMap};
    use std::time::{Duration, Instant};
    use std::collections::HashMap;
    use actix_web::http::header::USER_AGENT;
    use actix_web::dev::RequestHead;
    use cadence::{StatsdClient};
    use std::sync::Arc;

    #[derive(Default, Clone, Debug)]
    pub struct AdmFilter {
        /// Filter settings by Advertiser name
        pub advertiser_filters: AdmAdvertiserSettings,
        // /// Ignored (not included but also not reported to Sentry) Advertiser names
        // pub ignore_list: HashSet<String>,
        // /// Temporary list of advertisers with legacy images built into firefox
        // /// for pre 91 tile support.
        // pub legacy_list: HashSet<String>,
        // pub all_include_regions: HashSet<String>,
        // pub source: Option<String>,
        // pub source_url: Option<url::Url>,
        // pub last_updated: Option<chrono::DateTime<chrono::Utc>>,
        // pub refresh_rate: Duration,
        // pub defaults: AdmDefaults,
        // pub excluded_countries_200: bool,
    }
    /// The payload provided by ADM
    #[derive(Debug)]
    pub struct AdmTileResponse {
        pub tiles: Vec<AdmTile>,
    }

    pub struct AdmTile {}

    pub struct AdvertiserUrlFilter {}

impl Tile {
    pub fn from_adm_tile(tile: AdmTile) -> Self {
        Self {}
    }
}

    #[derive(Debug, Default, Clone)]
    pub struct AdmAdvertiserSettings {
        pub adm_advertisers: HashMap<String, HashMap<String, Vec<AdvertiserUrlFilter>>>,
    }
    pub type HandlerResult<T> = Result<T, HandlerError>;
    struct HandlerError {
        kind: HandlerErrorKind
    }

    impl HandlerError {
        pun fn kind() -> &HandlerErrorKind {
            &self.kind
        }
    }

    pub enum HandlerErrorKind {
        Reqwest(reqwest::Error),
        UnexpectedAdvertiser()
    }

    impl From<HandlerErrorKind> for HandlerError {
        fn from(kind: HandlerErrorKind) -> HandlerError {
            HandlerError { kind }
        }
    }

    #[derive(Debug)]
    pub struct TileResponse {
        pub tiles: Vec<Tile>,
    }

    #[paralegal::marker(sensitive, arguments = [0])]
    fn mark_sensitive<T>(t: &mut T){}
    #[derive(Debug, Clone)]
    pub struct MetricTimer {
        pub label: String,
        pub start: Instant,
        pub tags: Tags,
    }

    #[derive(Clone, Debug)]
    pub struct Tile {
        // pub id: u64,
        // pub name: String,
        // pub url: String,
        // pub click_url: String,
        // // The UA only expects image_url and the image's height/width specified as
        // // `image_size`. The height and width should be equal.
        // pub image_url: String,
        // pub image_size: Option<u32>,
        // pub impression_url: String,
    }

    pub struct ServerState {
        image_store: Option<String>,
        settings: Settings,
    }
    #[paralegal::marker(noinline)]
    pub fn sentry_report(err: &HandlerError, tags: &Tags) {
        unreachable!()
    }

    impl AdmFilter {
        // src/adm/filter.rs
        pub fn filter_and_process(
            &self,
            mut tile: AdmTile,
            //location: &Location,
            //device_info: &DeviceInfo,
            tags: &mut Tags,
            metrics: &Metrics,
        ) -> HandlerResult<Option<Tile>> {
            // Use strict matching for now, eventually, we may want to use backwards expanding domain
            // searches, (.e.g "xyz.example.com" would match "example.com")
            match self
                .advertiser_filters
                .adm_advertisers
                .get(&tile.name.to_lowercase())
            {
                Some(filter) => {
                    // Apply any additional tile filtering here.
                    // if filter.get(&location.country()).is_none() {
                    //     trace!(
                    //         "Rejecting tile: {:?} region {:?} not included",
                    //         &tile.name,
                    //         location.country()
                    //     );
                    //     metrics.incr_with_tags("filter.adm.err.invalid_location", Some(tags));
                    //     return Ok(None);
                    // }
                    // match to the version that we switched over from built in image management
                    // to CDN image fetch.

                    // if device_info.legacy_only()
                    //     && !self.legacy_list.contains(&tile.name.to_lowercase())
                    // {
                    //     trace!("Rejecting tile: Not a legacy advertiser {:?}", &tile.name);
                    //     metrics.incr_with_tags("filter.adm.err.non_legacy", Some(tags));
                    //     return Ok(None);
                    // }

                    // let adv_filter = filter.get(&location.country()).unwrap();
                    // if let Err(e) = self.check_advertiser(adv_filter, &mut tile, tags) {
                    //     trace!("Rejecting tile: bad adv");
                    //     metrics.incr_with_tags("filter.adm.err.invalid_advertiser", Some(tags));
                    //     self.report(&e, tags);
                    //     return Ok(None);
                    // }
                    if let Err(e) = self.check_click(&self.defaults, &mut tile, tags) {
                        // trace!("Rejecting tile: bad click");
                        metrics.incr_with_tags("filter.adm.err.invalid_click", Some(tags));
                        self.report(&e, tags);
                        return Ok(None);
                    }
                    // if let Err(e) = self.check_impression(&self.defaults, &mut tile, tags) {
                    //     trace!("Rejecting tile: bad imp");
                    //     metrics.incr_with_tags("filter.adm.err.invalid_impression", Some(tags));
                    //     self.report(&e, tags);
                    //     return Ok(None);
                    // }
                    // if let Err(e) = self.check_image_hosts(&self.defaults, &mut tile, tags) {
                    //     trace!("Rejecting tile: bad image");
                    //     metrics.incr_with_tags("filter.adm.err.invalid_image_host", Some(tags));
                    //     self.report(&e, tags);
                    //     return Ok(None);
                    // }
                    // if let Err(e) = tile.image_url.parse::<Uri>() {
                    //     trace!("Rejecting tile: bad image: {:?}", e);
                    //     metrics.incr_with_tags("filter.adm.err.invalid_image", Some(tags));
                    //     self.report(
                    //         &HandlerErrorKind::InvalidHost("Image", tile.image_url).into(),
                    //         tags,
                    //     );
                    //     return Ok(None);
                    // }
                    // trace!("allowing tile {:?}", &tile.name);
                    Ok(Some(Tile::from_adm_tile(tile)))
                }
                None => {
                    if !self.ignore_list.contains(&tile.name.to_lowercase()) {
                        metrics.incr_with_tags("filter.adm.err.unexpected_advertiser", Some(tags));
                        self.report(
                            &HandlerErrorKind::UnexpectedAdvertiser(tile.name).into(),
                            tags,
                        );
                    }
                    Ok(None)
                }
            }
        }
    }
        // src/adm/tiles.rs
        pub async fn adm_get_tiles(
            state: &ServerState,
            // location: &Location,
            // device_info: DeviceInfo,
            tags: &mut Tags,
            metrics: &Metrics,
            headers: Option<&HeaderMap>,
        ) -> HandlerResult<TileResponse> {
            let settings = &state.settings;
            let image_store = &state.img_store;
            // let pse = AdmPse::appropriate_from_settings(&device_info, settings);
            // let country_code = location
            //     .country
            //     .as_deref()
            //     .unwrap_or_else(|| settings.fallback_country.as_ref());
            // let adm_url = Url::parse_with_params(
            //     &pse.endpoint,
            //     &[
            //         ("partner", pse.partner_id.as_str()),
            //         ("sub1", pse.sub1.as_str()),
            //         ("sub2", "newtab"),
            //         ("country-code", country_code),
            //         ("region-code", &location.region()),
            //         (
            //             "dma-code",
            //             &filtered_dma(&state.excluded_dmas, &location.dma()),
            //         ),
            //         ("form-factor", &device_info.form_factor.to_string()),
            //         ("os-family", &device_info.os_family.to_string()),
            //         ("v", "1.0"),
            //         ("out", "json"), // not technically needed, but added for paranoid reasons.
            //         // XXX: some value for results seems required, it defaults to 0
            //         // when omitted (despite AdM claiming it would default to 1)
            //         ("results", &settings.adm_query_tile_count.to_string()),
            //     ],
            // )
            // .map_err(|e| HandlerError::internal(&e.to_string()))?;
            // let adm_url = adm_url.as_str();
            let adm_url = "";

            // // To reduce cardinality, only add this tag when fetching data from
            // // the partner. (This tag is only for metrics.)
            // tags.add_metric(
            //     "srv.hostname",
            //     &gethostname::gethostname()
            //         .into_string()
            //         .unwrap_or_else(|_| "Unknown".to_owned()),
            // );
            // if device_info.is_mobile() {
            //     tags.add_tag("endpoint", "mobile");
            // }
            // tags.add_extra("adm_url", adm_url);

            // // Add `country_code` for ad fill instrumentation.
            // tags.add_tag("geo.country_code", country_code);

            metrics.incr_with_tags("tiles.adm.request", Some(tags));
            let response: AdmTileResponse = match state.settings.test_mode {
                // crate::settings::TestModes::TestFakeResponse => {
                //     let default = HeaderValue::from_str("DEFAULT").unwrap();
                //     let test_response = headers
                //         .unwrap_or(&HeaderMap::new())
                //         .get("fake-response")
                //         .unwrap_or(&default)
                //         .to_str()
                //         .unwrap()
                //         .to_owned();
                //     trace!("Getting fake response: {:?}", &test_response);
                //     AdmTileResponse::fake_response(&state.settings, test_response)?
                // }
                // crate::settings::TestModes::TestTimeout => {
                //     trace!("### Timeout!");
                //     return Err(HandlerErrorKind::AdmLoadError().into());
                // }
                _ => {
                    state
                        .reqwest_client
                        .get(adm_url)
                        .sink()
                        .timeout(Duration::from_secs(settings.adm_timeout))
                        .send()
                        .await
                        .map_err(|e| {
                            // If we're just starting up, we're probably swamping the partner servers as
                            // we fill the queue. Instead of returning a normal 500 error, let's
                            // return something softer to keep our SRE's blood pressure lower.
                            //
                            // We still want to track this as a server error later.
                            //
                            // TODO: Remove this after the shared cache is implemented.
                            let err: HandlerError = if e.is_timeout()
                                && Instant::now()
                                    .checked_duration_since(state.start_up)
                                    .unwrap_or_else(|| Duration::from_secs(0))
                                    <= Duration::from_secs(state.settings.adm_timeout)
                            {
                                HandlerErrorKind::AdmLoadError().into()
                            } else {
                                HandlerErrorKind::AdmServerError().into()
                            };
                            // ADM servers are down, or improperly configured
                            // be sure to write the error to the provided mut tags.
                            tags.add_extra("error", &e.to_string());
                            err
                        })?
                        .error_for_status()?
                        .json()
                        .await
                        .map_err(|e| {
                            // ADM servers are not returning correct information

                            let err: HandlerError = HandlerErrorKind::BadAdmResponse(format!(
                                "ADM provided invalid response: {:?}",
                                e
                            ))
                            .into();
                            tags.add_extra("error", &e.to_string());
                            err
                        })?
                }
            };
            // if response.tiles.is_empty() {
            //     warn!("adm::get_tiles empty response {}", adm_url);
            //     metrics.incr_with_tags("filter.adm.empty_response", Some(tags));
            // }

            let mut filtered: Vec<Tile> = Vec::new();
            // let iter = response.tiles.into_iter();
            // let filter = state.partner_filter.read().await;
            // for tile in iter {
            //     if let Some(tile) =
            //         filter.filter_and_process(tile, location, &device_info, tags, metrics)?
            //     {
            //         filtered.push(tile);
            //     }
            //     if filtered.len() == settings.adm_max_tiles as usize {
            //         break;
            //     }
            // }

            let mut tiles: Vec<Tile> = Vec::new();
            for mut tile in filtered {
                if let Some(storage) = image_store {
                    // we should have already proven the image_url in `filter_and_process`
                    // we need to validate the image, store the image for eventual CDN retrieval,
                    // and get the metrics of the image.
                    match storage.store(&tile.image_url.parse().unwrap()).await {
                        Ok(result) => {
                            tile.image_url = result.url.to_string();
                            // Since height should equal width, using either value here works.
                            tile.image_size = Some(result.image_metrics.width);
                        }
                        Err(e) => {
                            // quietly report the error, and drop the tile.
                            sentry_report(&e, tags);
                            continue;
                        }
                    }
                }
                tiles.push(tile);
            }

            // if tiles.is_empty() {
            //     warn!("adm::get_tiles no valid tiles {}", adm_url);
            //     metrics.incr_with_tags("filter.adm.all_filtered", Some(tags));
            // }

            Ok(TileResponse { tiles })
        }

    /// The metric wrapper
    #[derive(Debug, Clone)]
    pub struct Metrics {
        client: Option<Arc<StatsdClient>>,
        tags: Option<Tags>,
        timer: Option<MetricTimer>,
    }

    impl Metrics {
        // src/metrics.rs
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
                #[cfg(feature = "leak")]
                for (key, value) in mtags.extra.iter() {
                    tagged = tagged.with_tag(key, value);
                }
                // Include any "hard coded" tags.
                // incr = incr.with_tag("version", env!("CARGO_PKG_VERSION"));
                match tagged.try_send() {
                    Err(e) => {
                        // eat the metric, but log the error
                        //warn!("⚠️ Metric {} error: {:?} ", label, e; mtags);
                    }
                    Ok(v) =>  () //trace!("☑️ {:?}", v.as_metric_str()),
                }
            }
        }
    }
    /// Tags are a set of meta information passed along with sentry errors and metrics.
    ///
    /// Not all tags are distributed out. `tags` are searchable and may cause cardinality issues.
    /// `extra` are not searchable, but may not be sent to [crate::metrics::Metrics].
    #[derive(Clone, Debug, Default)]
    pub struct Tags {
        // All tags (both metric and sentry)
        pub tags: HashMap<String, String>,
        // Sentry only "extra" data.
        pub extra: HashMap<String, String>,
        // metric only supplemental tags.
        pub metric: HashMap<String, String>,
    }

    impl Tags {
    pub fn extend(&mut self, tags: Self) {
        self.tags.extend(tags.tags);
        self.extra.extend(tags.extra);
        self.metric.extend(tags.metric);
    }
    }


    #[derive(Clone, Debug)]
pub struct Tiles {
    //pub content: TilesContent,
    // When this is in need of a refresh (the `Cache-Control` `max-age`)
    // expiry: SystemTime,
    // /// After expiry we'll continue serving the stale version of these Tiles
    // /// until they're successfully refreshed (acting as a fallback during
    // /// upstream service outages). `fallback_expiry` is when we stop serving
    // /// this stale Tiles completely
    // fallback_expiry: SystemTime,
    // /// Return OK instead of NoContent
    // always_ok: bool,
}

impl Tiles {
    #[paralegal::marker(noinline)]
    pub fn new(
        tile_response: TileResponse,
        ttl: Duration,
        fallback_ttl: Duration,
        always_ok: bool,
    ) -> Result<Self, HandlerError> {
        unreachable!()
    }
}

    impl Tags {
        // src/tags.rs
        pub fn from_head(req_head: &RequestHead, settings: &Settings) -> Self {
            // Return an Option<> type because the later consumers (HandlerErrors) presume that
            // tags are optional and wrapped by an Option<> type.
            let mut tags = HashMap::new();
            let mut extra = HashMap::new();
            mark_sensitive(&mut extra);
            if let Some(ua) = req_head.headers().get(USER_AGENT) {
                if let Ok(uas) = ua.to_str() {
                    // if let Ok(device_info) = get_device_info(uas) {
                    //     tags.insert("ua.os.family".to_owned(), device_info.os_family.to_string());
                    //     tags.insert(
                    //         "ua.form_factor".to_owned(),
                    //         device_info.form_factor.to_string(),
                    //     );
                    // }
                    extra.insert("ua".to_owned(), uas.to_string());
                }
            }
            if let Some(tracer) = settings.trace_header.clone() {
                if let Some(header) = req_head.headers().get(tracer) {
                    if let Ok(val) = header.to_str() {
                        if !val.is_empty() {
                            extra.insert("header.trace".to_owned(), val.to_owned());
                        }
                    }
                }
            }
            tags.insert("uri.method".to_owned(), req_head.method.to_string());
            // `uri.path` causes too much cardinality for influx but keep it in
            // extra for sentry
            extra.insert("uri.path".to_owned(), req_head.uri.to_string());
            Tags {
                tags,
                extra,
                metric: HashMap::new(),
            }
        }
    }
    struct AudienceKey {}
    pub struct Settings {
        pub trace_header: Option<String>,
        pub excluded_countries_200: bool,
    }
    pub enum TilesState {
        /// A task is currently populating this entry (via [crate::adm::get_tiles])
        Populating,
        /// Tiles that haven't expired (or been identified as expired) yet
        Fresh { tiles: Tiles },
        /// A task is currently refreshing this expired entry (via
        /// [crate::adm::get_tiles])
        Refreshing { tiles: Tiles },
    }

    // src/web/handlers.rs
    pub async fn get_tiles(
        // location: Location,
        // device_info: DeviceInfo,
        metrics: Metrics,
        state: web::Data<ServerState>,
        request: HttpRequest,
    ) -> HandlerResult<HttpResponse> {
        //trace!("get_tiles");
        metrics.incr("tiles.get");

        // if let Some(response) = maybe_early_respond(&state, &location, &device_info).await {
        //     return Ok(response);
        // }
        let audience_key = AudienceKey {
            // country_code: location.country(),
            // region_code: if location.region() != "" {
            //     Some(location.region())
            // } else {
            //     None
            // },
            // dma_code: location.dma,
            // form_factor: device_info.form_factor,
            // os_family: device_info.os_family,
            // legacy_only: device_info.legacy_only(),
        };

        let settings = &state.settings;
        let mut tags = Tags::from_head(request.head(), settings);
        {
            tags.add_extra("audience_key", &format!("{:#?}", audience_key));
            // Add/modify the existing request tags.
            // tags.clone().commit(&mut request.extensions_mut());
        }

        let mut expired = false;

        if true /*settings.test_mode != crate::settings::TestModes::TestFakeResponse */ {
            // First make a cheap read from the cache
            if let Some(tiles_state) = state.tiles_cache.get(&audience_key) {
                match &*tiles_state {
                    TilesState::Populating => {
                        // Another task is currently populating this entry and will
                        // complete shortly. 304 until then instead of queueing
                        // more redundant requests
                        //trace!("get_tiles: Another task Populating");
                        metrics.incr("tiles_cache.miss.populating");
                        return Ok(HttpResponse::NotModified().finish());
                    }
                    TilesState::Fresh { tiles } => {
                        expired = tiles.expired();
                        if !expired {
                            //trace!("get_tiles: cache hit: {:?}", audience_key);
                            metrics.incr("tiles_cache.hit");
                            return Ok(tiles.to_response(settings.cache_control_header));
                        }
                        // Needs refreshing
                    }
                    TilesState::Refreshing { tiles } => {
                        // Another task is currently refreshing this entry, just
                        // return the stale Tiles until it's completed
                        // trace!(
                        //     "get_tiles: cache hit (expired, Refreshing): {:?}",
                        //     audience_key
                        // );
                        metrics.incr("tiles_cache.hit.refreshing");
                        // expired() and maybe fallback_expired()
                        return Ok(fallback_response(settings, tiles));
                    }
                }
            }
        }

        // Alter the cache separately from the read above: writes are more
        // expensive and these alterations occur infrequently

        // Prepare to write: temporarily set the cache entry to
        // Refreshing/Populating until we've completed our write, notifying other
        // requests in flight during this time to return stale data/204 No Content
        // instead of making duplicate/redundant writes. The handle will reset the
        // temporary state if no write occurs (due to errors/panics)
        let handle = state.tiles_cache.prepare_write(&audience_key, expired);

        let result = adm_get_tiles(
            &state,
            // &location,
            // device_info,
            &mut tags,
            &metrics,
            // be aggressive about not passing headers unless we absolutely need to
            // if settings.test_mode != crate::settings::TestModes::NoTest {
            //     Some(request.head().headers())
            // } else {
                 None
            // },
        )
        .await;

        match result {
            Ok(response) => {
                let tiles = Tiles::new(
                    response,
                    settings.tiles_ttl_with_jitter(),
                    settings.tiles_fallback_ttl_with_jitter(),
                    settings.excluded_countries_200,
                )?;
                // trace!(
                //     "get_tiles: cache miss{}: {:?}",
                //     if expired { " (expired)" } else { "" },
                //     &audience_key
                // );
                metrics.incr("tiles_cache.miss");
                handle.insert(TilesState::Fresh {
                    tiles: tiles.clone(),
                });
                Ok(tiles.to_response(settings.cache_control_header))
            }
            Err(e) => {
                if matches!(e.kind(), HandlerErrorKind::BadAdmResponse(_)) {
                    // Handle a bad response from ADM specially.
                    // Report it to metrics and sentry, but also store an empty record
                    // into the cache so that we don't stampede the ADM servers.
                    // warn!("Bad response from ADM: {:?}", e);
                    // Merge in the error tags, which should already include the
                    // error string as `error`
                    tags.extend(e.tags.clone());
                    // tags.add_tag("level", "warning");
                    metrics.incr_with_tags("tiles.invalid", Some(&tags));
                    // write an empty tile set into the cache for this result.
                    handle.insert(TilesState::Fresh {
                        tiles: Tiles::empty(
                            settings.tiles_ttl_with_jitter(),
                            settings.tiles_fallback_ttl_with_jitter(),
                            settings.excluded_countries_200,
                        ),
                    });
                    // Report the error directly to sentry
                    // l_sentry::report(&e, &tags);
                    //warn!("ADM Server error: {:?}", e);
                    // Return a 204 to the client.
                    return Ok(HttpResponse::NoContent().finish());
                }

                // match e.kind() {
                //     HandlerErrorKind::Reqwest(e) if e.is_timeout() => {
                //         tags.add_tag("reason", "timeout")
                //     }
                //     HandlerErrorKind::Reqwest(e) if e.is_connect() => {
                //         tags.add_tag("reason", "connect")
                //     }
                //     _ => (),
                // }
                if handle.fallback_tiles.is_some() {
                    tags.add_tag("fallback", "true");
                }
                metrics.incr_with_tags("tiles.get.error", Some(&tags));

                // A general error occurred, try rendering fallback Tiles
                if let Some(tiles) = handle.fallback_tiles {
                    return Ok(fallback_response(settings, &tiles));
                }
                Err(e)
            }
        }
    }
    impl Settings {
        #[paralegal::marker(noinline)]
        pub fn tiles_ttl_with_jitter(&self) -> Duration {
            unreachable!()
        }

        #[paralegal::marker(noinline)]
        pub fn tiles_fallback_ttl_with_jitter(&self) -> Duration {
            unreachable!()
        }
    }
    #[paralegal::marker(noinline)]
fn fallback_response(settings: &Settings, tiles: &Tiles) -> HttpResponse {
    unreachable!()
}
);

fn policy(ctx: Arc<Context>) -> Result<()> {
    let m_sink = Identifier::new_intern("sink");
    let m_sensitive = Identifier::new_intern("sensitive");
    let m_send = Identifier::new_intern("metrics_server");
    ctx.clone().named_policy(
        Identifier::new_intern("personal tags not in metrics"),
        |ctx| {
            for sink in ctx.nodes_marked_any_way(m_sink) {
                for src in ctx.nodes_marked_any_way(m_sensitive) {
                    let mut intersections = sink
                        .influencers(&ctx, EdgeSelection::Data)
                        .into_iter()
                        .filter(|intersection| {
                            src.flows_to(*intersection, &ctx, EdgeSelection::Data)
                        });
                    if let Some(intersection) = intersections.next() {
                        let mut msg = ctx
                            .struct_node_error(intersection, "This call releases sensitive data");
                        msg.with_node_note(src, "Sensitive data originates here");
                        msg.with_node_note(intersection, "Externalizing value originates here");
                        msg.emit();
                    }
                }
            }
            Ok(())
        },
    )?;
    ctx.named_policy(Identifier::new_intern("personal tags not sent"), |ctx| {
        let personals = ctx.nodes_marked_any_way(m_sensitive).collect::<Box<[_]>>();
        let sends = ctx.nodes_marked_any_way(m_send).collect::<Box<[_]>>();
        if let Some((from, to)) = ctx.any_flows(&personals, &sends, EdgeSelection::Data) {
            ctx.always_happens_before([from], |_| false, |t| t == to)?
                .report(ctx);
            // let mut msg = ctx.struct_node_error(to, "This call externalizes a sensitive value");
            // msg.with_node_note(from, "Sensitive data originates here");
            // msg.emit();
        }
        Ok(())
    })
}

#[ignore = "WIP"]
#[test]
fn overtaint() -> Result<()> {
    let mut test = Test::new(CODE)?;
    // test.with_dep(["chrono@0.4"]);
    test.with_dep(["reqwest@0.11", "--features", "json"]);
    test.with_dep([
        "actix-web@4",
        "--no-default-features",
        "--features",
        "macros",
    ]);
    test.with_dep(["cadence@0.29"]);

    // test.with_dep([
    //     "actix-web-location@0.7",
    //     "--features",
    //     "actix-web-v4,maxmind,cadence",
    // ]);
    test.run(policy)
}
