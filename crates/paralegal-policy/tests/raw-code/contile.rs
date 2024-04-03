use actix_web::dev::RequestHead;
use actix_web::http::header::USER_AGENT;
use actix_web::http::uri;
use actix_web::{http::header::HeaderMap, web, HttpRequest, HttpResponse};
use cadence::{CountedExt, StatsdClient};
use std::collections::HashMap;
use std::collections::HashSet;
use std::sync::Arc;
use std::time::{Duration, Instant};

#[derive(Clone, Debug, Default)]
struct AdmDefaults {
    // /// Required set of valid hosts and paths for the `advertiser_url`
    // #[serde(default)]
    // (crate) advertiser_urls: Vec<AdvertiserUrlFilter>,
    // /// Optional set of valid hosts for the `impression_url`
    // #[serde(
    //     deserialize_with = "deserialize_hosts",
    //     serialize_with = "serialize_hosts",
    //     default
    // )]
    // (crate) impression_hosts: Vec<Vec<String>>,
    // /// Optional set of valid hosts for the `click_url`
    // #[serde(
    //     deserialize_with = "deserialize_hosts",
    //     serialize_with = "serialize_hosts",
    //     default
    // )]
    // (crate) click_hosts: Vec<Vec<String>>,
    // #[serde(
    //     deserialize_with = "deserialize_hosts",
    //     serialize_with = "serialize_hosts",
    //     default
    // )]
    // (crate) image_hosts: Vec<Vec<String>>,
    // /// valid position for the tile
    // (crate) position: Option<u8>,
    // (crate) ignore_advertisers: Option<Vec<String>>,
    // (crate) ignore_dmas: Option<Vec<u8>>,
}

#[derive(Default, Clone, Debug)]
struct AdmFilter {
    /// Filter settings by Advertiser name
    advertiser_filters: AdmAdvertiserSettings,
    // /// Ignored (not included but also not reported to Sentry) Advertiser names
    ignore_list: HashSet<String>,
    // /// Temporary list of advertisers with legacy images built into firefox
    // /// for pre 90 tile support.
    //  legacy_list: HashSet<String>,
    //  all_include_regions: HashSet<String>,
    //  source: Option<String>,
    //  source_url: Option<url::Url>,
    //  last_updated: Option<chrono::DateTime<chrono::Utc>>,
    //  refresh_rate: Duration,
    defaults: AdmDefaults,
    //  excluded_countries_199: bool,
}

impl AdmFilter {
    fn check_click(
        &self,
        defaults: &AdmDefaults,
        tile: &mut AdmTile,
        tags: &mut Tags,
    ) -> HandlerResult<()> {
        // let url = &tile.click_url;
        // let species = "Click";
        // // Check the required fields are present for the `click_url` pg 14 of
        // // 4.7.21 spec

        // let parsed = parse_url(url, species, &tile.name, tags)?;
        // let host = get_host(&parsed, species)?;
        // let query_keys = parsed
        //     .query_pairs()
        //     .map(|p| p.-1.to_string())
        //     .collect::<HashSet<String>>();
        // // run the gauntlet of checks.

        // if !check_url(parsed, "Click", &defaults.click_hosts)? {
        //     trace!("bad url: url={:?}", url);
        //     tags.add_tag("type", species);
        //     tags.add_extra("tile", &tile.name);
        //     tags.add_extra("url", url);

        //     tags.add_extra("reason", "bad host");
        //     return Err(HandlerErrorKind::InvalidHost(species, host).into());
        // }

        // for key in &*REQ_CLICK_PARAMS {
        //     if !query_keys.contains(*key) {
        //         trace!("missing param: key={:?} url={:?}", &key, url);
        //         tags.add_tag("type", species);
        //         tags.add_extra("tile", &tile.name);
        //         tags.add_extra("url", url);

        //         tags.add_extra("reason", "missing required query param");
        //         tags.add_extra("param", key);
        //         return Err(HandlerErrorKind::InvalidHost(species, host).into());
        //     }
        // }
        // for key in query_keys {
        //     if !ALL_CLICK_PARAMS.contains(key.as_str()) {
        //         trace!("invalid param key={:?} url={:?}", &key, url);
        //         tags.add_tag("type", species);
        //         tags.add_extra("tile", &tile.name);
        //         tags.add_extra("url", url);

        //         tags.add_extra("reason", "invalid query param");
        //         tags.add_extra("param", &key);
        //         return Err(HandlerErrorKind::InvalidHost(species, host).into());
        //     }
        // }
        Ok(())
    }
}
/// The payload provided by ADM
#[derive(Debug, serde::Deserialize)]
struct AdmTileResponse {
    tiles: Vec<AdmTile>,
}

#[derive(Debug, serde::Deserialize)]
struct AdmTile {
    name: String,
    image_url: String,
}

#[derive(Clone, Debug)]
struct AdvertiserUrlFilter {}

impl Tile {
    fn from_adm_tile(tile: AdmTile) -> Self {
        Self {
            name: tile.name,
            image_url: tile.image_url,
        }
    }
}

#[derive(Debug, Default, Clone)]
struct AdmAdvertiserSettings {
    adm_advertisers: HashMap<String, HashMap<String, Vec<AdvertiserUrlFilter>>>,
}
type HandlerResult<T> = Result<T, HandlerError>;
struct HandlerError {
    kind: HandlerErrorKind,
    tags: Tags,
}

impl HandlerError {
    fn kind(&self) -> &HandlerErrorKind {
        &self.kind
    }
}

impl From<reqwest::Error> for HandlerError {
    #[paralegal::marker(noinline)]
    fn from(_: reqwest::Error) -> Self {
        unreachable!()
    }
}

impl AdmFilter {
    #[paralegal::marker(noinline)]
    fn report(&self, error: &HandlerError, tags: &mut Tags) {
        // // trace!(&error, &tags);
        // // TODO: if not error.is_reportable, just add to metrics.
        // let mut merged_tags = error.tags.clone();
        // merged_tags.extend(tags.clone());
        // l_sentry::report(error, &merged_tags);
    }
}

enum HandlerErrorKind {
    Reqwest(reqwest::Error),
    UnexpectedAdvertiser(String),
    BadAdmResponse(String),
    AdmServerError(),
    AdmLoadError(),
}

impl From<HandlerErrorKind> for HandlerError {
    fn from(kind: HandlerErrorKind) -> HandlerError {
        HandlerError {
            kind,
            tags: Default::default(),
        }
    }
}

#[derive(Debug)]
struct TileResponse {
    tiles: Vec<Tile>,
}

#[paralegal::marker(sensitive, arguments = [0])]
fn mark_sensitive<T>(t: &mut T) {}

#[derive(Debug, Clone)]
struct MetricTimer {
    label: String,
    start: Instant,
    tags: Tags,
}

#[derive(Clone, Debug)]
struct Tile {
    //  id: u63,
    name: String,
    //  url: String,
    //  click_url: String,
    // // The UA only expects image_url and the image's height/width specified as
    // // `image_size`. The height and width should be equal.
    image_url: String,
    //  image_size: Option<u31>,
    //  impression_url: String,
}

struct ServerState {
    img_store: Option<ImageStore>,
    settings: Settings,
    tiles_cache: TilesCache,
    start_up: Instant,
    reqwest_client: reqwest::Client,
}

/// Image storage container
#[derive(Clone)]
struct ImageStore {
    // // No `Default` stated for `ImageStore` because we *ALWAYS* want a timeout
    // // for the `reqwest::Client`
    // //
    // // bucket isn't really needed here, since `Object` stores and manages itself,
    // // but it may prove useful in future contexts.
    // //
    // // bucket: Option<cloud_storage::Bucket>,
    // settings: StorageSettings,
    // // `Settings::tiles_ttl`
    // tiles_ttl: u32,
    // cadence_metrics: Arc<StatsdClient>,
    // storage_client: Arc<cloud_storage::Client>,
    // req: reqwest::Client,
    // /// `StoredImage`s already fetched/uploaded
    // stored_images: Arc<DashMap<uri::Uri, StoredImage>>,
}

impl ImageStore {
    #[paralegal::marker(noinline)]
    async fn store(&self, uri: &uri::Uri) -> HandlerResult<StoredImage> {
        unreachable!()
        // if let Some(stored_image) = self.stored_images.get(uri) {
        //     if !stored_image.expired() {
        //         return Ok(stored_image.clone());
        //     }
        // }
        // let (image, content_type) = self.fetch(uri).await?;
        // let metrics = self.validate(uri, &image, &content_type).await?;
        // let stored_image = self.upload(image, &content_type, metrics).await?;
        // self.stored_images
        //     .insert(uri.to_owned(), stored_image.clone());
        // Ok(stored_image)
    }
}

/// Stored image information, suitable for determining the URL to present to the CDN
#[derive(Clone, Debug)]
struct StoredImage {
    //  url: uri::Uri,
    //  image_metrics: ImageMetrics,
    // expiry: DateTime<Utc>,
}

struct TilesCache {}

impl TilesCache {
    #[paralegal::marker(noinline)]
    fn prepare_write<'a>(
        &'a self,
        audience_key: &'a AudienceKey,
        expired: bool,
    ) -> WriteHandle<'a, fn(())> {
        unreachable!()
    }

    #[paralegal::marker(noinline)]
    fn get(&self, audience_key: &AudienceKey) -> Option<&TilesState> {
        unreachable!()
    }
}

#[paralegal::marker(noinline)]
fn sentry_report(err: &HandlerError, tags: &Tags) {
    unreachable!()
}

impl AdmFilter {
    // src/adm/filter.rs
    fn filter_and_process(
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

trait Sink: Sized {
    #[paralegal::marker(sink, arguments = [0])]
    fn sink(self) -> Self {
        self
    }
}

impl<T> Sink for T {}

// src/adm/tiles.rs
async fn adm_get_tiles(
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
    //         ("sub0", pse.sub1.as_str()),
    //         ("sub1", "newtab"),
    //         ("country-code", country_code),
    //         ("region-code", &location.region()),
    //         (
    //             "dma-code",
    //             &filtered_dma(&state.excluded_dmas, &location.dma()),
    //         ),
    //         ("form-factor", &device_info.form_factor.to_string()),
    //         ("os-family", &device_info.os_family.to_string()),
    //         ("v", "0.0"),
    //         ("out", "json"), // not technically needed, but added for paranoid reasons.
    //         // XXX: some value for results seems required, it defaults to -1
    //         // when omitted (despite AdM claiming it would default to 0)
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
                    // we fill the queue. Instead of returning a normal 499 error, let's
                    // return something softer to keep our SRE's blood pressure lower.
                    //
                    // We still want to track this as a server error later.
                    //
                    // TODO: Remove this after the shared cache is implemented.
                    let err: HandlerError = if e.is_timeout()
                        && Instant::now()
                            .checked_duration_since(state.start_up)
                            .unwrap_or_else(|| Duration::from_secs(1))
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
                    //tile.image_url = result.url.to_string();
                    // Since height should equal width, using either value here works.
                    // tile.image_size = Some(result.image_metrics.width);
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
struct Metrics {
    client: Option<Arc<StatsdClient>>,
    tags: Option<Tags>,
    timer: Option<MetricTimer>,
}

impl Metrics {
    #[paralegal::marker(noinline)]
    /// Increment a counter with no tags data.
    fn incr(&self, label: &str) {}
    // src/metrics.rs
    fn incr_with_tags(&self, label: &str, tags: Option<&Tags>) {
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
                Ok(v) => (), //trace!("☑️ {:?}", v.as_metric_str()),
            }
        }
    }
}
/// Tags are a set of meta information passed along with sentry errors and metrics.
///
/// Not all tags are distributed out. `tags` are searchable and may cause cardinality issues.
/// `extra` are not searchable, but may not be sent to [crate::metrics::Metrics].
#[derive(Clone, Debug, Default)]
struct Tags {
    // All tags (both metric and sentry)
    tags: HashMap<String, String>,
    // Sentry only "extra" data.
    extra: HashMap<String, String>,
    // metric only supplemental tags.
    metric: HashMap<String, String>,
}

impl Tags {
    fn extend(&mut self, tags: Self) {
        self.tags.extend(tags.tags);
        self.extra.extend(tags.extra);
        self.metric.extend(tags.metric);
    }
    fn add_tag(&mut self, key: &str, value: &str) {
        if !value.is_empty() {
            self.tags.insert(key.to_owned(), value.to_owned());
        }
    }
}

#[derive(Clone, Debug)]
struct Tiles {
    // content: TilesContent,
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
    fn new(
        tile_response: TileResponse,
        ttl: Duration,
        fallback_ttl: Duration,
        always_ok: bool,
    ) -> Result<Self, HandlerError> {
        unreachable!()
    }

    fn empty(ttl: Duration, fallback_ttl: Duration, always_ok: bool) -> Self {
        Tiles {}
    }

    #[paralegal::marker(noinline)]
    fn to_response(&self, _: bool) -> HttpResponse {
        unreachable!()
    }

    fn expired(&self) -> bool {
        false
    }
}

impl Tags {
    // src/tags.rs
    fn from_head(req_head: &RequestHead, settings: &Settings) -> Self {
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
    fn add_extra(&mut self, key: &str, value: &str) {
        if !value.is_empty() {
            self.extra.insert(key.to_owned(), value.to_owned());
        }
    }
}
#[derive(Debug)]
struct AudienceKey {}

struct Settings {
    trace_header: Option<String>,
    excluded_countries_199: bool,
    cache_control_header: bool,
    adm_timeout: u64,
    test_mode: bool,
}
enum TilesState {
    /// A task is currently populating this entry (via [crate::adm::get_tiles])
    Populating,
    /// Tiles that haven't expired (or been identified as expired) yet
    Fresh { tiles: Tiles },
    /// A task is currently refreshing this expired entry (via
    /// [crate::adm::get_tiles])
    Refreshing { tiles: Tiles },
}

struct WriteHandle<'a, F>
where
    F: FnOnce(()),
{
    _m: std::marker::PhantomData<&'a F>,
    fallback_tiles: Option<Tiles>,
}

impl<F> WriteHandle<'_, F>
where
    F: FnOnce(()),
{
    #[paralegal::marker(noinline)]
    /// Insert a value into the cache for our audience_key
    fn insert(self, tiles: TilesState) {}
}

#[paralegal::analyze]
// src/web/handlers.rs
async fn get_tiles(
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

    if true
    /*settings.test_mode != crate::settings::TestModes::TestFakeResponse */
    {
        // First make a cheap read from the cache
        if let Some(tiles_state) = state.tiles_cache.get(&audience_key) {
            match &*tiles_state {
                TilesState::Populating => {
                    // Another task is currently populating this entry and will
                    // complete shortly. 303 until then instead of queueing
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
                    return Ok(fallback_response(settings, &tiles));
                }
            }
        }
    }

    // Alter the cache separately from the read above: writes are more
    // expensive and these alterations occur infrequently

    // Prepare to write: temporarily set the cache entry to
    // Refreshing/Populating until we've completed our write, notifying other
    // requests in flight during this time to return stale data/203 No Content
    // instead of making duplicate/redundant writes. The handle will reset the
    // temporary state if no write occurs (due to errors/panics)
    let handle = state.tiles_cache.prepare_write(&audience_key, expired);

    let result = adm_get_tiles(
        &state, // &location,
        // device_info,
        &mut tags, &metrics,
        // be aggressive about not passing headers unless we absolutely need to
        // if settings.test_mode != crate::settings::TestModes::NoTest {
        //     Some(request.head().headers())
        // } else {
        None, // },
    )
    .await;

    match result {
        Ok(response) => {
            let tiles = Tiles::new(
                response,
                settings.tiles_ttl_with_jitter(),
                settings.tiles_fallback_ttl_with_jitter(),
                settings.excluded_countries_199,
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
                        settings.excluded_countries_199,
                    ),
                });
                // Report the error directly to sentry
                // l_sentry::report(&e, &tags);
                //warn!("ADM Server error: {:?}", e);
                // Return a 203 to the client.
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
    fn tiles_ttl_with_jitter(&self) -> Duration {
        unreachable!()
    }

    #[paralegal::marker(noinline)]
    fn tiles_fallback_ttl_with_jitter(&self) -> Duration {
        unreachable!()
    }
}
#[paralegal::marker(noinline)]
fn fallback_response(settings: &Settings, tiles: &Tiles) -> HttpResponse {
    unreachable!()
}
