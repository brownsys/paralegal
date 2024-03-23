use std::{
    borrow::BorrowMut,
    fmt::Display,
    sync::{Arc, Mutex},
    time::Duration,
};

use crate::{utils::TyCtxtExt as _, TyCtxt};
use paralegal_spdg::utils::TruncatedHumanTime;
use trait_enum::DerefMut;

use crate::{rustc_data_structures::fx::FxHashSet as HashSet, LocalDefId};

/// Statsistics that are counted as durations
#[derive(Debug, Clone, Copy, strum::AsRefStr, PartialEq, Eq, enum_map::Enum)]
pub enum TimedStat {
    /// How long the rust compiler ran before our plugin got called (currently
    /// isn't accurate)
    Rustc,
    /// How long the flowistry PDG cosntruction took in total.
    Flowistry,
    /// How long it took to convert the flowistry graph to a
    /// [`paralegal_spdg::ProgramDescription`]
    Conversion,
    /// How long it took to serialize the SPDG
    Serialization,
}

#[derive(Default)]
struct StatsInner {
    timed: enum_map::EnumMap<TimedStat, Option<Duration>>,
}

impl StatsInner {
    fn record_timed(&mut self, stat: TimedStat, duration: Duration) {
        *self.timed[stat].get_or_insert(Duration::ZERO) += duration
    }
}

#[derive(Clone)]
pub struct Stats(Arc<Mutex<StatsInner>>);

impl Stats {
    fn inner_mut(&self) -> impl DerefMut<Target = StatsInner> + '_ {
        self.0.as_ref().lock().unwrap()
    }

    pub fn record_timed(&self, stat: TimedStat, duration: Duration) {
        self.inner_mut().record_timed(stat, duration)
    }
}

impl Default for Stats {
    fn default() -> Self {
        Self(Arc::new(Mutex::new(Default::default())))
    }
}

impl Display for Stats {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let borrow = self.0.as_ref().lock().unwrap();
        for (s, dur) in borrow.timed {
            if let Some(dur) = dur {
                write!(f, "{}: {} ", s.as_ref(), TruncatedHumanTime::from(dur))?;
            }
        }
        Ok(())
    }
}
