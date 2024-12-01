use std::{
    fmt::Display,
    sync::{Arc, Mutex},
    time::{Duration, Instant},
};

use paralegal_spdg::utils::TruncatedHumanTime;
use trait_enum::DerefMut;

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

struct StatsInner {
    timed: enum_map::EnumMap<TimedStat, Option<Duration>>,
    started: Instant,
}

impl Default for StatsInner {
    fn default() -> Self {
        Self {
            started: std::time::Instant::now(),
            timed: Default::default(),
        }
    }
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

    pub fn get_timed(&self, stat: TimedStat) -> Duration {
        self.0.lock().unwrap().timed[stat].unwrap_or(Duration::ZERO)
    }

    pub fn elapsed(&self) -> Duration {
        self.0.lock().unwrap().started.elapsed()
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
