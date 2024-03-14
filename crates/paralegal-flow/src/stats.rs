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

/// Statistics that are counted without a unit
#[derive(Debug, Clone, Copy, strum::AsRefStr, PartialEq, Eq, enum_map::Enum)]
pub enum CountedStat {
    /// The number of unique lines of code we analyzed. This means MIR bodies
    /// without considering monomorphization
    UniqueLoCs,
    /// The number of unique functions we analyzed. Corresponds to
    /// [`Self::UniqueLoCs`].
    UniqueFunctions,
    /// The number of lines we ran through the PDG construction. This is higher
    /// than unique LoCs, because we need to analyze some functions multiple
    /// times, due to monomorphization and calls tring differences.
    AnalyzedLoCs,
    /// Number of functions analyzed. Corresponds to [`Self::AnalyzedLoCs`].
    AnalyzedFunctions,
    /// How many times we inlined functions. This will be higher than
    /// [`Self::AnalyzedFunction`] because sometimes the callee PDG is served
    /// from the cache.
    InliningsPerformed,
}

struct StatsInner {
    timed: enum_map::EnumMap<TimedStat, Option<Duration>>,
    counted: enum_map::EnumMap<CountedStat, Option<u32>>,
    unique_loc_set: HashSet<LocalDefId>,
}

impl StatsInner {
    fn record_timed(&mut self, stat: TimedStat, duration: Duration) {
        *self.timed[stat].get_or_insert(Duration::ZERO) += duration
    }

    fn record_counted(&mut self, stat: CountedStat, increase: u32) {
        let target = self.counted[stat].get_or_insert(0);
        if let Some(new) = target.checked_add(increase) {
            *target = new;
        } else {
            panic!("A u32 was not enough for {}", stat.as_ref());
        }
    }

    fn incr_counted(&mut self, stat: CountedStat) {
        self.record_counted(stat, 1)
    }

    fn record_inlining(&mut self, tcx: TyCtxt<'_>, def_id: LocalDefId, is_in_cache: bool) {
        let src_map = tcx.sess.source_map();
        let span = tcx.body_for_def_id(def_id).unwrap().body.span;
        let (_, start_line, _, end_line, _) = src_map.span_to_location_info(span);
        let body_lines = (end_line - start_line) as u32;
        self.incr_counted(CountedStat::InliningsPerformed);
        if self.unique_loc_set.borrow_mut().insert(def_id) {
            self.incr_counted(CountedStat::UniqueFunctions);
            self.record_counted(CountedStat::UniqueLoCs, body_lines);
        }
        if !is_in_cache {
            self.incr_counted(CountedStat::AnalyzedFunctions);
            self.record_counted(CountedStat::AnalyzedLoCs, body_lines);
        }
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

    pub fn record_counted(&self, stat: CountedStat, increase: u32) {
        self.inner_mut().record_counted(stat, increase)
    }

    pub fn incr_counted(&self, stat: CountedStat) {
        self.inner_mut().incr_counted(stat)
    }

    pub fn record_inlining(&self, tcx: TyCtxt<'_>, def_id: LocalDefId, is_in_cache: bool) {
        self.inner_mut().record_inlining(tcx, def_id, is_in_cache)
    }
}

impl Default for Stats {
    fn default() -> Self {
        Self(Arc::new(Mutex::new(Default::default())))
    }
}

impl Default for StatsInner {
    fn default() -> Self {
        StatsInner {
            timed: Default::default(),
            counted: Default::default(),
            unique_loc_set: Default::default(),
        }
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
        for (c, count) in borrow.counted {
            if let Some(count) = count {
                write!(f, "{}: {} ", c.as_ref(), count)?;
            }
        }
        Ok(())
    }
}
