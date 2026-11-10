"""Point-in-time MP diagnostics on a history-indexed balanced-ternary/fibre panel.

Source ownership, measurement time, arrival time, historical universe and
consumer version remain explicit. The covariance and MP implementation is
reused from pnf_marchenko_pastur_numeric, not reimplemented here.

This is a diagnostic and candidate-only pipeline; no PNF semantic
promotion, investment action, or historical universe backfill is admitted.
"""
from dataclasses import dataclass
from typing import Mapping, Sequence
import numpy as np
try:
    from scripts.pnf_marchenko_pastur_numeric import receipt
except ModuleNotFoundError:
    from pnf_marchenko_pastur_numeric import receipt

@dataclass(frozen=True)
class TemporalObservation:
    history: str
    event_time: int
    available_at: int
    values: Mapping[str, float]
    source: str

@dataclass(frozen=True)
class HistoricalFeature:
    history: str
    source: str
    identifier: str
    first_known_at: int
    last_valid_at: int | None = None

def asof_mp(
    observations: Sequence[TemporalObservation],
    universe: Sequence[HistoricalFeature],
    *,
    history: str,
    asof: int,
    consumer_version: str,
    source: str,
    measurement: str,
    balanced_trit_native: bool = False,
):
    if not history or not source or not consumer_version or not measurement:
        raise ValueError("history/source/consumer/measurement receipts required")
    eligible_meta = [f for f in universe if f.history == history and f.source == source]
    if len({f.identifier for f in eligible_meta}) != len(eligible_meta):
        raise ValueError("duplicate source feature IDs")
    if any(f.last_valid_at is not None and f.last_valid_known_at is None
           for f in eligible_meta):
        raise ValueError("membership end date lacks as-of knowledge timestamp")
    features = [f.identifier for f in eligible_meta
                if f.first_known_at <= asof
                and (f.last_valid_at is None
                     or asof < f.last_valid_known_at
                     or asof <= f.last_valid_at)]
    if not features:
        raise ValueError("no point-in-time eligible features")
    window = [e for e in observations
              if e.history == history and e.event_time <= asof
              and e.available_at <= asof and e.source == source
              and all(feature in e.values for feature in features)]
    window.sort(key=lambda e: (e.event_time, e.available_at))
    if len(window) < 2:
        raise ValueError("fewer than two admissible complete observations")
    data = np.array([[e.values[f] for f in features] for e in window],
                    dtype=float)
    if balanced_trit_native and not np.isin(data, [-1, 0, 1]).all():
        raise ValueError("native trit measurements must be -1, 0 or +1")
    result = receipt(data, source, measurement, correlation=True)
    return {
        "history": history, "asof": asof,
        "consumer_version": consumer_version,
        "feature_ids": features,
        "source_event_times": [e.event_time for e in window],
        "source_available_times": [e.available_at for e in window],
        "balanced_trit_native": balanced_trit_native,
        "leakage_guard": all(e.event_time <= asof and e.available_at <= asof
                             for e in window),
        "mp_diagnostic": result,
        "authority": "candidate_only; retained historical fibre and consumer version",
    }
