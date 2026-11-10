"""Point-in-time covariance risk backtest. Diagnostic only; never emits orders.

Uses the existing MP numerical owner and historical source/universe records.
Every prediction is made at an as-of time from observations available then.
The later realised return is used exclusively for scoring, never fitting.
"""
from dataclasses import dataclass
from typing import Sequence
import numpy as np

try:
    from scripts.pnf_history_time_mp import TemporalObservation, HistoricalFeature
    from scripts.pnf_marchenko_pastur_numeric import MPNull, covariance, clean
except ModuleNotFoundError:
    from pnf_history_time_mp import TemporalObservation, HistoricalFeature
    from pnf_marchenko_pastur_numeric import MPNull, covariance, clean


@dataclass(frozen=True)
class RiskForecastReceipt:
    history: str
    source: str
    asof: int
    evaluation_time: int
    feature_ids: tuple[str, ...]
    training_count: int
    training_latest_time: int
    training_latest_available_at: int
    realized_available_at: int
    consumer_version: str
    benchmark_variance: float
    cleaned_variance: float
    realised_squared_return: float
    benchmark_squared_error: float
    cleaned_squared_error: float


def _features(universe: Sequence[HistoricalFeature], history: str,
              source: str, asof: int) -> tuple[str, ...]:
    selected = [f.identifier for f in universe
                if f.history == history and f.source == source
                and f.first_known_at <= asof
                and (f.last_valid_at is None or asof <= f.last_valid_at)]
    if len(set(selected)) != len(selected):
        raise ValueError("duplicate historical feature identifier")
    return tuple(selected)


def forecast_one_step(
    observations: Sequence[TemporalObservation],
    universe: Sequence[HistoricalFeature],
    *, history: str, source: str, asof: int, consumer_version: str,
    weights: Sequence[float], min_training: int = 5,
) -> RiskForecastReceipt:
    if not history or not source or not consumer_version:
        raise ValueError("history, source and consumer version required")
    if min_training < 3:
        raise ValueError("at least three training observations required")
    features = _features(universe, history, source, asof)
    if not features:
        raise ValueError("no historical assets")
    w = np.asarray(weights, dtype=float)
    if w.shape != (len(features),) or not np.isfinite(w).all():
        raise ValueError("weights must match point-in-time universe")
    if any(o.available_at < o.event_time for o in observations\n           if o.history == history and o.source == source):\n        raise ValueError("source availability predates event")\n    # Complete-case, strictly as-of training. A feature admitted today may
    # not be backfilled into yesterday's observations.
    selected = [o for o in observations if o.history == history
                and o.source == source and o.event_time <= asof
                and o.available_at <= asof
                and all(f in o.values for f in features)]
    selected.sort(key=lambda o: (o.event_time, o.available_at))
    if len(selected) < min_training:
        raise ValueError("insufficient historically available training")
    if len({o.event_time for o in selected}) != len(selected):
        raise ValueError("multiple observations for same event time")
    # One actual later target; its measurement is *not* used for fitting.
    future = sorted([o for o in observations if o.history == history
                     and o.source == source and o.event_time > asof
                     and all(f in o.values for f in features)],
                    key=lambda o: (o.event_time, o.available_at))
    if not future:
        raise ValueError("no held-out future observation")
    target = future[0]
    x = np.array([[o.values[f] for f in features] for o in selected],
                 dtype=float)
    y = np.array([target.values[f] for f in features], dtype=float)
    if not np.isfinite(x).all() or not np.isfinite(y).all():
        raise ValueError("nonfinite observations")
    sample = covariance(x, correlation=False)
    gamma = len(features) / (len(selected)-1)
    variance = float(np.trace(sample) / len(features))
    if variance <= 0:
        raise ValueError("zero sample variance")
    mp = MPNull(gamma, variance)
    filtered, _ = clean(sample, mp, correlation=False)
    base_pred = float(w @ sample @ w)
    clean_pred = float(w @ filtered @ w)
    # Held-out variance proxy is an ex-post squared surprise centred on
    # the *training* mean; future mean is never used.
    realised = float((w @ (y - x.mean(axis=0)))**2)
    return RiskForecastReceipt(
        history, source, asof, target.event_time, features, len(selected),
        selected[-1].event_time, max(o.available_at for o in selected),
        target.available_at, consumer_version,
        base_pred, clean_pred, realised,
        (base_pred-realised)**2, (clean_pred-realised)**2,
    )


def assess_walkforward(receipts: Sequence[RiskForecastReceipt],
                       *, qualification_asof: int, min_folds: int = 5) -> dict:
    if min_folds < 2 or len(receipts) < min_folds:
        raise ValueError("insufficient out-of-sample folds")
    if any(r.training_latest_time > r.asof
           or r.training_latest_available_at > r.asof
           or r.evaluation_time <= r.asof for r in receipts):
        raise ValueError("lookahead or non-forward evaluation")
    if any(r.realized_available_at > qualification_asof for r in receipts):
        raise ValueError("held-out realization unavailable at qualification time")
    if any(r.asof > qualification_asof for r in receipts):
        raise ValueError("forecast decision after qualification time")
    if len({(r.history, r.source, r.consumer_version, r.feature_ids)
            for r in receipts}) != 1:
        raise ValueError("mixed historical fibres, versions or feature universes")
    base = float(np.mean([r.benchmark_squared_error for r in receipts]))
    cleaned = float(np.mean([r.cleaned_squared_error for r in receipts]))
    return {"folds":len(receipts), "qualification_asof": qualification_asof,
            "history": receipts[0].history, "source": receipts[0].source,
            "consumer_version":receipts[0].consumer_version,
            "feature_ids":receipts[0].feature_ids,
            "baseline_loss":base,
            "mp_cleaned_loss":cleaned,
            "cleaned_improved_on_this_holdout":cleaned < base,
            "risk_quality_conclusion":"empirical_holdout_only",
            "trade_authority":False, "alpha_claim":False}
