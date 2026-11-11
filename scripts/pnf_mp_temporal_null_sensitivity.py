"""Source-qualified MP-vs-temporal-surrogate spectral diagnostic.

Synthetic demonstrations only. An IID Marchenko-Pastur bulk boundary does
not establish a valid finite-sample null for temporally dependent panels.
Circular shifts preserve each column's observed within-column time structure
but change contemporaneous cross-column alignment. They are NOT a universal
valid bootstrap and cannot establish statistical significance or causality.
"""
from dataclasses import dataclass
import numpy as np

from scripts.pnf_marchenko_pastur_numeric import MPNull, covariance


@dataclass(frozen=True)
class TemporalNullReceipt:
    source: str
    window_label: str
    n: int
    p: int
    iid_mp_upper_edge: float
    observed_top_eigenvalue: float
    circular_shift_top_quantile95: float
    iid_above_edge: bool
    surrogate_above_empirical95: bool
    surrogate_count: int
    qualification: str


def columnwise_ar1(*, n: int, p: int, rho: float, seed: int) -> np.ndarray:
    """Independent-column AR(1) *synthetic* panel, no common market factor."""
    if n < 3 or p < 2 or not np.isfinite(rho) or abs(rho) >= 1:
        raise ValueError("n>=3, p>=2 and |rho|<1 required")
    rng = np.random.default_rng(seed)
    noise = rng.standard_normal((n, p))
    x = np.empty_like(noise)
    x[0] = noise[0]
    for t in range(1, n):
        x[t] = rho * x[t - 1] + np.sqrt(1 - rho * rho) * noise[t]
    return x


def temporal_null_receipt(
    x: np.ndarray,
    *,
    source: str,
    window_label: str,
    seed: int = 20261111,
    surrogate_count: int = 100,
) -> TemporalNullReceipt:
    """Compare IID-MP upper edge against a source-labelled shift surrogate.

    Surrogate 95% quantile is a finite descriptive statistic of a selected
    algorithm, NOT a calibrated p-value or proof of null exchangeability.
    """
    if not source or not window_label or surrogate_count < 20:
        raise ValueError("source, window_label and >=20 surrogates required")
    a = np.asarray(x, dtype=float)
    if a.ndim != 2 or a.shape[0] < 3 or a.shape[1] < 2:
        raise ValueError("need n>=3, p>=2 panel")
    c = covariance(a, correlation=True)
    n, p = a.shape
    upper = MPNull(p / (n - 1)).edges[1]
    observed = float(np.linalg.eigvalsh(c)[-1])
    rng = np.random.default_rng(seed)
    maxima = []
    for _ in range(surrogate_count):
        shifted = np.column_stack(
            [np.roll(a[:, j], rng.integers(0, n)) for j in range(p)]
        )
        maxima.append(float(np.linalg.eigvalsh(
            covariance(shifted, correlation=True)
        )[-1]))
    threshold = float(np.quantile(maxima, 0.95))
    return TemporalNullReceipt(
        source=source, window_label=window_label, n=n, p=p,
        iid_mp_upper_edge=upper, observed_top_eigenvalue=observed,
        circular_shift_top_quantile95=threshold,
        iid_above_edge=bool(observed > upper),
        surrogate_above_empirical95=bool(observed > threshold),
        surrogate_count=surrogate_count,
        qualification=(
            "synthetic candidate only; circular shifts preserve per-column "
            "temporal autocorrelation but do not validate exchangeability, "
            "iid MP assumptions, causal interpretations, or trading permission"
        ),
    )
