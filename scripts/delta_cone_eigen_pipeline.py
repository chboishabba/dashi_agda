#!/usr/bin/env python3
"""Arrow-separated delta-cone, delta-Hecke, and signature-mask search."""

from __future__ import annotations

import argparse
import itertools
import json
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Iterable

import numpy as np
import pandas as pd

ARROW_COL = "v_arrow"
DEFAULT_FEATURE_COLS = ["v_pnorm", "v_dnorm", "v_depth"]
EPS_ARROW = 1e-9
EPS_CONE = 1e-12
SSP_PRIMES = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 41, 47, 59, 71]


@dataclass(frozen=True)
class SignatureMask:
    signs: tuple[int, ...]

    @property
    def p(self) -> int:
        return sum(1 for s in self.signs if s > 0)

    @property
    def q(self) -> int:
        return sum(1 for s in self.signs if s < 0)

    @property
    def z(self) -> int:
        return sum(1 for s in self.signs if s == 0)

    @property
    def nondegenerate(self) -> bool:
        return self.z == 0

    @property
    def lorentz_like(self) -> bool:
        return self.q == 1 and self.z == 0

    @property
    def indefinite(self) -> bool:
        return self.p > 0 and self.q > 0

    def label(self) -> str:
        return "".join("+" if s > 0 else "-" if s < 0 else "0" for s in self.signs)


@dataclass
class SignatureResult:
    mask: SignatureMask
    cone_frac_forward: float
    forward_frac: float
    strict_forward_count: int
    total_step_count: int
    qd_max: float
    qd_mean: float
    qd_min: float
    hecke_entropy_mean: float
    hecke_popcount_mean: float


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--csv", required=True, help="Input CSV trace file")
    parser.add_argument("--arrow-col", default=ARROW_COL, help="Arrow / time column")
    parser.add_argument(
        "--feature-cols",
        nargs="+",
        default=DEFAULT_FEATURE_COLS,
        help="Feature columns used to compute Delta-vectors",
    )
    parser.add_argument("--eps-arrow", type=float, default=EPS_ARROW)
    parser.add_argument("--eps-cone", type=float, default=EPS_CONE)
    parser.add_argument(
        "--strict-forward",
        action="store_true",
        help="Require Delta(arrow) > eps_arrow instead of allowing small reversals",
    )
    parser.add_argument(
        "--require-nondegenerate",
        action="store_true",
        help="Restrict search to masks with z == 0",
    )
    parser.add_argument(
        "--require-indefinite",
        action="store_true",
        help="Restrict search to mixed-signature masks with both positive and negative directions",
    )
    parser.add_argument(
        "--top-k",
        type=int,
        default=10,
        help="Number of top-ranked masks to report",
    )
    parser.add_argument(
        "--output-prefix",
        default=None,
        help="Optional prefix for CSV outputs; defaults beside the input file",
    )
    parser.add_argument("--json", action="store_true", help="Emit JSON summary")
    return parser.parse_args()


def load_embedding_csv(
    path: Path,
    feature_cols: list[str],
    arrow_col: str,
) -> tuple[np.ndarray, np.ndarray, list[str]]:
    df = pd.read_csv(path)
    cols = [c for c in feature_cols if c in df.columns]
    missing = [c for c in cols + [arrow_col] if c not in df.columns]
    if missing:
        raise ValueError(f"Missing columns: {missing}")
    x = df[cols].to_numpy(dtype=float)
    a = df[arrow_col].to_numpy(dtype=float)
    return x, a, cols


def delta_view(x: np.ndarray, a: np.ndarray) -> tuple[np.ndarray, np.ndarray]:
    return x[1:] - x[:-1], a[1:] - a[:-1]


def forward_mask(da: np.ndarray, eps_arrow: float, strict_forward: bool) -> np.ndarray:
    if strict_forward:
        return da > eps_arrow
    return da >= -eps_arrow


def robust_scale_rows(x: np.ndarray) -> np.ndarray:
    med = np.median(x, axis=0)
    mad = np.median(np.abs(x - med), axis=0) + 1e-12
    z = (x - med) / (1.4826 * mad)
    return np.tanh(z)


def prime_valuation_integer(n: int, p: int) -> int:
    n = abs(n)
    if n == 0:
        return 0
    v = 0
    while n % p == 0:
        n //= p
        v += 1
    return v


def quantize_delta(dx: np.ndarray, scale: float = 1000.0) -> np.ndarray:
    return np.round(dx * scale).astype(np.int64)


def delta_hecke_scan(dx: np.ndarray) -> np.ndarray:
    qdx = quantize_delta(dx)
    n_steps, _ = qdx.shape
    feats = np.zeros((n_steps, len(SSP_PRIMES)), dtype=np.int64)
    for i in range(n_steps):
        row = qdx[i]
        for j, p in enumerate(SSP_PRIMES):
            feats[i, j] = sum(prime_valuation_integer(int(v), p) for v in row)
    return feats


def hecke_popcount(hecke_feats: np.ndarray) -> np.ndarray:
    return (hecke_feats > 0).sum(axis=1)


def hecke_entropy(hecke_feats: np.ndarray) -> np.ndarray:
    out = np.zeros(hecke_feats.shape[0], dtype=float)
    for i, row in enumerate(hecke_feats):
        s = row.sum()
        if s <= 0:
            continue
        p = row / s
        p = p[p > 0]
        out[i] = float(-(p * np.log2(p)).sum())
    return out


def all_signature_masks(d: int) -> Iterable[SignatureMask]:
    for signs in itertools.product([-1, 0, 1], repeat=d):
        yield SignatureMask(tuple(signs))


def q_mask(dx: np.ndarray, mask: SignatureMask) -> np.ndarray:
    w = np.asarray(mask.signs, dtype=float)
    return (dx * dx * w).sum(axis=1)


def cone_fraction_forward(
    shape_dx: np.ndarray,
    da: np.ndarray,
    mask: SignatureMask,
    eps_cone: float,
    eps_arrow: float,
    strict_forward: bool,
) -> tuple[float, float, np.ndarray]:
    fwd = forward_mask(da, eps_arrow=eps_arrow, strict_forward=strict_forward)
    qd = q_mask(shape_dx, mask)
    if int(fwd.sum()) == 0:
        return 0.0, 0.0, qd
    cone_ok = qd <= eps_cone
    return float(cone_ok[fwd].mean()), float(fwd.mean()), qd


def search_signatures(
    shape_dx: np.ndarray,
    da: np.ndarray,
    hecke_feats: np.ndarray,
    eps_cone: float,
    eps_arrow: float,
    require_nondegenerate: bool,
    require_indefinite: bool,
    strict_forward: bool,
) -> list[SignatureResult]:
    ent = hecke_entropy(hecke_feats)
    pop = hecke_popcount(hecke_feats)
    results: list[SignatureResult] = []
    fwd = forward_mask(da, eps_arrow=eps_arrow, strict_forward=strict_forward)

    for mask in all_signature_masks(shape_dx.shape[1]):
        if require_nondegenerate and not mask.nondegenerate:
            continue
        if require_indefinite and not mask.indefinite:
            continue
        cone_frac, fwd_frac, qd = cone_fraction_forward(
            shape_dx, da, mask, eps_cone, eps_arrow, strict_forward
        )
        results.append(
            SignatureResult(
                mask=mask,
                cone_frac_forward=cone_frac,
                forward_frac=fwd_frac,
                strict_forward_count=int(fwd.sum()),
                total_step_count=int(len(da)),
                qd_max=float(np.max(qd)),
                qd_mean=float(np.mean(qd)),
                qd_min=float(np.min(qd)),
                hecke_entropy_mean=float(np.mean(ent)),
                hecke_popcount_mean=float(np.mean(pop)),
            )
        )

    results.sort(
        key=lambda r: (-r.cone_frac_forward, -r.forward_frac, r.mask.z, abs(r.qd_max))
    )
    return results


def summarize_top(results: list[SignatureResult], top_k: int) -> pd.DataFrame:
    rows = []
    for r in results[:top_k]:
        rows.append(
            {
                "mask": r.mask.label(),
                "p": r.mask.p,
                "q": r.mask.q,
                "z": r.mask.z,
                "nondegenerate": r.mask.nondegenerate,
                "indefinite": r.mask.indefinite,
                "lorentz_like": r.mask.lorentz_like,
                "cone_frac_forward": r.cone_frac_forward,
                "forward_frac": r.forward_frac,
                "qd_min": r.qd_min,
                "qd_mean": r.qd_mean,
                "qd_max": r.qd_max,
                "hecke_entropy_mean": r.hecke_entropy_mean,
                "hecke_popcount_mean": r.hecke_popcount_mean,
            }
        )
    return pd.DataFrame(rows)


def ccr_surrogate(dx: np.ndarray) -> pd.DataFrame:
    d = dx.shape[1]
    mid = d // 2
    if mid == 0:
        raise ValueError("Need at least 2 coordinates for CCR surrogate.")
    x = dx[:, :mid]
    p = dx[:, mid : mid + mid]
    if p.shape[1] != x.shape[1]:
        m = min(x.shape[1], p.shape[1])
        x = x[:, :m]
        p = p[:, :m]
    omega = (x * p).sum(axis=1)
    return pd.DataFrame(
        {
            "omega_mean": [float(np.mean(omega))],
            "omega_std": [float(np.std(omega))],
            "omega_abs_mean": [float(np.mean(np.abs(omega)))],
        }
    )


def default_output_prefix(csv_path: Path) -> Path:
    safe_name = csv_path.as_posix().replace("/", "_").replace("..", "_")
    return Path("scripts/data") / safe_name


def main() -> None:
    args = parse_args()
    csv_path = Path(args.csv)
    output_prefix = Path(args.output_prefix) if args.output_prefix else default_output_prefix(csv_path)

    x, a, cols = load_embedding_csv(csv_path, args.feature_cols, args.arrow_col)
    x = robust_scale_rows(x)
    shape_dx, da = delta_view(x, a)
    hecke_feats = delta_hecke_scan(shape_dx)
    fwd = forward_mask(da, args.eps_arrow, args.strict_forward)
    results = search_signatures(
        shape_dx,
        da,
        hecke_feats,
        eps_cone=args.eps_cone,
        eps_arrow=args.eps_arrow,
        require_nondegenerate=args.require_nondegenerate,
        require_indefinite=args.require_indefinite,
        strict_forward=args.strict_forward,
    )

    top = summarize_top(results, top_k=args.top_k)
    top_path = output_prefix.parent / f"{output_prefix.name}_delta_signature_rank.csv"
    top.to_csv(top_path, index=False)

    ccr_df = ccr_surrogate(shape_dx)
    ccr_path = output_prefix.parent / f"{output_prefix.name}_delta_ccr_surrogate.csv"
    ccr_df.to_csv(ccr_path, index=False)

    cov = np.cov(x.T)
    eigvals, eigvecs = np.linalg.eigh(cov)
    nondegenerate_best = next((r for r in results if r.mask.nondegenerate), None)

    payload = {
        "csv": str(csv_path),
        "feature_cols": cols,
        "arrow_col": args.arrow_col,
        "rows": int(len(x)),
        "strict_forward": args.strict_forward,
        "require_indefinite": args.require_indefinite,
        "forward_fraction": float(fwd.mean()),
        "strict_forward_count": int(fwd.sum()),
        "total_step_count": int(len(da)),
        "eigenvalues": eigvals.tolist(),
        "top_eigenvectors": eigvecs[:, -min(3, eigvecs.shape[1]) :].tolist(),
        "top_results": top.to_dict(orient="records"),
        "best_nondegenerate": None
        if nondegenerate_best is None
        else {
            **asdict(nondegenerate_best),
            "mask": nondegenerate_best.mask.label(),
            "p": nondegenerate_best.mask.p,
            "q": nondegenerate_best.mask.q,
            "z": nondegenerate_best.mask.z,
            "lorentz_like": nondegenerate_best.mask.lorentz_like,
        },
        "output_rank_csv": str(top_path),
        "output_ccr_csv": str(ccr_path),
    }

    if args.json:
        print(json.dumps(payload, indent=2))
        return

    print("Feature cols:", cols)
    print(
        f"Arrow-separated mode: arrow_col={args.arrow_col} "
        f"strict_forward={args.strict_forward} "
        f"strict_forward_count={int(fwd.sum())}/{len(da)}"
    )
    print(top.to_string(index=False))
    if nondegenerate_best is not None:
        print("\nBest nondegenerate mask:")
        print(
            f"  mask={nondegenerate_best.mask.label()} "
            f"(p={nondegenerate_best.mask.p}, q={nondegenerate_best.mask.q}, z={nondegenerate_best.mask.z}, "
            f"lorentz_like={nondegenerate_best.mask.lorentz_like}) "
            f"cone_frac_forward={nondegenerate_best.cone_frac_forward:.6f}"
        )
    print("\nCCR surrogate:")
    print(ccr_df.to_string(index=False))
    print(f"\nWrote: {top_path}")
    print(f"Wrote: {ccr_path}")


if __name__ == "__main__":
    main()
