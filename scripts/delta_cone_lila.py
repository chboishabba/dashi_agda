#!/usr/bin/env python3
"""Analyze LILA training logs as DASHI-style delta-cone dynamics."""

from __future__ import annotations

import argparse
import itertools
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, Sequence

import numpy as np
import pandas as pd


@dataclass(frozen=True)
class Signature:
    p: int
    q: int
    z: int
    signs: tuple[int, ...]

    @property
    def mask(self) -> str:
        return ",".join(str(s) for s in self.signs)


def robust_scale_frame(df: pd.DataFrame, cols: Sequence[str]) -> pd.DataFrame:
    out = df.copy()
    for col in cols:
        values = out[col].astype(float).to_numpy()
        median = float(np.median(values))
        mad = float(np.median(np.abs(values - median))) + 1e-12
        z = (values - median) / (1.4826 * mad)
        out[col] = np.tanh(z)
    return out


def trit(values: np.ndarray, eps: float) -> np.ndarray:
    out = np.zeros_like(values, dtype=int)
    out[values > eps] = 1
    out[values < -eps] = -1
    return out


def all_signatures(d: int, allow_zero: bool = True) -> Iterable[Signature]:
    vals = (-1, 0, 1) if allow_zero else (-1, 1)
    for signs in itertools.product(vals, repeat=d):
        p = sum(1 for s in signs if s == 1)
        q = sum(1 for s in signs if s == -1)
        z = sum(1 for s in signs if s == 0)
        if p == 0 and q == 0:
            continue
        yield Signature(p=p, q=q, z=z, signs=tuple(signs))


def quadratic_delta(dx: np.ndarray, signs: Sequence[int]) -> np.ndarray:
    signed = np.asarray(signs, dtype=float)
    return ((dx ** 2) * signed[None, :]).sum(axis=1)


def forward_mask(arrow_delta: np.ndarray, *, eps_arrow: float, arrow_mode: str) -> np.ndarray:
    if arrow_mode == "decreasing":
        return arrow_delta <= eps_arrow
    if arrow_mode == "increasing":
        return arrow_delta >= -eps_arrow
    raise ValueError(f"Unsupported arrow mode: {arrow_mode}")


def score_signature(
    dx: np.ndarray,
    arrow_delta: np.ndarray,
    signs: Sequence[int],
    *,
    eps_cone: float,
    eps_arrow: float,
    arrow_mode: str,
) -> dict[str, float]:
    qd = quadratic_delta(dx, signs)
    cone_ok = qd <= eps_cone
    forward = forward_mask(arrow_delta, eps_arrow=eps_arrow, arrow_mode=arrow_mode)
    both = cone_ok & forward

    out: dict[str, float] = {
        "cone_frac": float(cone_ok.mean()) if len(cone_ok) else float("nan"),
        "forward_frac": float(forward.mean()) if len(forward) else float("nan"),
        "forward_cone_frac_all": float(both.mean()) if len(both) else float("nan"),
        "n_steps": int(len(qd)),
        "n_forward": int(forward.sum()),
        "n_cone": int(cone_ok.sum()),
        "max_Qd": float(np.max(qd)) if len(qd) else float("nan"),
        "min_Qd": float(np.min(qd)) if len(qd) else float("nan"),
        "mean_Qd": float(np.mean(qd)) if len(qd) else float("nan"),
    }
    out["forward_cone_frac_conditional"] = (
        float(cone_ok[forward].mean()) if int(forward.sum()) > 0 else float("nan")
    )
    return out


def basin_stats(df: pd.DataFrame, basin_col: str) -> dict[str, object]:
    basins = df[basin_col].astype(str).tolist()
    if len(basins) < 2:
        return {"basin_dwell_mean": float("nan"), "basin_switches": 0, "basin_counts": {}}

    counts: dict[str, int] = {}
    dwells: list[int] = []
    current = basins[0]
    run = 1
    counts[current] = counts.get(current, 0) + 1
    switches = 0

    for basin in basins[1:]:
        counts[basin] = counts.get(basin, 0) + 1
        if basin == current:
            run += 1
        else:
            dwells.append(run)
            switches += 1
            current = basin
            run = 1
    dwells.append(run)

    return {
        "basin_dwell_mean": float(np.mean(dwells)),
        "basin_switches": int(switches),
        "basin_counts": counts,
    }


def parse_args() -> argparse.Namespace:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--csv", required=True, help="Training log CSV")
    ap.add_argument("--features", required=True, help="Comma-separated feature columns")
    ap.add_argument("--arrow", required=True, help="Arrow column to test for monotonicity")
    ap.add_argument("--step", default="step", help="Step column")
    ap.add_argument("--basin-col", default=None, help="Optional basin column")
    ap.add_argument("--eps", type=float, default=0.15, help="Cone threshold")
    ap.add_argument("--eps-arrow", type=float, default=1e-9, help="Arrow tolerance")
    ap.add_argument(
        "--arrow-mode",
        choices=("decreasing", "increasing"),
        default="decreasing",
        help="Direction considered forward for the arrow coordinate",
    )
    ap.add_argument("--allow-zero", action="store_true", help="Allow degenerate masks")
    ap.add_argument("--require-nondegenerate", action="store_true", help="Require z = 0")
    ap.add_argument("--out", default="delta_cone_rank.csv", help="Ranking CSV path")
    ap.add_argument(
        "--step-out",
        default=None,
        help="Optional per-step CSV path with the chosen best signature applied",
    )
    return ap.parse_args()


def main() -> int:
    args = parse_args()
    df = pd.read_csv(args.csv).sort_values(args.step).reset_index(drop=True)

    features = [c.strip() for c in args.features.split(",") if c.strip()]
    if args.arrow not in features:
        raise ValueError(f"--arrow {args.arrow!r} must be one of --features")

    missing = [c for c in [args.step, *features] if c not in df.columns]
    if missing:
        raise ValueError(f"Missing columns: {missing}")

    sdf = robust_scale_frame(df, features)
    q_cols = [c for c in features if c != args.arrow]
    if not q_cols:
        raise ValueError("Need at least one non-arrow feature for the quadratic")

    x = sdf[q_cols].to_numpy(dtype=float)
    arrow = sdf[args.arrow].to_numpy(dtype=float)
    dx = x[1:] - x[:-1]
    darrow = arrow[1:] - arrow[:-1]
    _ = trit(darrow, args.eps_arrow)

    rows: list[dict[str, object]] = []
    for sig in all_signatures(len(q_cols), allow_zero=args.allow_zero):
        if args.require_nondegenerate and sig.z != 0:
            continue
        score = score_signature(
            dx,
            darrow,
            sig.signs,
            eps_cone=args.eps,
            eps_arrow=args.eps_arrow,
            arrow_mode=args.arrow_mode,
        )
        rows.append({"p": sig.p, "q": sig.q, "z": sig.z, "mask": sig.mask, **score})

    rank = pd.DataFrame(rows)
    if rank.empty:
        raise ValueError("No signatures matched the requested filters")

    rank = rank.sort_values(
        by=[
            "forward_cone_frac_conditional",
            "forward_frac",
            "cone_frac",
            "z",
            "mean_Qd",
        ],
        ascending=[False, False, False, True, True],
    ).reset_index(drop=True)
    rank.to_csv(args.out, index=False)

    print(f"[ok] wrote: {args.out}")
    print(f"[info] q cols used: {q_cols}")
    print(f"[info] arrow col: {args.arrow}")
    print(f"[info] arrow mode: {args.arrow_mode}")
    print("[note] Arrow is kept out of Q and only used as a monotonicity filter.")
    print("\n=== Best delta-cone signature ===")
    print(rank.iloc[0].to_string())

    if args.step_out:
        best = rank.iloc[0]
        qd = quadratic_delta(dx, tuple(int(s) for s in best["mask"].split(",")))
        fwd = forward_mask(darrow, eps_arrow=args.eps_arrow, arrow_mode=args.arrow_mode)
        step_df = pd.DataFrame(
            {
                "step_from": df[args.step].iloc[:-1].to_numpy(),
                "step_to": df[args.step].iloc[1:].to_numpy(),
                "arrow_delta": darrow,
                "cone_Qd": qd,
                "forward": fwd.astype(int),
                "cone_ok": (qd <= args.eps).astype(int),
                "forward_cone_ok": ((qd <= args.eps) & fwd).astype(int),
            }
        )
        step_df.to_csv(args.step_out, index=False)
        print(f"[ok] wrote: {args.step_out}")

    if args.basin_col and args.basin_col in df.columns:
        print("\n=== Basin stats ===")
        print(basin_stats(df, args.basin_col))

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
