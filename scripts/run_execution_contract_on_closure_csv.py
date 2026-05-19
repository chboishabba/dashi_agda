#!/usr/bin/env python3
"""Run the projected-delta execution contract on closure_embedding_per_step.csv."""

from __future__ import annotations

import argparse
from pathlib import Path
from typing import Sequence

import numpy as np
import pandas as pd

from execution_contract import (
    AcceptanceThresholds,
    DEFAULT_FEATURE_COLS,
    DeltaConeEnforcer,
    earth_spoke_hub_eigen,
    mdl_l1,
)


def build_series(
    df: pd.DataFrame,
    *,
    label_col: str,
    step_col: str,
    state_cols: Sequence[str],
) -> dict[str, np.ndarray]:
    series: dict[str, np.ndarray] = {}
    for label, group in df.groupby(label_col, sort=False):
        ordered = group.sort_values(step_col)
        series[str(label)] = ordered[list(state_cols)].to_numpy(dtype=float)
    return series


def write_receipts(
    out_path: Path,
    *,
    series: dict[str, np.ndarray],
    enforcer: DeltaConeEnforcer,
) -> pd.DataFrame:
    rows: list[dict[str, object]] = []

    for label, states in series.items():
        if len(states) < 2:
            continue
        for step_idx in range(len(states) - 1):
            decision = enforcer.evaluate_step(states[step_idx], states[step_idx + 1])
            metrics = decision.metrics
            rows.append(
                {
                    "label": label,
                    "step_from": step_idx,
                    "step_to": step_idx + 1,
                    "accepted": int(decision.accepted),
                    "reasons": "|".join(decision.reasons),
                    "arrow_ok": int(metrics.arrow_ok),
                    "cone_ok": int(metrics.cone_ok),
                    "basin_ok": int(metrics.basin_ok),
                    "mdl_ok": int(metrics.mdl_ok),
                    "eigen_overlap": metrics.eigen_overlap,
                    "q_delta": metrics.q_delta,
                    "mdl_prev": metrics.mdl_prev,
                    "mdl_next": metrics.mdl_next,
                }
            )

    out_df = pd.DataFrame(rows)
    out_df.to_csv(out_path, index=False)
    return out_df


def summarize_receipts(out_df: pd.DataFrame) -> dict[str, object]:
    if out_df.empty:
        return {
            "rows": 0,
            "acceptance_rate": None,
            "accepted_steps": 0,
            "violation_counts": {},
        }

    rejected = out_df.loc[out_df["accepted"] == 0, "reasons"]
    violation_counts = rejected.value_counts().to_dict()
    return {
        "rows": int(len(out_df)),
        "acceptance_rate": float(out_df["accepted"].mean()),
        "accepted_steps": int(out_df["accepted"].sum()),
        "violation_counts": violation_counts,
    }


def make_enforcer(
    *,
    x_cols: Sequence[str],
    mask: Sequence[float],
    eps_arrow: float,
    eps_cone: float,
    min_eigen_overlap: float,
    basin_radius: float,
) -> DeltaConeEnforcer:
    if len(mask) != len(x_cols):
        raise ValueError(
            f"Mask length {len(mask)} does not match feature count {len(x_cols)}"
        )

    def projection(x: np.ndarray) -> np.ndarray:
        return x[:-1]

    def arrow_fn(x: np.ndarray) -> float:
        return float(x[-1])

    center = np.zeros(len(x_cols), dtype=float)

    def basin_pred(x: np.ndarray) -> bool:
        return float(np.linalg.norm(np.asarray(x, dtype=float) - center)) <= basin_radius

    def mdl_on_state(x: np.ndarray) -> float:
        return mdl_l1(x[:-1])

    def eigen_on_state(x: np.ndarray) -> dict[str, float]:
        return earth_spoke_hub_eigen(x[:-1])

    return DeltaConeEnforcer(
        mask=mask,
        projection=projection,
        mdl_fn=mdl_on_state,
        arrow_fn=arrow_fn,
        basin_pred=basin_pred,
        eigen_fn=eigen_on_state,
        thresholds=AcceptanceThresholds(
            eps_arrow=eps_arrow,
            eps_cone=eps_cone,
            min_eigen_overlap=min_eigen_overlap,
        ),
    )


def evaluate_closure_csv(
    embedding: Path,
    *,
    label_col: str,
    step_col: str,
    arrow_col: str,
    x_cols: Sequence[str],
    mask: Sequence[float],
    eps_arrow: float,
    eps_cone: float,
    min_eigen_overlap: float,
    basin_radius: float,
    out_path: Path,
) -> tuple[pd.DataFrame, dict[str, object]]:
    df = pd.read_csv(embedding)
    state_cols = [*x_cols, arrow_col]
    needed = [label_col, step_col, *state_cols]
    missing = [col for col in needed if col not in df.columns]
    if missing:
        raise ValueError(f"Missing required columns: {missing}")

    series = build_series(
        df,
        label_col=label_col,
        step_col=step_col,
        state_cols=state_cols,
    )
    enforcer = make_enforcer(
        x_cols=x_cols,
        mask=mask,
        eps_arrow=eps_arrow,
        eps_cone=eps_cone,
        min_eigen_overlap=min_eigen_overlap,
        basin_radius=basin_radius,
    )
    out_df = write_receipts(out_path, series=series, enforcer=enforcer)
    return out_df, summarize_receipts(out_df)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--embedding", required=True)
    parser.add_argument("--label-col", default="label")
    parser.add_argument("--step-col", default="step")
    parser.add_argument("--arrow-col", default="v_arrow")
    parser.add_argument("--x-cols", nargs="+", default=DEFAULT_FEATURE_COLS)
    parser.add_argument("--mask", nargs="+", type=float, required=True)
    parser.add_argument("--eps-arrow", type=float, default=1e-9)
    parser.add_argument("--eps-cone", type=float, default=1e-9)
    parser.add_argument("--min-eigen-overlap", type=float, default=0.80)
    parser.add_argument("--basin-radius", type=float, default=10.0)
    parser.add_argument("--out", default="execution_contract_receipts.csv")
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    out_df, summary = evaluate_closure_csv(
        Path(args.embedding),
        label_col=args.label_col,
        step_col=args.step_col,
        arrow_col=args.arrow_col,
        x_cols=args.x_cols,
        mask=args.mask,
        eps_arrow=args.eps_arrow,
        eps_cone=args.eps_cone,
        min_eigen_overlap=args.min_eigen_overlap,
        basin_radius=args.basin_radius,
        out_path=Path(args.out),
    )
    if out_df.empty:
        print("[warn] no step receipts written")
        return

    print(f"[ok] wrote: {args.out}")
    print(f"[info] rows: {summary['rows']}")
    print(f"[info] acceptance rate: {summary['acceptance_rate']:.4f}")
    print("[info] violation counts:")
    print(pd.Series(summary["violation_counts"]).head(10))


if __name__ == "__main__":
    main()
