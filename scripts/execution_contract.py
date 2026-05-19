#!/usr/bin/env python3
"""Projected-delta execution-contract enforcement for embedding traces."""

from __future__ import annotations

import argparse
import json
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Callable, Iterable, Mapping, Sequence

import numpy as np
import pandas as pd

ARROW_COL = "v_arrow"
DEFAULT_FEATURE_COLS = ["v_pnorm", "v_dnorm", "v_depth"]


Vector = np.ndarray
EigenMass = Mapping[str, float]


@dataclass(frozen=True)
class StepMetrics:
    arrow_ok: bool
    cone_ok: bool
    basin_ok: bool
    mdl_ok: bool
    eigen_overlap: float
    q_delta: float
    mdl_prev: float
    mdl_next: float


@dataclass(frozen=True)
class AcceptanceThresholds:
    eps_arrow: float = 1e-9
    eps_cone: float = 1e-9
    min_eigen_overlap: float = 0.80


@dataclass(frozen=True)
class ExecutionDecision:
    accepted: bool
    metrics: StepMetrics
    reasons: tuple[str, ...]


def q_masked(x: Vector, mask: Vector) -> float:
    return float(np.sum(mask * np.square(x)))


def normalized_overlap(lhs: EigenMass, rhs: EigenMass) -> float:
    keys = sorted(set(lhs) | set(rhs))
    mins = 0.0
    maxs = 0.0
    for key in keys:
        a = float(lhs.get(key, 0.0))
        b = float(rhs.get(key, 0.0))
        mins += min(a, b)
        maxs += max(a, b)
    if maxs <= 0.0:
        return 1.0
    return mins / maxs


class DeltaConeEnforcer:
    """Execution contract:

    1. arrow monotone
    2. projected delta-cone compatibility
    3. projected basin preservation
    4. MDL non-increase
    5. eigen-overlap floor
    """

    def __init__(
        self,
        *,
        mask: Sequence[float],
        projection: Callable[[Vector], Vector],
        mdl_fn: Callable[[Vector], float],
        arrow_fn: Callable[[Vector], float],
        basin_pred: Callable[[Vector], bool],
        eigen_fn: Callable[[Vector], EigenMass],
        thresholds: AcceptanceThresholds | None = None,
    ) -> None:
        self.mask = np.asarray(mask, dtype=float)
        self.projection = projection
        self.mdl_fn = mdl_fn
        self.arrow_fn = arrow_fn
        self.basin_pred = basin_pred
        self.eigen_fn = eigen_fn
        self.thresholds = thresholds or AcceptanceThresholds()

    def evaluate_step(self, x_prev: Vector, x_next: Vector) -> ExecutionDecision:
        x_prev = np.asarray(x_prev, dtype=float)
        x_next = np.asarray(x_next, dtype=float)

        dx = x_next - x_prev
        p_prev = self.projection(x_prev)
        p_next = self.projection(x_next)
        p_dx = self.projection(dx)

        arrow_prev = float(self.arrow_fn(x_prev))
        arrow_next = float(self.arrow_fn(x_next))
        arrow_ok = arrow_next >= arrow_prev - self.thresholds.eps_arrow

        q_delta = q_masked(p_dx, self.mask)
        cone_ok = q_delta <= self.thresholds.eps_cone

        basin_ok = self.basin_pred(p_prev) and self.basin_pred(p_next)

        mdl_prev = float(self.mdl_fn(x_prev))
        mdl_next = float(self.mdl_fn(x_next))
        mdl_ok = mdl_next <= mdl_prev + self.thresholds.eps_arrow

        eig_prev = self.eigen_fn(p_prev)
        eig_next = self.eigen_fn(p_next)
        eigen_overlap = normalized_overlap(eig_prev, eig_next)
        eigen_ok = eigen_overlap >= self.thresholds.min_eigen_overlap

        reasons: list[str] = []
        if not arrow_ok:
            reasons.append("arrow")
        if not cone_ok:
            reasons.append("cone")
        if not basin_ok:
            reasons.append("basin")
        if not mdl_ok:
            reasons.append("mdl")
        if not eigen_ok:
            reasons.append("eigen")

        return ExecutionDecision(
            accepted=(len(reasons) == 0),
            metrics=StepMetrics(
                arrow_ok=arrow_ok,
                cone_ok=cone_ok,
                basin_ok=basin_ok,
                mdl_ok=mdl_ok,
                eigen_overlap=eigen_overlap,
                q_delta=q_delta,
                mdl_prev=mdl_prev,
                mdl_next=mdl_next,
            ),
            reasons=tuple(reasons),
        )


def identity_projection(x: Vector) -> Vector:
    return x


def basin_from_l2_radius(center: Sequence[float], radius: float) -> Callable[[Vector], bool]:
    center_vec = np.asarray(center, dtype=float)

    def pred(x: Vector) -> bool:
        return float(np.linalg.norm(np.asarray(x, dtype=float) - center_vec)) <= radius

    return pred


def earth_spoke_hub_eigen(x: Vector) -> dict[str, float]:
    x = np.asarray(x, dtype=float)
    if x.size < 3:
        return {"Earth": float(np.linalg.norm(x)), "Spoke": 0.0, "Hub": 0.0}

    thirds = np.array_split(np.abs(x), 3)
    return {
        "Earth": float(np.sum(thirds[0])),
        "Spoke": float(np.sum(thirds[1])),
        "Hub": float(np.sum(thirds[2])),
    }


def mdl_l1(x: Vector) -> float:
    return float(np.sum(np.abs(np.asarray(x, dtype=float))))


def load_embedding_csv(
    path: Path,
    feature_cols: Sequence[str],
    arrow_col: str,
) -> tuple[np.ndarray, np.ndarray, list[str]]:
    df = pd.read_csv(path)
    cols = [col for col in feature_cols if col in df.columns]
    required = list(cols) + [arrow_col]
    missing = [col for col in required if col not in df.columns]
    if missing:
        raise ValueError(f"Missing columns: {missing}")
    return df[cols].to_numpy(dtype=float), df[arrow_col].to_numpy(dtype=float), cols


def run_trace_contract(
    x: np.ndarray,
    a: np.ndarray,
    *,
    enforcer: DeltaConeEnforcer,
) -> dict[str, object]:
    if x.ndim != 2 or a.ndim != 1 or len(x) != len(a):
        raise ValueError("Expected features with shape [T, d] and arrow vector [T]")

    augmented = np.concatenate([x, a.reshape(-1, 1)], axis=1)
    decisions: list[ExecutionDecision] = []
    for idx in range(len(augmented) - 1):
        decisions.append(enforcer.evaluate_step(augmented[idx], augmented[idx + 1]))

    violations = {
        "arrow": sum("arrow" in d.reasons for d in decisions),
        "cone": sum("cone" in d.reasons for d in decisions),
        "basin": sum("basin" in d.reasons for d in decisions),
        "mdl": sum("mdl" in d.reasons for d in decisions),
        "eigen": sum("eigen" in d.reasons for d in decisions),
    }

    return {
        "accepted_steps": sum(d.accepted for d in decisions),
        "total_steps": len(decisions),
        "violations": violations,
        "decisions": [
            {
                "accepted": d.accepted,
                "reasons": list(d.reasons),
                "metrics": asdict(d.metrics),
            }
            for d in decisions
        ],
    }


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--csv", required=True, help="Input closure_embedding_per_step.csv")
    parser.add_argument("--arrow-col", default=ARROW_COL)
    parser.add_argument("--feature-cols", nargs="+", default=DEFAULT_FEATURE_COLS)
    parser.add_argument(
        "--mask",
        nargs="+",
        type=float,
        default=[1.0, 1.0, -1.0],
        help="Quadratic mask for projected deltas",
    )
    parser.add_argument("--eps-arrow", type=float, default=1e-9)
    parser.add_argument("--eps-cone", type=float, default=1e-9)
    parser.add_argument("--min-eigen-overlap", type=float, default=0.80)
    parser.add_argument("--basin-radius", type=float, default=10.0)
    parser.add_argument("--json", action="store_true", help="Emit JSON")
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    csv_path = Path(args.csv)
    x, a, cols = load_embedding_csv(csv_path, args.feature_cols, args.arrow_col)
    if len(args.mask) != len(cols):
        raise ValueError(
            f"Mask length {len(args.mask)} does not match feature count {len(cols)}"
        )

    def projection(v: Vector) -> Vector:
        return v[: len(cols)]

    def arrow_fn(v: Vector) -> float:
        return float(v[-1])

    enforcer = DeltaConeEnforcer(
        mask=args.mask,
        projection=projection,
        mdl_fn=lambda v: mdl_l1(projection(v)),
        arrow_fn=arrow_fn,
        basin_pred=basin_from_l2_radius(np.zeros(len(cols)), args.basin_radius),
        eigen_fn=lambda v: earth_spoke_hub_eigen(projection(v)),
        thresholds=AcceptanceThresholds(
            eps_arrow=args.eps_arrow,
            eps_cone=args.eps_cone,
            min_eigen_overlap=args.min_eigen_overlap,
        ),
    )
    summary = run_trace_contract(x, a, enforcer=enforcer)
    summary["feature_cols"] = cols
    summary["arrow_col"] = args.arrow_col
    summary["mask"] = list(args.mask)

    if args.json:
        print(json.dumps(summary, indent=2))
    else:
        print(f"accepted_steps={summary['accepted_steps']}")
        print(f"total_steps={summary['total_steps']}")
        print("violations=", json.dumps(summary["violations"], sort_keys=True))


if __name__ == "__main__":
    main()
