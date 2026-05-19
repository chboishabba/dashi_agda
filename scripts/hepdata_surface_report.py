#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

import numpy as np

try:
    from hepdata_consumer import (
        build_summary,
        load_hepdata_artifact,
        to_measurement_surface,
    )
except ModuleNotFoundError:
    from scripts.hepdata_consumer import (
        build_summary,
        load_hepdata_artifact,
        to_measurement_surface,
    )


def build_surface_report(artifact: dict[str, Any], *, family: str | None = None) -> dict[str, Any]:
    surface = to_measurement_surface(artifact, family=family)
    summary = build_summary(artifact, surface, family=family)

    x = np.asarray(surface.x, dtype=float)
    y = np.asarray(surface.y, dtype=float)
    cov = np.asarray(surface.cov, dtype=float)
    diag = np.diag(cov) if cov.size else np.asarray([], dtype=float)
    rank = int(np.linalg.matrix_rank(cov)) if cov.size else 0
    cond = float(np.linalg.cond(cov)) if cov.size else None
    symmetric = bool(np.allclose(cov, cov.T)) if cov.size else True

    issues: list[str] = []
    if not symmetric:
        issues.append("covariance-not-symmetric")
    if rank != int(x.shape[0]):
        issues.append("covariance-rank-deficient")
    if cond is not None and not np.isfinite(cond):
        issues.append("covariance-condition-infinite")

    surface_validation = "ok" if not issues else "metric-degraded"

    report = {
        "trace_id": surface.trace_id,
        "point_count": int(x.shape[0]),
        "x_range": [float(np.min(x)), float(np.max(x))] if x.size else None,
        "y_range": [float(np.min(y)), float(np.max(y))] if y.size else None,
        "covariance_shape": [int(cov.shape[0]), int(cov.shape[1])] if cov.ndim == 2 else None,
        "covariance_rank": rank,
        "covariance_condition_number": cond,
        "covariance_diagonal_range": (
            [float(np.min(diag)), float(np.max(diag))] if diag.size else None
        ),
        "covariance_symmetric": symmetric,
        "metric_ready": not issues,
        "projection_eligible": not issues,
        "surface_validation": surface_validation,
        "issues": issues,
        "measurement_summary": summary,
    }
    return report


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Produce a report-only health summary for one validated HEPData "
            "measurement surface."
        )
    )
    parser.add_argument("artifact", help="Path to canonical artifact JSON")
    parser.add_argument("--family", help="Family name when the artifact contains multiple families")
    parser.add_argument("--output", help="Optional output path. Defaults to stdout.")
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    artifact = load_hepdata_artifact(Path(args.artifact))
    report = build_surface_report(artifact, family=args.family)
    text = json.dumps(report, indent=2, sort_keys=True) + "\n"
    if args.output:
        Path(args.output).write_text(text, encoding="utf-8")
    else:
        print(text, end="")


if __name__ == "__main__":
    main()
