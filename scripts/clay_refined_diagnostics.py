#!/usr/bin/env python3
"""Compute refined Clay-sprint diagnostics from local CSV artifacts.

The outputs are empirical/non-promoting diagnostics.  They do not prove
PAWOTG, Yang-Mills, Navier-Stokes, Gate 3, or Clay claims.
"""

from __future__ import annotations

import argparse
import csv
import math
from pathlib import Path


DEFAULT_ARTIFACT_DIR = Path("Docs/Images/clay-analytic-sprint")


def read_csv(path: Path) -> list[dict[str, str]]:
    with path.open(newline="") as handle:
        return list(csv.DictReader(handle))


def write_csv(path: Path, fieldnames: list[str], rows: list[dict[str, object]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=fieldnames)
        writer.writeheader()
        for row in rows:
            writer.writerow(row)


def fmt(value: float) -> str:
    if math.isinf(value):
        return "inf"
    if math.isnan(value):
        return "nan"
    return f"{value:.10g}"


def compute_ns_tail_restricted(artifact_dir: Path) -> None:
    rows = read_csv(artifact_dir / "ns_theta_full_sweep.csv")
    grouped: dict[tuple[str, str], list[dict[str, str]]] = {}
    for row in rows:
        grouped.setdefault((row["trace"], row["nu"]), []).append(row)

    out_rows: list[dict[str, object]] = []
    for (trace, nu), group in sorted(grouped.items()):
        k_diss = math.ceil(float(group[0]["K_kolmogorov"]))
        global_row = max(group, key=lambda row: float(row["theta_k"]))
        tail_rows = [row for row in group if int(row["k"]) >= k_diss]
        tail_row = max(tail_rows, key=lambda row: float(row["theta_k"])) if tail_rows else None

        theta_global = float(global_row["theta_k"])
        if tail_row is None:
            theta_tail = math.nan
            danger_tail = ""
            margin_tail = math.nan
            tail_rows_count = 0
        else:
            theta_tail = float(tail_row["theta_k"])
            danger_tail = tail_row["k"]
            margin_tail = 1.0 - theta_tail
            tail_rows_count = len(tail_rows)

        out_rows.append(
            {
                "trace": trace,
                "nu": nu,
                "K_kolmogorov": group[0]["K_kolmogorov"],
                "K_diss": k_diss,
                "theta_global": fmt(theta_global),
                "danger_shell_global": global_row["k"],
                "global_margin": fmt(1.0 - theta_global),
                "theta_tail": fmt(theta_tail),
                "danger_shell_tail": danger_tail,
                "tail_margin": fmt(margin_tail),
                "tail_rows": tail_rows_count,
                "low_shell_warning": str(int(global_row["k"]) < k_diss),
                "tail_barrier_pass": str(theta_tail < 1.0 if tail_row is not None else False),
                "promotion_status": "NO_PROMOTION",
            }
        )

    write_csv(
        artifact_dir / "ns_theta_tail_restricted.csv",
        [
            "trace",
            "nu",
            "K_kolmogorov",
            "K_diss",
            "theta_global",
            "danger_shell_global",
            "global_margin",
            "theta_tail",
            "danger_shell_tail",
            "tail_margin",
            "tail_rows",
            "low_shell_warning",
            "tail_barrier_pass",
            "promotion_status",
        ],
        out_rows,
    )


def compute_ym_c0_sensitivity(artifact_dir: Path) -> None:
    rows = read_csv(artifact_dir / "ym_p7_polymer_kp.csv")
    p = float(rows[0]["p"])
    a = float(rows[0]["a"])
    c_min = float(rows[0]["c_min"])
    beta_physical = 6.0
    c0_values = [0.5, 0.75, 1.0, 1.25, 1.5, 2.0, 3.0, 5.0, 10.0]
    r_targets = [1.0, 0.5, 0.25, 0.1, 0.01]

    out_rows: list[dict[str, object]] = []
    for c0 in c0_values:
        for target in r_targets:
            beta_required = (a + math.log(p * c0 / target)) / c_min
            out_rows.append(
                {
                    "C0": fmt(c0),
                    "r_target": fmt(target),
                    "kp_sum_at_target": fmt(target / (1.0 - target)) if target < 1.0 else "inf",
                    "beta_required": fmt(beta_required),
                    "gap_from_beta6": fmt(beta_required - beta_physical),
                    "p": fmt(p),
                    "a": fmt(a),
                    "c_min": fmt(c_min),
                    "promotion_status": "NO_PROMOTION",
                }
            )

    write_csv(
        artifact_dir / "ym_c0_threshold_sensitivity.csv",
        [
            "C0",
            "r_target",
            "kp_sum_at_target",
            "beta_required",
            "gap_from_beta6",
            "p",
            "a",
            "c_min",
            "promotion_status",
        ],
        out_rows,
    )


def compute_gate3_sampler_quality(artifact_dir: Path) -> None:
    rows = read_csv(artifact_dir / "gate3_frame_extended.csv")
    out_rows: list[dict[str, object]] = []
    for row in rows:
        n = int(row["N"])
        mu = float(row["mu_N"])
        n_minus_1_mu = float(row["N_minus_1_times_mu"])
        target_mu = 1.0 / max(n - 1, 1)
        out_rows.append(
            {
                "sigma": row["sigma"],
                "N": n,
                "dict_type": row["dict_type"],
                "mu_N": row["mu_N"],
                "target_mu_strict_1_over_N_minus_1": fmt(target_mu),
                "mu_over_target": fmt(mu / target_mu),
                "N_minus_1_times_mu": row["N_minus_1_times_mu"],
                "gershgorin_lower": row["gershgorin_lower"],
                "A_N": row["A_N"],
                "condition_number_proxy": row["frame_ratio"],
                "sampler_quality": "FAIL_CLUSTERED" if n_minus_1_mu >= 1.0 else "PASS_GERSHGORIN",
                "promotion_status": "NO_PROMOTION",
            }
        )

    write_csv(
        artifact_dir / "gate3_sampler_quality.csv",
        [
            "sigma",
            "N",
            "dict_type",
            "mu_N",
            "target_mu_strict_1_over_N_minus_1",
            "mu_over_target",
            "N_minus_1_times_mu",
            "gershgorin_lower",
            "A_N",
            "condition_number_proxy",
            "sampler_quality",
            "promotion_status",
        ],
        out_rows,
    )


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--artifact-dir",
        type=Path,
        default=DEFAULT_ARTIFACT_DIR,
        help="Directory containing clay analytic sprint CSV artifacts.",
    )
    args = parser.parse_args()

    compute_ns_tail_restricted(args.artifact_dir)
    compute_ym_c0_sensitivity(args.artifact_dir)
    compute_gate3_sampler_quality(args.artifact_dir)

    print(f"wrote {args.artifact_dir / 'ns_theta_tail_restricted.csv'}")
    print(f"wrote {args.artifact_dir / 'ym_c0_threshold_sensitivity.csv'}")
    print(f"wrote {args.artifact_dir / 'gate3_sampler_quality.csv'}")


if __name__ == "__main__":
    main()
