#!/usr/bin/env python3
"""Sprint 149 deterministic linearization/spectrum probe.

This stdlib-only artifact probes a transparent finite-difference toy
linearization around a Hou-Luo-like concentration profile.  It scans fixed beta
candidates and records spectral drift and stability indicators for the
ScalingConsistencyForHouLuoConcentration gate.

The operator and spectrum are evidence only.  They are not a PDE
linearization proof, not a self-similar profile proof, not a scaling-consistency
proof, and not a Clay Navier-Stokes promotion.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
import math
import os
import shutil
import sys
import tempfile
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any


CONTRACT = "ns_sprint149_linearization_spectrum_probe"
OUT_DIR_DEFAULT = Path("outputs/ns_sprint149_linearization_spectrum_probe")
SUMMARY_NAME = CONTRACT + "_summary.json"
ROWS_JSON_NAME = CONTRACT + "_rows.json"
ROWS_CSV_NAME = CONTRACT + "_rows.csv"
REPORT_NAME = CONTRACT + ".md"
MANIFEST_NAME = CONTRACT + "_manifest.json"

SPRINT = 149
LANE = 3
PROGRAM = "HouLuoAxisymmetricWithSwirlBarrierProgram"
TARGET_GATE = "ScalingConsistencyForHouLuoConcentration"
MODEL_KIND = "deterministic_transparent_finite_difference_toy_linearization"
DECISION = "evidence_only_linearization_spectrum_probe_no_proof"
PROMOTION_DECISION = "hold_no_clay_promotion"

GRID_N = 49
DOMAIN_LEFT = -1.0
DOMAIN_RIGHT = 1.0
NU = 0.035
WIDTH = 0.24
SOURCE_GAIN = 0.82
VISCOUS_WEIGHT = 1.0
CURVATURE_DAMPING = 0.18
BOUNDARY_DAMPING = 0.22
BETA_CANDIDATES = (-1.0, -0.5, -0.25, 0.0, 0.125, 0.25, 0.5, 0.75, 1.0, 1.25, 1.5)
JACOBI_TOL = 1.0e-12
JACOBI_MAX_SWEEPS = 250

CONTROL_CARD = {
    "O": (
        "Lane 3 owns only scripts/ns_sprint149_linearization_spectrum_probe.py "
        "and outputs/ns_sprint149_linearization_spectrum_probe/ artifacts."
    ),
    "R": (
        "Emit deterministic evidence rows for beta candidates in a transparent "
        "finite-difference toy linearization around a Hou-Luo-like concentration profile."
    ),
    "C": (
        "Single stdlib Python script writes rows JSON, rows CSV, summary JSON, "
        "Markdown, and manifest through an atomic staging directory."
    ),
    "S": (
        "The state is evidence-only: positive toy spectral drift may be observed, "
        "but no self-similar profile analysis or scaling-consistency theorem is proved."
    ),
    "L": (
        "Use a fixed Dirichlet grid, explicit second-difference diffusion, "
        "multiplicative concentration source, damping terms, and Jacobi eigenvalue scan."
    ),
    "P": (
        "Treat the result as a reproducible diagnostic for the missing "
        "ScalingConsistencyForHouLuoConcentration gate, not as proof."
    ),
    "G": (
        "Validation passes only when all beta rows are present, spectral values "
        "are finite, output hashes are recorded, and all proof/promotion flags remain false."
    ),
    "F": (
        "Missing: rigorous Hou-Luo self-similar profile analysis, PDE linearization "
        "identification, scaling-consistency theorem, and Clay Navier-Stokes solution."
    ),
}


@dataclass(frozen=True)
class ProbeRow:
    beta: float
    beta_sign: str
    grid_n: int
    grid_dx: float
    profile_mass: float
    profile_peak: float
    profile_width_proxy: float
    operator_trace: float
    dominant_eigenvalue: float
    second_eigenvalue: float
    bottom_eigenvalue: float
    spectral_gap: float
    spectral_radius: float
    drift_from_beta_zero: float
    positive_dominant_eigenvalue: bool
    stability_indicator: str
    beta_positive_candidate: bool
    interpretation: str

    def as_row(self) -> dict[str, Any]:
        row = asdict(self)
        row["sprint"] = SPRINT
        row["lane"] = LANE
        row["contract"] = CONTRACT
        row["program"] = PROGRAM
        row["target_gate"] = TARGET_GATE
        row["model_kind"] = MODEL_KIND
        row["decision"] = DECISION
        row["linearization_probe_complete"] = True
        row["self_similar_profile_analysis_proved"] = False
        row["scaling_consistency_proved"] = False
        row["full_clay_ns_solved"] = False
        row["clay_navier_stokes_promoted"] = False
        row["promotion_allowed"] = False
        row["claim_proved"] = False
        row["claim_proven"] = False
        row["no_pde_proof"] = True
        row["no_promotion"] = True
        row["row_hash"] = stable_hash({k: v for k, v in row.items() if k != "row_hash"})
        return row


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, default=Path.cwd())
    parser.add_argument("--out-dir", type=Path, default=OUT_DIR_DEFAULT)
    return parser.parse_args()


def stable_hash(value: Any) -> str:
    encoded = json.dumps(value, sort_keys=True, separators=(",", ":")).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def file_sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(65536), b""):
            digest.update(chunk)
    return digest.hexdigest()


def display_path(path: Path, repo_root: Path) -> str:
    try:
        return str(path.relative_to(repo_root))
    except ValueError:
        return str(path)


def clean(value: float) -> float:
    if abs(value) < 1.0e-14:
        return 0.0
    return float(f"{value:.15g}")


def make_grid(n: int) -> tuple[list[float], float]:
    if n < 5:
        raise ValueError("grid_n must be at least 5")
    dx = (DOMAIN_RIGHT - DOMAIN_LEFT) / (n - 1)
    return [DOMAIN_LEFT + i * dx for i in range(n)], dx


def hou_luo_like_profile(x: float, beta: float) -> float:
    """Smooth concentrated bump with beta-dependent amplitude and width."""
    width = WIDTH / math.sqrt(1.0 + 0.35 * max(beta, 0.0))
    core = math.exp(-(x / width) ** 2)
    shoulder = 1.0 / (1.0 + 16.0 * x * x)
    amplitude = 1.0 + 0.45 * beta
    return max(0.0, amplitude) * core + 0.22 * shoulder


def build_operator(beta: float, grid: list[float], dx: float) -> list[list[float]]:
    """Build a symmetric Dirichlet toy linearization on interior grid nodes."""
    interior = grid[1:-1]
    m = len(interior)
    inv_dx2 = 1.0 / (dx * dx)
    matrix = [[0.0 for _ in range(m)] for _ in range(m)]
    for i, x in enumerate(interior):
        profile = hou_luo_like_profile(x, beta)
        source = beta * SOURCE_GAIN * profile
        damping = CURVATURE_DAMPING * x * x + BOUNDARY_DAMPING * abs(x) ** 4
        matrix[i][i] = -2.0 * NU * VISCOUS_WEIGHT * inv_dx2 + source - damping
        if i > 0:
            matrix[i][i - 1] = NU * VISCOUS_WEIGHT * inv_dx2
        if i < m - 1:
            matrix[i][i + 1] = NU * VISCOUS_WEIGHT * inv_dx2
    return matrix


def max_offdiag(matrix: list[list[float]]) -> tuple[float, int, int]:
    best = 0.0
    p = 0
    q = 1
    n = len(matrix)
    for i in range(n):
        for j in range(i + 1, n):
            value = abs(matrix[i][j])
            if value > best:
                best = value
                p = i
                q = j
    return best, p, q


def jacobi_eigenvalues_symmetric(matrix: list[list[float]]) -> list[float]:
    """Deterministic Jacobi rotation eigenvalue solver for small symmetric matrices."""
    a = [row[:] for row in matrix]
    n = len(a)
    for _ in range(JACOBI_MAX_SWEEPS * n * n):
        off, p, q = max_offdiag(a)
        if off < JACOBI_TOL:
            break
        app = a[p][p]
        aqq = a[q][q]
        apq = a[p][q]
        if apq == 0.0:
            continue
        tau = (aqq - app) / (2.0 * apq)
        sign = 1.0 if tau >= 0.0 else -1.0
        t = sign / (abs(tau) + math.sqrt(1.0 + tau * tau))
        c = 1.0 / math.sqrt(1.0 + t * t)
        s = t * c
        for k in range(n):
            if k != p and k != q:
                akp = a[k][p]
                akq = a[k][q]
                a[k][p] = c * akp - s * akq
                a[p][k] = a[k][p]
                a[k][q] = s * akp + c * akq
                a[q][k] = a[k][q]
        a[p][p] = c * c * app - 2.0 * s * c * apq + s * s * aqq
        a[q][q] = s * s * app + 2.0 * s * c * apq + c * c * aqq
        a[p][q] = 0.0
        a[q][p] = 0.0
    return sorted((a[i][i] for i in range(n)), reverse=True)


def profile_metrics(beta: float, grid: list[float], dx: float) -> tuple[float, float, float]:
    values = [hou_luo_like_profile(x, beta) for x in grid]
    mass = sum(values) * dx
    peak = max(values)
    second_moment = sum((x * x) * v for x, v in zip(grid, values)) * dx / max(mass, 1.0e-12)
    return clean(mass), clean(peak), clean(math.sqrt(max(second_moment, 0.0)))


def compute_raw_rows() -> list[dict[str, Any]]:
    grid, dx = make_grid(GRID_N)
    raw: list[dict[str, Any]] = []
    baseline_dominant = None
    for beta in BETA_CANDIDATES:
        matrix = build_operator(beta, grid, dx)
        eigenvalues = jacobi_eigenvalues_symmetric(matrix)
        dominant = eigenvalues[0]
        second = eigenvalues[1]
        bottom = eigenvalues[-1]
        if beta == 0.0:
            baseline_dominant = dominant
        raw.append(
            {
                "beta": beta,
                "grid": grid,
                "dx": dx,
                "matrix": matrix,
                "eigenvalues": eigenvalues,
                "dominant": dominant,
                "second": second,
                "bottom": bottom,
            }
        )
    if baseline_dominant is None:
        raise RuntimeError("beta=0 baseline missing")
    rows = []
    for item in raw:
        beta = item["beta"]
        mass, peak, width = profile_metrics(beta, item["grid"], item["dx"])
        dominant = clean(item["dominant"])
        second = clean(item["second"])
        bottom = clean(item["bottom"])
        spectral_gap = clean(dominant - second)
        spectral_radius = clean(max(abs(v) for v in item["eigenvalues"]))
        drift = clean(item["dominant"] - baseline_dominant)
        trace = clean(sum(item["matrix"][i][i] for i in range(len(item["matrix"]))))
        positive = dominant > 0.0
        beta_positive_candidate = beta > 0.0 and positive
        if positive:
            indicator = "toy_unstable_positive_dominant_mode"
            interpretation = "toy_operator_has_positive_dominant_eigenvalue_evidence_only"
        elif drift > 0.0:
            indicator = "toy_stable_with_positive_drift"
            interpretation = "dominant_mode_remains_negative_but_drifts_upward_evidence_only"
        else:
            indicator = "toy_stable_nonpositive_drift"
            interpretation = "dominant_mode_nonpositive_with_no_positive_drift_evidence_only"
        rows.append(
            ProbeRow(
                beta=clean(beta),
                beta_sign="positive" if beta > 0 else "negative" if beta < 0 else "zero",
                grid_n=GRID_N,
                grid_dx=clean(item["dx"]),
                profile_mass=mass,
                profile_peak=peak,
                profile_width_proxy=width,
                operator_trace=trace,
                dominant_eigenvalue=dominant,
                second_eigenvalue=second,
                bottom_eigenvalue=bottom,
                spectral_gap=spectral_gap,
                spectral_radius=spectral_radius,
                drift_from_beta_zero=drift,
                positive_dominant_eigenvalue=positive,
                stability_indicator=indicator,
                beta_positive_candidate=beta_positive_candidate,
                interpretation=interpretation,
            ).as_row()
        )
    return rows


def validate_rows(rows: list[dict[str, Any]]) -> list[str]:
    failures: list[str] = []
    if len(rows) != len(BETA_CANDIDATES):
        failures.append("row_count_mismatch")
    observed = {row["beta"] for row in rows}
    expected = {clean(beta) for beta in BETA_CANDIDATES}
    if observed != expected:
        failures.append("beta_candidate_set_mismatch")
    if not any(row["beta"] == 0.0 for row in rows):
        failures.append("missing_beta_zero_baseline")
    finite_keys = (
        "profile_mass",
        "profile_peak",
        "profile_width_proxy",
        "operator_trace",
        "dominant_eigenvalue",
        "second_eigenvalue",
        "bottom_eigenvalue",
        "spectral_gap",
        "spectral_radius",
        "drift_from_beta_zero",
    )
    for row in rows:
        for key in finite_keys:
            if not math.isfinite(float(row[key])):
                failures.append(f"nonfinite_{key}_{row['beta']}")
        for flag in (
            "self_similar_profile_analysis_proved",
            "scaling_consistency_proved",
            "full_clay_ns_solved",
            "clay_navier_stokes_promoted",
            "promotion_allowed",
        ):
            if row[flag] is not False:
                failures.append(f"{flag}_not_false_{row['beta']}")
        if row["linearization_probe_complete"] is not True:
            failures.append(f"linearization_probe_complete_not_true_{row['beta']}")
    return failures


def build_summary(rows: list[dict[str, Any]], invariant_failures: list[str]) -> dict[str, Any]:
    positive_rows = [row for row in rows if row["beta_positive_candidate"]]
    dominant_values = [float(row["dominant_eigenvalue"]) for row in rows]
    drift_values = [float(row["drift_from_beta_zero"]) for row in rows]
    summary: dict[str, Any] = {
        "sprint": SPRINT,
        "lane": LANE,
        "contract": CONTRACT,
        "program": PROGRAM,
        "target_gate": TARGET_GATE,
        "model_kind": MODEL_KIND,
        "decision": DECISION,
        "promotion_decision": PROMOTION_DECISION,
        "control_card": CONTROL_CARD,
        "row_count": len(rows),
        "beta_candidates": [clean(beta) for beta in BETA_CANDIDATES],
        "grid_n": GRID_N,
        "domain": [DOMAIN_LEFT, DOMAIN_RIGHT],
        "nu": NU,
        "profile_formula": "q_beta(x)=max(0,1+0.45 beta) exp(-(x/w_beta)^2)+0.22/(1+16x^2)",
        "width_formula": "w_beta=0.24/sqrt(1+0.35 max(beta,0))",
        "operator_formula": "L_beta = nu Dxx + beta*0.82*q_beta(x) - 0.18*x^2 - 0.22*|x|^4 with Dirichlet endpoints",
        "linearization_probe_complete": True,
        "beta_positive_candidate_seen": bool(positive_rows),
        "beta_positive_candidate_betas": [row["beta"] for row in positive_rows],
        "max_dominant_eigenvalue": clean(max(dominant_values)),
        "min_dominant_eigenvalue": clean(min(dominant_values)),
        "max_drift_from_beta_zero": clean(max(drift_values)),
        "toy_unstable_row_count": sum(1 for row in rows if row["positive_dominant_eigenvalue"]),
        "self_similar_profile_analysis_proved": False,
        "scaling_consistency_proved": False,
        "full_clay_ns_solved": False,
        "clay_navier_stokes_promoted": False,
        "promotion_allowed": False,
        "artifact_complete": True,
        "fail_closed": True,
        "invariant_failures": invariant_failures,
        "invariant_valid": not invariant_failures,
        "invariants_passed": not invariant_failures,
        "artifact_claim": "finite_difference_toy_spectrum_evidence_only",
        "proof_claim": "none",
        "blockers": [
            "PDELinearizationIdentificationMissing",
            "SelfSimilarProfileAnalysisMissing",
            "ScalingConsistencyForHouLuoConcentrationNotProved",
            "ToySpectrumDoesNotImplyPDEStability",
            "ClayNavierStokesPromotionBlocked",
        ],
    }
    summary["summary_hash"] = stable_hash({k: v for k, v in summary.items() if k != "summary_hash"})
    return summary


def write_json(path: Path, payload: Any) -> None:
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def write_csv(path: Path, rows: list[dict[str, Any]]) -> None:
    fieldnames = sorted({key for row in rows for key in row})
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=fieldnames)
        writer.writeheader()
        writer.writerows(rows)


def write_report(path: Path, summary: dict[str, Any], rows: list[dict[str, Any]]) -> None:
    lines = [
        "# Sprint 149 Linearization Spectrum Probe",
        "",
        "This artifact is a deterministic finite-difference toy probe for the "
        "ScalingConsistencyForHouLuoConcentration gate. It does not claim a proof.",
        "",
        "## Control Card",
        "",
    ]
    for key in ("O", "R", "C", "S", "L", "P", "G", "F"):
        lines.append(f"- **{key}**: {CONTROL_CARD[key]}")
    lines.extend(
        [
            "",
            "## Method",
            "",
            f"- Model kind: `{MODEL_KIND}`",
            f"- Profile: `{summary['profile_formula']}`",
            f"- Width: `{summary['width_formula']}`",
            f"- Operator: `{summary['operator_formula']}`",
            "- Spectrum: deterministic Jacobi eigenvalue scan of the symmetric toy matrix.",
            "",
            "## Gate Flags",
            "",
            f"- `linearization_probe_complete`: `{str(summary['linearization_probe_complete']).lower()}`",
            f"- `beta_positive_candidate_seen`: `{str(summary['beta_positive_candidate_seen']).lower()}`",
            "- `self_similar_profile_analysis_proved`: `false`",
            "- `scaling_consistency_proved`: `false`",
            "- `full_clay_ns_solved`: `false`",
            "- `clay_navier_stokes_promoted`: `false`",
            "",
            "## Rows",
            "",
            "| beta | dominant | drift from beta=0 | gap | stability indicator |",
            "| ---: | ---: | ---: | ---: | --- |",
        ]
    )
    for row in rows:
        lines.append(
            "| {beta} | {dom} | {drift} | {gap} | {indicator} |".format(
                beta=row["beta"],
                dom=row["dominant_eigenvalue"],
                drift=row["drift_from_beta_zero"],
                gap=row["spectral_gap"],
                indicator=row["stability_indicator"],
            )
        )
    lines.extend(
        [
            "",
            "## Interpretation",
            "",
            "Positive beta rows with positive dominant toy eigenvalue are recorded as "
            "candidate evidence only. They do not prove scaling consistency, PDE "
            "stability, self-similar profile validity, or any Clay Navier-Stokes claim.",
            "",
        ]
    )
    path.write_text("\n".join(lines), encoding="utf-8")


def write_manifest(
    path: Path,
    final_out: Path,
    repo_root: Path,
    files: list[Path],
) -> None:
    manifest = {
        "sprint": SPRINT,
        "lane": LANE,
        "contract": CONTRACT,
        "out_dir": display_path(final_out, repo_root),
        "files": [
            {
                "path": display_path(final_out / file_path.name, repo_root),
                "bytes": file_path.stat().st_size,
                "sha256": file_sha256(file_path),
            }
            for file_path in files
        ],
    }
    manifest["manifest_hash"] = stable_hash(manifest)
    write_json(path, manifest)


def atomic_emit(repo_root: Path, out_dir: Path, rows: list[dict[str, Any]], summary: dict[str, Any]) -> None:
    final_out = out_dir if out_dir.is_absolute() else repo_root / out_dir
    final_out.parent.mkdir(parents=True, exist_ok=True)
    staging = Path(tempfile.mkdtemp(prefix=f".{CONTRACT}.", dir=str(final_out.parent)))
    try:
        rows_json = staging / ROWS_JSON_NAME
        rows_csv = staging / ROWS_CSV_NAME
        summary_json = staging / SUMMARY_NAME
        report = staging / REPORT_NAME
        manifest = staging / MANIFEST_NAME
        write_json(rows_json, rows)
        write_csv(rows_csv, rows)
        write_json(summary_json, summary)
        write_report(report, summary, rows)
        write_manifest(manifest, final_out, repo_root, [summary_json, rows_json, rows_csv, report])
        if final_out.exists():
            shutil.rmtree(final_out)
        os.replace(staging, final_out)
    except Exception:
        shutil.rmtree(staging, ignore_errors=True)
        raise


def main() -> int:
    args = parse_args()
    repo_root = args.repo_root.resolve()
    rows = compute_raw_rows()
    invariant_failures = validate_rows(rows)
    summary = build_summary(rows, invariant_failures)
    if invariant_failures:
        print("Invariant failures: " + ", ".join(invariant_failures), file=sys.stderr)
        return 2
    atomic_emit(repo_root, args.out_dir, rows, summary)
    print(json.dumps({"contract": CONTRACT, "rows": len(rows), "out_dir": str(args.out_dir)}, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
