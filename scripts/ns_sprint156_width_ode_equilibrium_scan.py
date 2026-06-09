#!/usr/bin/env python3
"""Sprint 156 corrected width-ODE/equilibrium scalar scan.

This deterministic stdlib emitter scans the corrected reduced width model

    delta_dot = -Umax*logOmega*delta + nu/delta

with equilibrium

    delta_eq = sqrt(nu/(Umax*logOmega)).

It also records the compatible scalar vorticity-growth inequality

    Omega_dot <= C*Umax*Omega*logOmega

and its finite-time double-exponential control for finite T.  The artifact
supports only reduced-model validity bookkeeping.  It is not a BKM proof and
does not solve the Clay Navier-Stokes problem.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
import math
import shutil
import sys
import tempfile
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any


CONTRACT = "ns_sprint156_width_ode_equilibrium_scan"
OUT_DIR_DEFAULT = Path("outputs/ns_sprint156_width_ode_equilibrium_scan")
SUMMARY_NAME = CONTRACT + "_summary.json"
ROWS_JSON_NAME = CONTRACT + "_rows.json"
ROWS_CSV_NAME = CONTRACT + "_rows.csv"
REPORT_NAME = CONTRACT + ".md"
MANIFEST_NAME = CONTRACT + "_manifest.json"

SPRINT = 156
LANE = 3
PROGRAM = "CorrectedWidthODEEquilibriumScalarScan"
MODEL_NAME = "CorrectedWidthODEModelValiditySupport"
WIDTH_ODE_FORMULA = "delta_dot = -Umax*logOmega*delta + nu/delta"
EQUILIBRIUM_FORMULA = "delta_eq = sqrt(nu/(Umax*logOmega))"
OMEGA_GROWTH_FORMULA = "Omega_dot <= C*Umax*Omega*logOmega"
DOUBLE_EXP_FORMULA = "Omega(t) <= exp(log(Omega0)*exp(C*Umax*T))"

FLAGS = {
    "model_validity_support": True,
    "bkm_finite": False,
    "full_clay_ns_solved": False,
    "clay_navier_stokes_promoted": False,
    "promotion_allowed": False,
    "evidence_only": True,
}

CONTROL_CARD = {
    "O": (
        "Worker 3 owns scripts/ns_sprint156_width_ode_equilibrium_scan.py and "
        "outputs/ns_sprint156_width_ode_equilibrium_scan/."
    ),
    "R": (
        "Scan the corrected scalar width ODE equilibrium, compatible Omega "
        "growth inequality, and finite-T double-exponential control."
    ),
    "C": (
        "A deterministic Python stdlib emitter writes rows JSON, rows CSV, "
        "summary JSON, Markdown, and manifest through an atomic directory swap."
    ),
    "S": (
        "The corrected equilibrium delta_eq=sqrt(nu/(Umax*logOmega)) is "
        "algebraically supported for positive nu, Umax, and logOmega."
    ),
    "L": (
        "The finite-T double-exponential bound supports scalar model validity "
        "only; BKM and full Navier-Stokes theorem obligations remain separate."
    ),
    "P": (
        "Use these rows as reduced-model validity evidence and invariant "
        "checks, with no promotion beyond model-validity support."
    ),
    "G": (
        "Validation requires positive parameters, equilibrium sign consistency, "
        "growth inequality compliance, finite double-exponential bounds, and "
        "hard false BKM/Clay promotion flags."
    ),
    "F": (
        "No full localized Navier-Stokes derivation, no BKM integrability "
        "theorem, and no Clay Navier-Stokes solution are claimed."
    ),
}


@dataclass(frozen=True)
class ScanPoint:
    nu: float
    Umax: float
    Omega: float
    C: float
    T: float
    delta_factor: float
    growth_factor: float

    def as_row(self) -> dict[str, Any]:
        log_omega = math.log(self.Omega)
        delta_eq = math.sqrt(self.nu / (self.Umax * log_omega))
        delta = self.delta_factor * delta_eq
        delta_dot = width_delta_dot(self.nu, self.Umax, self.Omega, delta)
        omega_growth_cap = self.C * self.Umax * self.Omega * log_omega
        omega_dot_model = self.growth_factor * omega_growth_cap
        omega_bound = double_exp_bound(self.Omega, self.C, self.Umax, self.T)
        log_bound = math.log(omega_bound)
        row = {
            **base_fields(),
            **FLAGS,
            "row_id": row_id(self),
            "row_kind": "corrected_width_ode_equilibrium_scan",
            "model_name": MODEL_NAME,
            "nu": clean(self.nu),
            "Umax": clean(self.Umax),
            "Omega": clean(self.Omega),
            "logOmega": clean(log_omega),
            "C": clean(self.C),
            "T": clean(self.T),
            "delta_factor_relative_to_eq": clean(self.delta_factor),
            "growth_factor_relative_to_cap": clean(self.growth_factor),
            "delta_eq": clean(delta_eq),
            "delta": clean(delta),
            "delta_dot": clean(delta_dot),
            "delta_dot_sign": sign_label(delta_dot),
            "expected_sign_relative_to_equilibrium": expected_sign(self.delta_factor),
            "sign_matches_equilibrium_rule": sign_label(delta_dot) == expected_sign(self.delta_factor),
            "equilibrium_residual_at_delta_eq": clean(width_delta_dot(self.nu, self.Umax, self.Omega, delta_eq)),
            "equilibrium_formula": EQUILIBRIUM_FORMULA,
            "width_ode_formula": WIDTH_ODE_FORMULA,
            "Omega_dot_model": clean(omega_dot_model),
            "Omega_growth_cap": clean(omega_growth_cap),
            "omega_growth_inequality_holds": omega_dot_model <= omega_growth_cap + 1.0e-12,
            "omega_growth_formula": OMEGA_GROWTH_FORMULA,
            "Omega_double_exp_bound_T": clean(omega_bound),
            "log_Omega_double_exp_bound_T": clean(log_bound),
            "double_exponential_bound_finite": math.isfinite(omega_bound) and omega_bound > 0.0,
            "double_exponential_formula": DOUBLE_EXP_FORMULA,
            "finite_T_control_supported": math.isfinite(omega_bound) and self.T < math.inf,
            "support_level": "model_validity_support",
            "claim_boundary": "no_bkm_or_clay_promotion",
            "fail_closed": True,
        }
        row["row_hash"] = stable_hash({k: v for k, v in row.items() if k != "row_hash"})
        return row


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, default=Path.cwd())
    parser.add_argument("--out-dir", type=Path, default=OUT_DIR_DEFAULT)
    return parser.parse_args()


def base_fields() -> dict[str, Any]:
    return {
        "sprint": SPRINT,
        "lane": LANE,
        "contract": CONTRACT,
        "program": PROGRAM,
    }


def clean(value: float) -> float:
    if abs(value) < 1.0e-14:
        return 0.0
    return float(f"{value:.15g}")


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


def width_delta_dot(nu: float, Umax: float, Omega: float, delta: float) -> float:
    return -Umax * math.log(Omega) * delta + nu / delta


def double_exp_bound(Omega0: float, C: float, Umax: float, T: float) -> float:
    return math.exp(math.log(Omega0) * math.exp(C * Umax * T))


def sign_label(value: float) -> str:
    if abs(value) <= 1.0e-11:
        return "zero"
    return "positive" if value > 0.0 else "negative"


def expected_sign(delta_factor: float) -> str:
    if abs(delta_factor - 1.0) <= 1.0e-12:
        return "zero"
    return "positive" if delta_factor < 1.0 else "negative"


def row_id(point: ScanPoint) -> str:
    return (
        f"nu_{point.nu:g}__U_{point.Umax:g}__Omega_{point.Omega:g}"
        f"__C_{point.C:g}__T_{point.T:g}__df_{point.delta_factor:g}"
        f"__gf_{point.growth_factor:g}"
    ).replace(".", "p")


def build_rows() -> list[dict[str, Any]]:
    nus = [0.0025, 0.01, 0.04]
    umax_values = [0.5, 1.0, 2.5]
    omegas = [1.2, 2.0, 6.0, 20.0]
    constants = [0.25, 1.0]
    times = [0.0, 0.5, 1.0, 2.0]
    delta_factors = [0.5, 0.9, 1.0, 1.25, 2.0]
    growth_factors = [0.0, 0.5, 1.0]
    return [
        ScanPoint(
            nu=nu,
            Umax=Umax,
            Omega=Omega,
            C=C,
            T=T,
            delta_factor=delta_factor,
            growth_factor=growth_factor,
        ).as_row()
        for nu in nus
        for Umax in umax_values
        for Omega in omegas
        for C in constants
        for T in times
        for delta_factor in delta_factors
        for growth_factor in growth_factors
    ]


def validate(rows: list[dict[str, Any]]) -> list[str]:
    errors: list[str] = []
    if not rows:
        return ["scan rows are empty"]
    signs = {row["delta_dot_sign"] for row in rows}
    if signs != {"positive", "zero", "negative"}:
        errors.append(f"expected positive/zero/negative sign coverage, got {sorted(signs)}")
    for row in rows:
        for key, expected in FLAGS.items():
            if row.get(key) is not expected:
                errors.append(f"{row['row_id']} invalid flag {key}={row.get(key)!r}")
        for key in ("nu", "Umax", "Omega", "logOmega", "C"):
            if row[key] <= 0.0:
                errors.append(f"{row['row_id']} nonpositive {key}")
        if row["Omega"] <= 1.0:
            errors.append(f"{row['row_id']} Omega must exceed 1")
        expected_delta_eq = math.sqrt(row["nu"] / (row["Umax"] * row["logOmega"]))
        if not math.isclose(row["delta_eq"], expected_delta_eq, rel_tol=1.0e-12, abs_tol=1.0e-12):
            errors.append(f"{row['row_id']} corrected equilibrium mismatch")
        if abs(row["equilibrium_residual_at_delta_eq"]) > 1.0e-11:
            errors.append(f"{row['row_id']} equilibrium residual is not zero")
        if not row["sign_matches_equilibrium_rule"]:
            errors.append(f"{row['row_id']} width ODE sign rule failed")
        if not row["omega_growth_inequality_holds"]:
            errors.append(f"{row['row_id']} Omega growth inequality failed")
        if row["Omega_dot_model"] > row["Omega_growth_cap"] + 1.0e-12:
            errors.append(f"{row['row_id']} Omega_dot exceeds cap")
        if not row["double_exponential_bound_finite"]:
            errors.append(f"{row['row_id']} double exponential bound is not finite")
        if row["Omega_double_exp_bound_T"] + 1.0e-12 < row["Omega"]:
            errors.append(f"{row['row_id']} bound decreased below initial Omega")
        if row["bkm_finite"] or row["full_clay_ns_solved"] or row["clay_navier_stokes_promoted"]:
            errors.append(f"{row['row_id']} promoted beyond model validity support")
    return errors


def write_json(path: Path, value: Any) -> None:
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def write_csv(path: Path, rows: list[dict[str, Any]]) -> None:
    fieldnames: list[str] = []
    for row in rows:
        for key in row:
            if key not in fieldnames:
                fieldnames.append(key)
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=fieldnames)
        writer.writeheader()
        for row in rows:
            writer.writerow(
                {
                    key: json.dumps(value, sort_keys=True) if isinstance(value, (dict, list)) else value
                    for key, value in row.items()
                }
            )


def build_summary(rows: list[dict[str, Any]]) -> dict[str, Any]:
    validation_errors = validate(rows)
    sign_counts: dict[str, int] = {"positive": 0, "zero": 0, "negative": 0}
    for row in rows:
        sign_counts[row["delta_dot_sign"]] += 1
    summary = {
        **base_fields(),
        **FLAGS,
        "control_card": CONTROL_CARD,
        "model_name": MODEL_NAME,
        "width_ode_formula": WIDTH_ODE_FORMULA,
        "equilibrium_formula": EQUILIBRIUM_FORMULA,
        "omega_growth_formula": OMEGA_GROWTH_FORMULA,
        "double_exponential_formula": DOUBLE_EXP_FORMULA,
        "row_count": len(rows),
        "sign_counts": sign_counts,
        "nu_values": sorted({row["nu"] for row in rows}),
        "Umax_values": sorted({row["Umax"] for row in rows}),
        "Omega_values": sorted({row["Omega"] for row in rows}),
        "C_values": sorted({row["C"] for row in rows}),
        "T_values": sorted({row["T"] for row in rows}),
        "delta_factors": sorted({row["delta_factor_relative_to_eq"] for row in rows}),
        "growth_factors": sorted({row["growth_factor_relative_to_cap"] for row in rows}),
        "all_equilibrium_signs_match": all(row["sign_matches_equilibrium_rule"] for row in rows),
        "all_growth_inequalities_hold": all(row["omega_growth_inequality_holds"] for row in rows),
        "all_double_exp_bounds_finite": all(row["double_exponential_bound_finite"] for row in rows),
        "theorem_flags_fail_closed": True,
        "no_promotion_beyond_model_validity_support": True,
        "validation_passed": not validation_errors,
        "validation_errors": validation_errors,
    }
    summary["summary_hash"] = stable_hash(
        {key: value for key, value in summary.items() if key != "summary_hash"}
    )
    return summary


def build_report(summary: dict[str, Any]) -> str:
    lines = [
        f"# Sprint {SPRINT} Corrected Width ODE Equilibrium Scan",
        "",
        f"- Contract: `{CONTRACT}`",
        f"- Width ODE: `{WIDTH_ODE_FORMULA}`",
        f"- Equilibrium: `{EQUILIBRIUM_FORMULA}`",
        f"- Omega growth cap: `{OMEGA_GROWTH_FORMULA}`",
        f"- Finite-T bound: `{DOUBLE_EXP_FORMULA}`",
        f"- Rows: {summary['row_count']}",
        f"- Validation passed: `{str(summary['validation_passed']).lower()}`",
        f"- Sign counts: `{summary['sign_counts']}`",
        "",
        "## Flags",
    ]
    for key, value in FLAGS.items():
        lines.append(f"- `{key}`: `{str(value).lower()}`")
    lines.extend(["", "## O/R/C/S/L/P/G/F"])
    for key in ("O", "R", "C", "S", "L", "P", "G", "F"):
        lines.append(f"- **{key}**: {CONTROL_CARD[key]}")
    lines.extend(
        [
            "",
            "## Boundary",
            "",
            "This scan records corrected reduced-model equilibrium evidence and "
            "finite-time scalar double-exponential control only. It does not "
            "promote BKM finiteness, full Clay Navier-Stokes, or any theorem "
            "beyond model-validity support.",
            "",
        ]
    )
    return "\n".join(lines)


def build_manifest(repo_root: Path, out_dir: Path, summary: dict[str, Any]) -> dict[str, Any]:
    files = sorted(
        path.name
        for path in out_dir.iterdir()
        if path.is_file() and path.name != MANIFEST_NAME
    )
    manifest = {
        **base_fields(),
        "output_dir": display_path(out_dir, repo_root),
        "files": [
            {
                "path": display_path(out_dir / name, repo_root),
                "sha256": file_sha256(out_dir / name),
            }
            for name in files
        ],
        "manifest_hash": stable_hash({"files": files, "summary": summary}),
    }
    return manifest


def emit(repo_root: Path, out_dir: Path) -> dict[str, Any]:
    repo_root = repo_root.resolve()
    out_dir = out_dir if out_dir.is_absolute() else repo_root / out_dir
    rows = build_rows()
    summary = build_summary(rows)
    if not summary["validation_passed"]:
        raise ValueError("validation failed: " + "; ".join(summary["validation_errors"]))

    out_dir.parent.mkdir(parents=True, exist_ok=True)
    tmp_dir = Path(tempfile.mkdtemp(prefix=out_dir.name + ".", dir=out_dir.parent))
    try:
        write_json(tmp_dir / ROWS_JSON_NAME, rows)
        write_csv(tmp_dir / ROWS_CSV_NAME, rows)
        write_json(tmp_dir / SUMMARY_NAME, summary)
        (tmp_dir / REPORT_NAME).write_text(build_report(summary), encoding="utf-8")
        if out_dir.exists():
            shutil.rmtree(out_dir)
        tmp_dir.rename(out_dir)
        manifest = build_manifest(repo_root, out_dir, summary)
        write_json(out_dir / MANIFEST_NAME, manifest)
    except Exception:
        shutil.rmtree(tmp_dir, ignore_errors=True)
        raise

    return summary


def main() -> int:
    args = parse_args()
    summary = emit(args.repo_root, args.out_dir)
    print(
        json.dumps(
            {
                "contract": CONTRACT,
                "output_dir": str(args.out_dir),
                "row_count": summary["row_count"],
                "model_validity_support": summary["model_validity_support"],
                "bkm_finite": summary["bkm_finite"],
                "full_clay_ns_solved": summary["full_clay_ns_solved"],
                "validation_passed": summary["validation_passed"],
                "summary_hash": summary["summary_hash"],
            },
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
