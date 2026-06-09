#!/usr/bin/env python3
"""Sprint 151 width-ODE extraction evidence ledger.

This deterministic stdlib emitter records an evidence-only derivation ledger
for the reduced localized-enstrophy width model

    dot(delta) = -Omega log(Omega) + nu / delta.

It scans several positive nu/Omega/delta values, records the equilibrium
delta_eq = nu / (Omega log(Omega)) when Omega > 1, checks the sign of
dot(delta) relative to that equilibrium, and emits a conditional subcritical
Omega projection with beta > 0.  It is not a Navier-Stokes theorem extractor,
not a BKM closure, and not a Clay solution.
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


CONTRACT = "ns_sprint151_width_ode_extraction"
OUT_DIR_DEFAULT = Path("outputs/ns_sprint151_width_ode_extraction")
SUMMARY_NAME = CONTRACT + "_summary.json"
SCAN_JSON_NAME = CONTRACT + "_scan_rows.json"
SCAN_CSV_NAME = CONTRACT + "_scan_rows.csv"
DERIVATION_JSON_NAME = CONTRACT + "_derivation_ledger.json"
DERIVATION_CSV_NAME = CONTRACT + "_derivation_ledger.csv"
SUBCRITICAL_JSON_NAME = CONTRACT + "_subcritical_projection.json"
SUBCRITICAL_CSV_NAME = CONTRACT + "_subcritical_projection.csv"
REPORT_NAME = CONTRACT + ".md"
MANIFEST_NAME = CONTRACT + "_manifest.json"

SPRINT = 151
LANE = 4
PROGRAM = "LocalizedEnstrophyWidthODEEvidenceProgram"
MODEL_NAME = "WidthODEFromLocalizedEnstrophyTerms"
ODE_FORMULA = "delta_dot = -Omega*log(Omega) + nu/delta"
EQUILIBRIUM_FORMULA = "delta_eq = nu/(Omega*log(Omega))"

FLAGS = {
    "width_ode_extracted_from_ns": False,
    "equilibrium_model_supported": True,
    "subcritical_ode_conditional": True,
    "bkm_finite": False,
    "full_clay_ns_solved": False,
}

CONTROL_CARD = {
    "O": (
        "Worker 4 owns scripts/ns_sprint151_width_ode_extraction.py and "
        "outputs/ns_sprint151_width_ode_extraction/."
    ),
    "R": (
        "Create a deterministic evidence ledger for the reduced width ODE "
        "dot(delta) = -Omega log Omega + nu/delta from localized enstrophy "
        "term accounting."
    ),
    "C": (
        "The artifact is a Python stdlib emitter producing JSON, CSV, "
        "Markdown, and manifest files with stable hashes and fail-closed flags."
    ),
    "S": (
        "For Omega > 1 the equilibrium model delta_eq = nu/(Omega log Omega) "
        "is supported algebraically, and the scan confirms dot(delta) is "
        "positive below equilibrium, zero at equilibrium, and negative above it."
    ),
    "L": (
        "Localized stretching is represented by the compressive term "
        "-Omega log Omega and viscosity by +nu/delta; this is a reduced scalar "
        "projection, not a derivation from the full Navier-Stokes system."
    ),
    "P": (
        "Use the ledger as evidence for reduced-model bookkeeping and for "
        "conditional beta-positive subcritical projection only."
    ),
    "G": (
        "Validation requires exact theorem flags, positive scan parameters, "
        "Omega > 1 for equilibrium rows, beta > 0 for subcritical rows, and "
        "the expected sign relation to delta_eq."
    ),
    "F": (
        "Gaps remain: no rigorous extraction from localized Navier-Stokes "
        "enstrophy identities, no BKM finite integral theorem, and no full "
        "Clay Navier-Stokes solution."
    ),
}


@dataclass(frozen=True)
class DerivationStep:
    step_id: str
    localized_term: str
    reduced_symbol: str
    sign: str
    model_contribution: str
    evidence_status: str
    theorem_status: str
    note: str

    def as_row(self) -> dict[str, Any]:
        row = asdict(self)
        row.update(base_fields())
        row.update(FLAGS)
        row["row_hash"] = stable_hash({k: v for k, v in row.items() if k != "row_hash"})
        return row


@dataclass(frozen=True)
class ScanPoint:
    nu: float
    omega: float
    delta_factor: float

    def as_row(self) -> dict[str, Any]:
        omega_log_omega = self.omega * math.log(self.omega)
        delta_eq = self.nu / omega_log_omega
        delta = self.delta_factor * delta_eq
        delta_dot = width_delta_dot(self.nu, self.omega, delta)
        sign = sign_label(delta_dot)
        expected_sign = expected_sign_from_factor(self.delta_factor)
        row = {
            **base_fields(),
            **FLAGS,
            "row_kind": "parameter_scan",
            "nu": rounded(self.nu),
            "Omega": rounded(self.omega),
            "log_Omega": rounded(math.log(self.omega)),
            "Omega_log_Omega": rounded(omega_log_omega),
            "delta_factor_relative_to_eq": rounded(self.delta_factor),
            "delta_eq": rounded(delta_eq),
            "delta": rounded(delta),
            "delta_dot": rounded(delta_dot),
            "delta_dot_sign": sign,
            "expected_sign_relative_to_equilibrium": expected_sign,
            "sign_matches_equilibrium_rule": sign == expected_sign,
            "equilibrium_relation": classify_relative_to_eq(self.delta_factor),
            "ode_formula": ODE_FORMULA,
            "equilibrium_formula": EQUILIBRIUM_FORMULA,
        }
        row["row_hash"] = stable_hash({k: v for k, v in row.items() if k != "row_hash"})
        return row


@dataclass(frozen=True)
class SubcriticalProjection:
    beta: float
    omega0: float
    t: float

    def as_row(self) -> dict[str, Any]:
        omega = omega_subcritical_solution(self.omega0, self.beta, self.t)
        omega_dot = -self.beta * omega * math.log(omega)
        row = {
            **base_fields(),
            **FLAGS,
            "row_kind": "subcritical_omega_projection",
            "projection_status": "conditional_evidence_only",
            "Omega_ode": "Omega_dot = -beta*Omega*log(Omega)",
            "beta": rounded(self.beta),
            "beta_positive": self.beta > 0.0,
            "t": rounded(self.t),
            "Omega0": rounded(self.omega0),
            "Omega_projected": rounded(omega),
            "Omega_dot_projected": rounded(omega_dot),
            "log_Omega_projected": rounded(math.log(omega)),
            "subcritical_trend": "decreases_toward_1_from_above",
            "conditional_inputs": [
                "beta-positive depletion coefficient assumed",
                "closed scalar Omega projection assumed",
                "localized enstrophy projection not proved from full NS",
            ],
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
        "model_name": MODEL_NAME,
    }


def rounded(value: float) -> float:
    return round(value, 12)


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


def width_delta_dot(nu: float, omega: float, delta: float) -> float:
    return -omega * math.log(omega) + nu / delta


def sign_label(value: float) -> str:
    if abs(value) <= 1.0e-11:
        return "zero"
    return "positive" if value > 0.0 else "negative"


def expected_sign_from_factor(delta_factor: float) -> str:
    if abs(delta_factor - 1.0) <= 1.0e-12:
        return "zero"
    return "positive" if delta_factor < 1.0 else "negative"


def classify_relative_to_eq(delta_factor: float) -> str:
    if abs(delta_factor - 1.0) <= 1.0e-12:
        return "at_equilibrium"
    return "below_equilibrium" if delta_factor < 1.0 else "above_equilibrium"


def omega_subcritical_solution(omega0: float, beta: float, t: float) -> float:
    # Solves d(log Omega)/dt = -beta log Omega for Omega0 > 1, beta > 0.
    return math.exp(math.log(omega0) * math.exp(-beta * t))


def build_derivation_rows() -> list[dict[str, Any]]:
    steps = [
        DerivationStep(
            "localized_stretching_log_amplification",
            "localized enstrophy stretching concentration term",
            "Omega log(Omega)",
            "compressive",
            "-Omega*log(Omega)",
            "reduced_model_basis_recorded",
            "conditional_not_extracted_from_full_ns",
            "Represents the model-side inward width drift from logarithmic amplification.",
        ),
        DerivationStep(
            "localized_viscous_width_relaxation",
            "localized viscous diffusion across width delta",
            "nu/delta",
            "expansive",
            "+nu/delta",
            "reduced_model_basis_recorded",
            "conditional_not_extracted_from_full_ns",
            "Represents the outward width relaxation supplied by viscosity.",
        ),
        DerivationStep(
            "scalar_balance_width_ode",
            "stretching-viscosity reduced balance",
            "dot(delta)",
            "signed_balance",
            ODE_FORMULA,
            "algebraic_model_balance_supported",
            "not_a_navier_stokes_theorem",
            "Combines the two localized terms into the scalar width ODE.",
        ),
        DerivationStep(
            "equilibrium_balance",
            "zero drift width balance",
            EQUILIBRIUM_FORMULA,
            "neutral",
            "dot(delta)=0 iff delta=nu/(Omega*log(Omega)) for Omega>1",
            "equilibrium_model_supported",
            "conditional_reduced_model_statement",
            "The parameter scan checks signs below, at, and above this equilibrium.",
        ),
    ]
    return [step.as_row() for step in steps]


def build_scan_rows() -> list[dict[str, Any]]:
    nus = [0.005, 0.02, 0.08]
    omegas = [1.25, 2.0, 5.0, 12.0]
    delta_factors = [0.5, 0.9, 1.0, 1.2, 2.0]
    return [
        ScanPoint(nu=nu, omega=omega, delta_factor=factor).as_row()
        for nu in nus
        for omega in omegas
        for factor in delta_factors
    ]


def build_subcritical_rows() -> list[dict[str, Any]]:
    betas = [0.05, 0.2, 0.75]
    omega0s = [1.5, 4.0, 10.0]
    times = [0.0, 1.0, 4.0, 10.0]
    return [
        SubcriticalProjection(beta=beta, omega0=omega0, t=t).as_row()
        for beta in betas
        for omega0 in omega0s
        for t in times
    ]


def validate(derivation_rows: list[dict[str, Any]], scan_rows: list[dict[str, Any]], subcritical_rows: list[dict[str, Any]]) -> None:
    required_flags = {
        "width_ode_extracted_from_ns": False,
        "equilibrium_model_supported": True,
        "subcritical_ode_conditional": True,
        "bkm_finite": False,
        "full_clay_ns_solved": False,
    }
    for collection_name, rows in [
        ("derivation", derivation_rows),
        ("scan", scan_rows),
        ("subcritical", subcritical_rows),
    ]:
        if not rows:
            raise ValueError(f"{collection_name} rows are empty")
        for row in rows:
            for key, expected in required_flags.items():
                if row.get(key) is not expected:
                    raise ValueError(f"{collection_name} row {row.get('row_hash')} has invalid {key}")

    if len(derivation_rows) != 4:
        raise ValueError("expected exactly four derivation rows")

    for row in scan_rows:
        if row["nu"] <= 0.0 or row["Omega"] <= 1.0 or row["delta"] <= 0.0:
            raise ValueError(f"invalid positive scan parameters in {row}")
        if not row["sign_matches_equilibrium_rule"]:
            raise ValueError(f"equilibrium sign rule failed in {row}")

    for row in subcritical_rows:
        if not row["beta_positive"]:
            raise ValueError(f"subcritical row lacks beta > 0: {row}")
        if row["Omega_projected"] < 1.0:
            raise ValueError(f"subcritical projection crossed below Omega=1: {row}")
        if row["Omega_dot_projected"] > 1.0e-11:
            raise ValueError(f"subcritical projection has positive Omega_dot: {row}")


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
            encoded = {
                key: json.dumps(value, sort_keys=True) if isinstance(value, (list, dict)) else value
                for key, value in row.items()
            }
            writer.writerow(encoded)


def build_summary(derivation_rows: list[dict[str, Any]], scan_rows: list[dict[str, Any]], subcritical_rows: list[dict[str, Any]]) -> dict[str, Any]:
    sign_counts: dict[str, int] = {}
    for row in scan_rows:
        sign_counts[row["delta_dot_sign"]] = sign_counts.get(row["delta_dot_sign"], 0) + 1

    return {
        **base_fields(),
        **FLAGS,
        "control_card": CONTROL_CARD,
        "ode_formula": ODE_FORMULA,
        "equilibrium_formula": EQUILIBRIUM_FORMULA,
        "derivation_row_count": len(derivation_rows),
        "scan_row_count": len(scan_rows),
        "subcritical_projection_row_count": len(subcritical_rows),
        "scan_sign_counts": sign_counts,
        "all_scan_signs_match_equilibrium_rule": all(
            row["sign_matches_equilibrium_rule"] for row in scan_rows
        ),
        "nu_values": sorted({row["nu"] for row in scan_rows}),
        "Omega_values": sorted({row["Omega"] for row in scan_rows}),
        "delta_factors": sorted({row["delta_factor_relative_to_eq"] for row in scan_rows}),
        "beta_values": sorted({row["beta"] for row in subcritical_rows}),
        "Omega0_values": sorted({row["Omega0"] for row in subcritical_rows}),
        "theorem_flags_fail_closed": True,
        "evidence_only": True,
        "ledger_hash": stable_hash(
            {
                "derivation_rows": derivation_rows,
                "scan_rows": scan_rows,
                "subcritical_rows": subcritical_rows,
                "flags": FLAGS,
            }
        ),
    }


def build_report(summary: dict[str, Any]) -> str:
    lines = [
        f"# Sprint {SPRINT} Width ODE Extraction Evidence Ledger",
        "",
        f"- Contract: `{CONTRACT}`",
        f"- Formula: `{ODE_FORMULA}`",
        f"- Equilibrium: `{EQUILIBRIUM_FORMULA}` for `Omega > 1`",
        f"- Derivation rows: {summary['derivation_row_count']}",
        f"- Scan rows: {summary['scan_row_count']}",
        f"- Subcritical projection rows: {summary['subcritical_projection_row_count']}",
        f"- Scan sign counts: `{summary['scan_sign_counts']}`",
        "",
        "## Flags",
    ]
    for key, value in FLAGS.items():
        lines.append(f"- `{key}`: `{str(value).lower()}`")
    lines.extend(["", "## O/R/C/S/L/P/G/F"])
    for key in ["O", "R", "C", "S", "L", "P", "G", "F"]:
        lines.append(f"- **{key}**: {CONTROL_CARD[key]}")
    lines.extend(
        [
            "",
            "## Boundary",
            "",
            "This artifact supports only the reduced equilibrium model and a "
            "conditional beta-positive subcritical projection. It does not "
            "extract the width ODE from the full Navier-Stokes equations, does "
            "not prove BKM finiteness, and does not solve the Clay problem.",
            "",
        ]
    )
    return "\n".join(lines)


def emit(repo_root: Path, out_dir: Path) -> dict[str, Any]:
    repo_root = repo_root.resolve()
    out_dir = out_dir if out_dir.is_absolute() else repo_root / out_dir
    derivation_rows = build_derivation_rows()
    scan_rows = build_scan_rows()
    subcritical_rows = build_subcritical_rows()
    validate(derivation_rows, scan_rows, subcritical_rows)
    summary = build_summary(derivation_rows, scan_rows, subcritical_rows)

    parent = out_dir.parent
    parent.mkdir(parents=True, exist_ok=True)
    tmp_dir = Path(tempfile.mkdtemp(prefix=out_dir.name + ".", dir=parent))
    try:
        write_json(tmp_dir / DERIVATION_JSON_NAME, derivation_rows)
        write_csv(tmp_dir / DERIVATION_CSV_NAME, derivation_rows)
        write_json(tmp_dir / SCAN_JSON_NAME, scan_rows)
        write_csv(tmp_dir / SCAN_CSV_NAME, scan_rows)
        write_json(tmp_dir / SUBCRITICAL_JSON_NAME, subcritical_rows)
        write_csv(tmp_dir / SUBCRITICAL_CSV_NAME, subcritical_rows)
        write_json(tmp_dir / SUMMARY_NAME, summary)
        (tmp_dir / REPORT_NAME).write_text(build_report(summary), encoding="utf-8")

        manifest_files = sorted(
            path.name for path in tmp_dir.iterdir() if path.is_file() and path.name != MANIFEST_NAME
        )
        manifest = {
            **base_fields(),
            "output_dir": display_path(out_dir, repo_root),
            "files": [
                {
                    "path": display_path(tmp_dir / name, repo_root).replace(tmp_dir.name, out_dir.name),
                    "sha256": file_sha256(tmp_dir / name),
                }
                for name in manifest_files
            ],
            "manifest_hash": stable_hash({"files": manifest_files, "summary": summary}),
        }
        write_json(tmp_dir / MANIFEST_NAME, manifest)

        if out_dir.exists():
            shutil.rmtree(out_dir)
        tmp_dir.rename(out_dir)
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
                "scan_rows": summary["scan_row_count"],
                "subcritical_projection_rows": summary["subcritical_projection_row_count"],
                "flags": {key: summary[key] for key in FLAGS},
                "ledger_hash": summary["ledger_hash"],
            },
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
