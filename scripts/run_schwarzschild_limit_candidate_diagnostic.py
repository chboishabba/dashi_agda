#!/usr/bin/env python3
"""Fail-closed Schwarzschild limit candidate diagnostic.

This script records the minimal Schwarzschild-radius sanity surface

    r_s = 2 G_N M / c^2

and only performs numeric candidate checks when the required in-repo or
explicit CLI inputs are present.  It does not promote any physics lane.
"""

from __future__ import annotations

import argparse
import json
import math
import re
from dataclasses import dataclass
from pathlib import Path
from typing import Any


DEFAULT_OUTPUT = Path("scripts/data/outputs/schwarzschild_limit_candidate_diagnostic.json")
DEFAULT_INPUTS = [
    Path("scripts/data/schwarzschild_limit_candidate_inputs.json"),
    Path("scripts/data/physics_constants.json"),
    Path("scripts/data/authority_packet.example.json"),
]

# Exact SI value since the 1983 metre definition.
SPEED_OF_LIGHT_M_PER_S = 299_792_458.0

REQUIRED_NUMERIC_INPUTS = [
    "gravitational_constant_G_N_m3_kg_minus1_s_minus2",
    "source_mass_M_kg",
    "source_radius_R_m",
]

REQUIRED_CANDIDATE_INPUTS = [
    "einstein_tensor_G00_at_k_eq_1_SI",
    "stress_energy_T00_at_k_eq_1_SI",
    "acceptance_relative_tolerance",
    "units",
]

SEARCH_PATTERNS = {
    "Schwarzschild": re.compile(r"\bSchwarzschild\b", re.IGNORECASE),
    "G_N": re.compile(r"\bG_N\b|\bNewton(?:ian)?\b|\bgravitational_constant\b", re.IGNORECASE),
    "weak_field": re.compile(r"weak[-_ ]field|weak field", re.IGNORECASE),
    "k_eq_1": re.compile(r"\bk\s*=\s*1\b|\bk_eq_1\b|\bk=1\b", re.IGNORECASE),
}


@dataclass(frozen=True)
class CandidateInputs:
    gravitational_constant: float | None
    source_mass: float | None
    source_radius: float | None
    radial_probe: float | None
    g00: float | None
    t00: float | None
    acceptance_relative_tolerance: float | None
    units: str | None
    weak_field_formula: str | None
    g_n_ratio_at_k_eq_1: float | None
    provenance: dict[str, Any]


def finite_positive(value: Any) -> float | None:
    if isinstance(value, bool):
        return None
    try:
        number = float(value)
    except (TypeError, ValueError):
        return None
    if math.isfinite(number) and number > 0.0:
        return number
    return None


def finite_number(value: Any) -> float | None:
    if isinstance(value, bool):
        return None
    try:
        number = float(value)
    except (TypeError, ValueError):
        return None
    if math.isfinite(number):
        return number
    return None


def load_json_object(path: Path) -> dict[str, Any] | None:
    if not path.exists() or not path.is_file():
        return None
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return None
    return payload if isinstance(payload, dict) else None


def first_present_float(payload: dict[str, Any], keys: list[str]) -> tuple[float | None, str | None]:
    for key in keys:
        value = finite_positive(payload.get(key))
        if value is not None:
            return value, key
    return None, None


def first_present_number(payload: dict[str, Any], keys: list[str]) -> tuple[float | None, str | None]:
    for key in keys:
        value = finite_number(payload.get(key))
        if value is not None:
            return value, key
    return None, None


def first_present_string(payload: dict[str, Any], keys: list[str]) -> tuple[str | None, str | None]:
    for key in keys:
        value = payload.get(key)
        if isinstance(value, str) and value.strip():
            return value.strip(), key
    return None, None


def collect_inputs(input_paths: list[Path]) -> CandidateInputs:
    provenance: dict[str, Any] = {"input_files": []}
    merged: dict[str, Any] = {}
    key_sources: dict[str, str] = {}

    for path in input_paths:
        payload = load_json_object(path)
        record = {
            "path": str(path),
            "present": path.exists(),
            "json_object_loaded": payload is not None,
        }
        provenance["input_files"].append(record)
        if payload is None:
            continue
        for key, value in payload.items():
            if key not in merged:
                merged[key] = value
                key_sources[key] = str(path)

    g_n, g_n_key = first_present_float(
        merged,
        [
            "gravitational_constant_G_N_m3_kg_minus1_s_minus2",
            "G_N",
            "G",
            "newton_gravitational_constant",
        ],
    )
    mass, mass_key = first_present_float(merged, ["source_mass_M_kg", "M_kg", "mass_kg"])
    source_radius, source_radius_key = first_present_float(
        merged,
        ["source_radius_R_m", "source_radius_m", "R_m", "radius_m"],
    )
    radial_probe, radial_probe_key = first_present_float(merged, ["radial_probe_r_m", "r_m"])
    g00, g00_key = first_present_number(
        merged,
        ["einstein_tensor_G00_at_k_eq_1_SI", "G00_at_k_eq_1", "G00"],
    )
    t00, t00_key = first_present_number(
        merged,
        ["stress_energy_T00_at_k_eq_1_SI", "T00_at_k_eq_1", "T00"],
    )
    tolerance, tolerance_key = first_present_float(
        merged,
        ["acceptance_relative_tolerance", "relative_tolerance", "rtol"],
    )
    units, units_key = first_present_string(merged, ["units", "unit_system"])
    weak_formula, weak_formula_key = first_present_string(
        merged,
        ["candidate_weak_field_factor_formula", "weak_field_factor_formula"],
    )
    ratio, ratio_key = first_present_float(
        merged,
        ["candidate_G_N_ratio_at_k_eq_1", "G_N_ratio_at_k_eq_1", "g_n_ratio_k1"],
    )

    provenance["resolved_keys"] = {
        "gravitational_constant_G_N_m3_kg_minus1_s_minus2": {
            "key": g_n_key,
            "source": key_sources.get(g_n_key) if g_n_key else None,
        },
        "source_mass_M_kg": {
            "key": mass_key,
            "source": key_sources.get(mass_key) if mass_key else None,
        },
        "source_radius_R_m": {
            "key": source_radius_key,
            "source": key_sources.get(source_radius_key) if source_radius_key else None,
        },
        "radial_probe_r_m": {
            "key": radial_probe_key,
            "source": key_sources.get(radial_probe_key) if radial_probe_key else None,
        },
        "einstein_tensor_G00_at_k_eq_1_SI": {
            "key": g00_key,
            "source": key_sources.get(g00_key) if g00_key else None,
        },
        "stress_energy_T00_at_k_eq_1_SI": {
            "key": t00_key,
            "source": key_sources.get(t00_key) if t00_key else None,
        },
        "acceptance_relative_tolerance": {
            "key": tolerance_key,
            "source": key_sources.get(tolerance_key) if tolerance_key else None,
        },
        "units": {
            "key": units_key,
            "source": key_sources.get(units_key) if units_key else None,
        },
        "candidate_weak_field_factor_formula": {
            "key": weak_formula_key,
            "source": key_sources.get(weak_formula_key) if weak_formula_key else None,
        },
        "candidate_G_N_ratio_at_k_eq_1": {
            "key": ratio_key,
            "source": key_sources.get(ratio_key) if ratio_key else None,
        },
    }

    return CandidateInputs(
        gravitational_constant=g_n,
        source_mass=mass,
        source_radius=source_radius,
        radial_probe=radial_probe,
        g00=g00,
        t00=t00,
        acceptance_relative_tolerance=tolerance,
        units=units,
        weak_field_formula=weak_formula,
        g_n_ratio_at_k_eq_1=ratio,
        provenance=provenance,
    )


def bounded_repo_signal_scan(repo_root: Path) -> dict[str, Any]:
    roots = [repo_root / "README.md", repo_root / "TODO.md", repo_root / "status.md", repo_root / "devlog.md", repo_root / "DASHI", repo_root / "scripts"]
    matches: dict[str, list[dict[str, Any]]] = {key: [] for key in SEARCH_PATTERNS}
    files_scanned = 0
    files_skipped = 0

    def candidate_files() -> list[Path]:
        files: list[Path] = []
        for root in roots:
            if root.is_file():
                files.append(root)
            elif root.is_dir():
                files.extend(path for path in root.rglob("*") if path.is_file())
        return sorted(set(files))

    for path in candidate_files():
        rel = path.relative_to(repo_root)
        if any(part in {"__pycache__", "data", "pdf"} for part in rel.parts):
            files_skipped += 1
            continue
        if path.suffix not in {".agda", ".md", ".py", ".json", ".txt"}:
            files_skipped += 1
            continue
        try:
            text = path.read_text(encoding="utf-8")
        except UnicodeDecodeError:
            files_skipped += 1
            continue
        files_scanned += 1
        for name, pattern in SEARCH_PATTERNS.items():
            if len(matches[name]) >= 12:
                continue
            for line_number, line in enumerate(text.splitlines(), start=1):
                if pattern.search(line):
                    matches[name].append(
                        {
                            "path": str(rel),
                            "line": line_number,
                            "excerpt": line.strip()[:180],
                        }
                    )
                    break

    return {
        "scope": "bounded text scan of README/TODO/status/devlog/DASHI/scripts excluding scripts/data and pdf caches",
        "files_scanned": files_scanned,
        "files_skipped": files_skipped,
        "matches": matches,
    }


def formal_agda_surface_observation(repo_root: Path) -> dict[str, Any]:
    path = repo_root / "DASHI/Physics/Closure/SchwarzschildLimitCandidate.agda"
    observation: dict[str, Any] = {
        "path": str(path.relative_to(repo_root)),
        "present": path.exists(),
        "status": "not_inspected",
        "first_missing": None,
        "exact_missing_primitives": [],
        "missing_surface_fields": [],
        "boundary": None,
    }
    if not path.exists():
        observation["status"] = "absent"
        return observation

    text = path.read_text(encoding="utf-8")
    primitive_names = [
        "missingRadialValuation",
        "missingSphericalSymmetryPredicate",
        "missingW4MassSource",
        "missingBirkhoffCarrierProof",
        "missingWeakFieldNewtonianPotential",
        "missingSchwarzschildMetricMatch",
    ]
    observation["exact_missing_primitives"] = [name for name in primitive_names if name in text]

    first_missing_match = re.search(r"; firstMissing\s*=\s*(missing[A-Za-z0-9_]+)", text)
    if first_missing_match:
        observation["first_missing"] = first_missing_match.group(1)

    missing_fields: list[str] = []
    in_missing_surface = False
    for line in text.splitlines():
        stripped = line.strip()
        if stripped.startswith("; missingSurface"):
            in_missing_surface = True
            continue
        if in_missing_surface and stripped.startswith("; unsupportedClaims"):
            break
        if in_missing_surface and '"' in stripped:
            missing_fields.append(stripped.split('"', 2)[1])
    observation["missing_surface_fields"] = missing_fields

    observation["boundary"] = (
        "request-only; no non-flat metric, W4 mass source, weak-field Newtonian limit, "
        "or Schwarzschild metric match is constructed in the Agda surface"
    )
    observation["status"] = "request_surface_only_no_numeric_inputs"
    return observation


def build_payload(repo_root: Path, input_paths: list[Path]) -> dict[str, Any]:
    inputs = collect_inputs(input_paths)
    missing_numeric = [
        key
        for key, value in {
            "gravitational_constant_G_N_m3_kg_minus1_s_minus2": inputs.gravitational_constant,
            "source_mass_M_kg": inputs.source_mass,
            "source_radius_R_m": inputs.source_radius,
        }.items()
        if value is None
    ]
    missing_candidate = [
        key
        for key, value in {
            "einstein_tensor_G00_at_k_eq_1_SI": inputs.g00,
            "stress_energy_T00_at_k_eq_1_SI": inputs.t00,
            "acceptance_relative_tolerance": inputs.acceptance_relative_tolerance,
            "units": inputs.units,
        }.items()
        if value is None or value == ""
    ]

    numeric_possible = not missing_numeric
    schwarzschild_radius = None
    compactness = None
    weak_field_factor_standard = None
    if numeric_possible:
        assert inputs.gravitational_constant is not None
        assert inputs.source_mass is not None
        assert inputs.source_radius is not None
        schwarzschild_radius = (
            2.0
            * inputs.gravitational_constant
            * inputs.source_mass
            / (SPEED_OF_LIGHT_M_PER_S * SPEED_OF_LIGHT_M_PER_S)
        )
        compactness = schwarzschild_radius / inputs.source_radius
        weak_field_factor_standard = 1.0 - compactness

    g_n_candidate = None
    g_n_ratio_check = None
    g_n_candidate_possible = not missing_candidate and inputs.t00 not in (None, 0.0)
    if g_n_candidate_possible:
        assert inputs.g00 is not None
        assert inputs.t00 is not None
        assert inputs.gravitational_constant is not None
        assert inputs.acceptance_relative_tolerance is not None
        g_n_candidate = inputs.g00 / (8.0 * math.pi * inputs.t00)
        ratio = g_n_candidate / inputs.gravitational_constant
        relative_difference = abs(ratio - 1.0)
        g_n_ratio_check = {
            "computed": True,
            "G_N_candidate_m3_kg_minus1_s_minus2": g_n_candidate,
            "G_N_candidate_over_reference_G_N": ratio,
            "expected_reference_ratio": 1.0,
            "relative_difference_from_reference": relative_difference,
            "acceptance_relative_tolerance": inputs.acceptance_relative_tolerance,
            "accepted": relative_difference <= inputs.acceptance_relative_tolerance,
        }
    elif inputs.t00 == 0.0:
        missing_candidate.append("nonzero_stress_energy_T00_at_k_eq_1_SI")

    candidate_ratio_check = None
    if inputs.g_n_ratio_at_k_eq_1 is not None:
        candidate_ratio_check = {
            "candidate_G_N_ratio_at_k_eq_1": inputs.g_n_ratio_at_k_eq_1,
            "expected_reference_ratio": 1.0,
            "absolute_difference": abs(inputs.g_n_ratio_at_k_eq_1 - 1.0),
            "passes_exact_float_equality": inputs.g_n_ratio_at_k_eq_1 == 1.0,
        }

    status = "fail_closed_missing_inputs" if missing_numeric or missing_candidate else "computed_non_promoting"
    return {
        "artifact": "schwarzschild_limit_candidate_diagnostic",
        "status": status,
        "promotion_status": "diagnostic_only_no_proof_no_gate_promotion",
        "repo_root": str(repo_root),
        "constants_recorded": {
            "speed_of_light_m_per_s": SPEED_OF_LIGHT_M_PER_S,
            "speed_of_light_status": "exact_SI_definition",
        },
        "required_inputs": {
            "numeric": REQUIRED_NUMERIC_INPUTS,
            "candidate": REQUIRED_CANDIDATE_INPUTS,
        },
        "input_schema": {
            "gravitational_constant_G_N_m3_kg_minus1_s_minus2": {
                "description": "Reference Newton gravitational constant used for the k=1 ratio check.",
                "required": True,
                "unit": "m^3 kg^-1 s^-2",
            },
            "einstein_tensor_G00_at_k_eq_1_SI": {
                "description": "G00 component evaluated at k=1 in the same convention as 8*pi*G_N*T00.",
                "required": True,
                "unit": "s^-2 or convention-equivalent SI curvature density",
            },
            "stress_energy_T00_at_k_eq_1_SI": {
                "description": "T00 component evaluated at k=1; must be finite and nonzero.",
                "required": True,
                "unit": "kg m^-1 s^-2 or convention-equivalent SI energy density",
            },
            "acceptance_relative_tolerance": {
                "description": "Maximum accepted absolute relative difference between G_N_candidate / G_N and 1.",
                "required": True,
                "unit": "dimensionless",
            },
            "units": {
                "description": "Explicit unit convention for G00, T00, G_N, source mass, and source radius.",
                "required": True,
                "accepted_value": "SI",
            },
            "source_mass_M_kg": {
                "description": "Mass source used for the Schwarzschild sanity check.",
                "required": True,
                "unit": "kg",
            },
            "source_radius_R_m": {
                "description": "Source radius used as the Schwarzschild radial scale.",
                "required": True,
                "unit": "m",
            },
        },
        "missing_inputs": {
            "numeric": missing_numeric,
            "candidate": missing_candidate,
        },
        "input_resolution": inputs.provenance,
        "symbolic_sanity": {
            "schwarzschild_radius_formula": "r_s = 2 * G_N * M / c^2",
            "compactness_formula": "epsilon = r_s / R",
            "standard_schwarzschild_g_tt_weak_field_factor": "1 - r_s / r = 1 - 2 * G_N * M / (c^2 * r)",
            "G_N_candidate_formula": "G_N_candidate = G00 / (8 * pi * T00)",
            "G_N_ratio_formula_at_k_eq_1": "G_N_candidate_over_reference_G_N = G_N_candidate / G_N",
            "numeric_evaluation_policy": "only evaluated when G_N, M, and R are present as positive finite inputs",
            "candidate_formula_policy": "candidate G_N ratio is computed only from explicit G00, T00, G_N, acceptance, and units input keys",
        },
        "G_N_candidate_schema": {
            "formula": "G_N_candidate = G00 / (8 * pi * T00)",
            "ratio_formula_at_k_eq_1": "G_N_candidate / G_N",
            "acceptance_rule": "abs((G_N_candidate / G_N) - 1) <= acceptance_relative_tolerance",
            "fail_closed_policy": "no G_N candidate or acceptance claim is computed unless all required inputs are resolved",
            "computed": bool(g_n_ratio_check and g_n_ratio_check["computed"]),
            "result": g_n_ratio_check,
        },
        "numeric_sanity": {
            "computed": numeric_possible,
            "schwarzschild_radius_m": schwarzschild_radius,
            "compactness_r_s_over_r": compactness,
            "standard_weak_field_factor_1_minus_r_s_over_r": weak_field_factor_standard,
            "radial_probe_outside_schwarzschild_radius": (
                bool(inputs.source_radius is not None and schwarzschild_radius is not None and inputs.source_radius > schwarzschild_radius)
                if numeric_possible
                else None
            ),
        },
        "candidate_checks": {
            "weak_field_factor_formula": inputs.weak_field_formula,
            "G_N_ratio_at_k_eq_1": candidate_ratio_check,
        },
        "formal_agda_surface_observation": formal_agda_surface_observation(repo_root),
        "repo_signal_scan": bounded_repo_signal_scan(repo_root),
        "interpretation": [
            "This artifact is a deterministic scaffold for the Schwarzschild limit candidate.",
            "It does not invent missing physical calibration data or a repo-local candidate formula.",
            "A fail-closed status means numeric Schwarzschild or k=1 G_N-ratio claims are intentionally not made.",
        ],
    }


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Run a fail-closed Schwarzschild candidate diagnostic")
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument(
        "--input",
        type=Path,
        action="append",
        default=[],
        help="Optional JSON input file. Earlier files win for duplicated keys.",
    )
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    repo_root = Path(__file__).resolve().parents[1]
    input_paths = [path if path.is_absolute() else repo_root / path for path in args.input]
    input_paths.extend(repo_root / path for path in DEFAULT_INPUTS)
    payload = build_payload(repo_root, input_paths)
    output = args.output if args.output.is_absolute() else repo_root / args.output
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps(payload, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
