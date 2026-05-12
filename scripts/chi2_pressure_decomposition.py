#!/usr/bin/env python3
"""Non-promoting DY chi2 pressure-domain decomposition.

This tool consumes existing comparison artifacts when present and separates the
observed pressure into convention/bin-normalization, PDF, model, and
efficiency/acceptance domains only as far as local evidence permits. It fails
closed when the accepted DY convention authority or W4 fields are absent.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import re
import sys
from pathlib import Path
from typing import Any


EXIT_OK = 0
EXIT_BLOCKED = 45
EXIT_INPUT_ERROR = 46

ACCEPTED_STATUSES = {"accepted", "replacement"}
ABSENT_STRINGS = {"", "missing", "insufficient", "unknown", "none", "null"}
NEGATIVE_AUTHORITY_MARKERS = (
    "no accepted convention",
    "not an accepted authority",
    "not accepted",
    "cannot provide authority",
    "no convention or luminosity value is accepted",
)

REQUIRED_PROVIDER_FIELDS = (
    "provider_name",
    "provider_role",
    "pdf_set_version",
    "lhapdf_id",
    "member_id",
    "grid_checksum",
    "scale_convention",
    "rapidity_window",
    "mass_bin_rule",
    "flavour_weight_rule",
    "integration_method",
    "luminosity_values",
    "efficiency_acceptance_model",
    "systematic_budget",
    "cms_smp_publication_pointer",
    "normalization_preservation_law",
    "conversion_law",
    "source_citation",
    "attestation_no_manual_overfit",
)

RUNNER_CONVERSION_FIELDS = (
    "L43",
    "L45",
    "W4_per_bin_luminosities",
)

FIELD_GROUPS = {
    "provider_identity": (
        "provider_name",
        "provider_role",
        "source_citation",
        "attestation_no_manual_overfit",
    ),
    "pdf_authority": (
        "pdf_set_version",
        "lhapdf_id",
        "member_id",
        "grid_checksum",
    ),
    "dy_convention": (
        "scale_convention",
        "rapidity_window",
        "mass_bin_rule",
        "flavour_weight_rule",
        "integration_method",
    ),
    "luminosity_runner_inputs": (
        "luminosity_values",
        "L43",
        "L45",
        "W4_per_bin_luminosities",
    ),
    "normalization_conversion": (
        "normalization_preservation_law",
        "conversion_law",
    ),
    "efficiency_acceptance": (
        "efficiency_acceptance_model",
        "systematic_budget",
        "cms_smp_publication_pointer",
    ),
}

FIELD_TO_GROUP = {
    field: group
    for group, fields in FIELD_GROUPS.items()
    for field in fields
}


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def stable_digest(payload: Any) -> str:
    encoded = json.dumps(payload, sort_keys=True, separators=(",", ":")).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def load_json(path: Path) -> dict[str, Any]:
    with path.open("r", encoding="utf-8") as handle:
        payload = json.load(handle)
    if not isinstance(payload, dict):
        raise ValueError(f"{path}: JSON root must be an object")
    return payload


def absentish(value: Any) -> bool:
    if value is None:
        return True
    if isinstance(value, str):
        return value.strip().lower() in ABSENT_STRINGS
    if isinstance(value, list):
        return len(value) == 0
    return False


def field_status(value: Any) -> str:
    if absentish(value):
        return "missing"
    if isinstance(value, str) and any(marker in value.strip().lower() for marker in NEGATIVE_AUTHORITY_MARKERS):
        return "negative-authority-marker"
    return "present"


def group_missing(fields: list[str]) -> dict[str, list[str]]:
    grouped: dict[str, list[str]] = {group: [] for group in FIELD_GROUPS}
    grouped["other"] = []
    for field in fields:
        grouped.setdefault(FIELD_TO_GROUP.get(field, "other"), []).append(field)
    return {group: values for group, values in grouped.items() if values}


def choose_authority_payload(packet: dict[str, Any]) -> dict[str, Any]:
    for key in (
        "authority_response",
        "accepted_dy_luminosity_convention_authority",
        "accepted_dy_luminosity_convention",
        "authority",
    ):
        value = packet.get(key)
        if isinstance(value, dict):
            merged = dict(value)
            if "status" not in merged and "status" in packet:
                merged["status"] = packet["status"]
            return merged
    return packet


def first_present(mapping: dict[str, Any], keys: tuple[str, ...]) -> Any:
    for key in keys:
        if key in mapping:
            return mapping[key]
    return None


def finite_positive(value: Any) -> bool:
    if isinstance(value, bool):
        return False
    try:
        number = float(value)
    except (TypeError, ValueError):
        return False
    return math.isfinite(number) and number > 0.0


def positive_diagnostic(value: Any) -> dict[str, Any]:
    return {
        "raw": value,
        "present": not absentish(value),
        "positiveFinite": finite_positive(value),
    }


def w4_luminosity_diagnostic(value: Any) -> dict[str, Any]:
    if not isinstance(value, list):
        return {
            "present": not absentish(value),
            "count": 0,
            "positiveFiniteCount": 0,
            "allPositiveFinite": False,
            "shape": type(value).__name__,
        }
    positive_count = 0
    for item in value:
        candidate = item.get("luminosity", item) if isinstance(item, dict) else item
        if finite_positive(candidate):
            positive_count += 1
    return {
        "present": bool(value),
        "count": len(value),
        "positiveFiniteCount": positive_count,
        "allPositiveFinite": bool(value) and positive_count == len(value),
        "shape": "list",
    }


def inspect_authority(path: Path | None) -> dict[str, Any]:
    all_missing = list(REQUIRED_PROVIDER_FIELDS) + list(RUNNER_CONVERSION_FIELDS)
    if path is None:
        return {
            "path": None,
            "present": False,
            "accepted": False,
            "status": "missing",
            "missingFields": all_missing,
            "missingByGroup": group_missing(all_missing),
            "negativeAuthorityMarkerFields": [],
            "providerDeclaredMissingFields": [],
            "fieldDiagnostics": [
                {"field": field, "group": FIELD_TO_GROUP.get(field, "other"), "status": "missing"}
                for field in all_missing
            ],
            "runnerLuminosityDiagnostics": {
                "L43": positive_diagnostic(None),
                "L45": positive_diagnostic(None),
                "W4_per_bin_luminosities": w4_luminosity_diagnostic(None),
            },
            "authorityGate": {
                "statusAcceptedOrReplacement": False,
                "requiredFieldsPresent": False,
                "negativeAuthorityMarkersAbsent": True,
                "accepted": False,
                "acceptedFalseReasons": ["authorityPacketMissing", "requiredFieldsMissing"],
                "firstMissing": all_missing[0],
                "firstMissingGroup": FIELD_TO_GROUP.get(all_missing[0], "other"),
                "blockedExitCode": EXIT_BLOCKED,
            },
            "sha256": None,
        }
    if not path.exists():
        return {
            "path": str(path),
            "present": False,
            "accepted": False,
            "status": "missing-file",
            "missingFields": all_missing,
            "missingByGroup": group_missing(all_missing),
            "negativeAuthorityMarkerFields": [],
            "providerDeclaredMissingFields": [],
            "fieldDiagnostics": [
                {"field": field, "group": FIELD_TO_GROUP.get(field, "other"), "status": "missing"}
                for field in all_missing
            ],
            "runnerLuminosityDiagnostics": {
                "L43": positive_diagnostic(None),
                "L45": positive_diagnostic(None),
                "W4_per_bin_luminosities": w4_luminosity_diagnostic(None),
            },
            "authorityGate": {
                "statusAcceptedOrReplacement": False,
                "requiredFieldsPresent": False,
                "negativeAuthorityMarkersAbsent": True,
                "accepted": False,
                "acceptedFalseReasons": ["authorityPacketMissingFile", "requiredFieldsMissing"],
                "firstMissing": all_missing[0],
                "firstMissingGroup": FIELD_TO_GROUP.get(all_missing[0], "other"),
                "blockedExitCode": EXIT_BLOCKED,
            },
            "sha256": None,
        }

    packet = load_json(path)
    authority = choose_authority_payload(packet)
    status = authority.get("status", packet.get("status"))
    field_diagnostics = []
    missing = []
    negative_markers = []
    for field in REQUIRED_PROVIDER_FIELDS:
        value = authority.get(field, packet.get(field))
        status_for_field = field_status(value)
        field_diagnostics.append(
            {
                "field": field,
                "group": FIELD_TO_GROUP.get(field, "other"),
                "status": status_for_field,
            }
        )
        if status_for_field == "missing":
            missing.append(field)
        elif status_for_field == "negative-authority-marker":
            negative_markers.append(field)

    luminosities = packet.get("luminosities") if isinstance(packet.get("luminosities"), dict) else packet
    l43 = first_present(luminosities, ("L43", "L_M43_Y43", "L_50_76", "L_M50_76", "luminosity_43"))
    l45 = first_present(luminosities, ("L45", "L_M45_Y45", "L_106_170", "L_M106_170", "luminosity_45"))
    w4 = first_present(
        luminosities,
        (
            "W4_per_bin",
            "W4_per_bin_luminosities",
            "W4_luminosity_bins",
            "W4_luminosities",
            "L_W4_bins",
            "z_peak_per_bin_luminosities",
        ),
    )
    if not finite_positive(l43):
        missing.append("L43")
    if not finite_positive(l45):
        missing.append("L45")
    if not isinstance(w4, list) or not w4 or not all(finite_positive(item.get("luminosity", item) if isinstance(item, dict) else item) for item in w4):
        missing.append("W4_per_bin_luminosities")

    accepted = status in ACCEPTED_STATUSES and not missing
    accepted_false_reasons = []
    if status not in ACCEPTED_STATUSES:
        accepted_false_reasons.append("statusNotAcceptedOrReplacement")
    if missing:
        accepted_false_reasons.append("requiredFieldsMissing")
    if negative_markers:
        accepted_false_reasons.append("negativeAuthorityMarkerPresent")
        accepted = False

    provider_declared_missing = packet.get("missing_fields", authority.get("missing_fields", []))
    if not isinstance(provider_declared_missing, list):
        provider_declared_missing = [provider_declared_missing]

    return {
        "path": str(path),
        "present": True,
        "accepted": accepted,
        "status": status,
        "missingFields": missing,
        "missingByGroup": group_missing(missing),
        "negativeAuthorityMarkerFields": negative_markers,
        "providerDeclaredMissingFields": provider_declared_missing,
        "fieldDiagnostics": field_diagnostics,
        "runnerLuminosityDiagnostics": {
            "L43": positive_diagnostic(l43),
            "L45": positive_diagnostic(l45),
            "W4_per_bin_luminosities": w4_luminosity_diagnostic(w4),
        },
        "authorityGate": {
            "statusAcceptedOrReplacement": status in ACCEPTED_STATUSES,
            "requiredFieldsPresent": not missing,
            "negativeAuthorityMarkersAbsent": not negative_markers,
            "accepted": accepted,
            "acceptedFalseReasons": accepted_false_reasons,
            "firstMissing": missing[0] if missing else None,
            "firstMissingGroup": FIELD_TO_GROUP.get(missing[0], "other") if missing else None,
            "blockedExitCode": EXIT_BLOCKED if not accepted else None,
        },
        "sha256": sha256_file(path),
    }


def extract_w4_status_doc(path: Path | None) -> dict[str, Any] | None:
    if path is None or not path.exists():
        return None
    text = path.read_text(encoding="utf-8")
    match = re.search(r"chi2/dof\s*\|\s*`([0-9]+(?:\.[0-9]+)?)`", text)
    if match is None:
        match = re.search(r"dirty Z-peak chi2/dof\s*=\s*([0-9]+(?:\.[0-9]+)?)", text)
    if match is None:
        return None
    chi2_per_dof = float(match.group(1))
    return {
        "label": "W4",
        "path": str(path),
        "present": True,
        "required": True,
        "status": "status-doc-observed",
        "missingFields": [],
        "sha256": sha256_file(path),
        "artifactSchema": "markdown-status",
        "comparisonStatus": "dirty-shape-diagnostic-not-accepted-dy-adequacy",
        "chi2": None,
        "chi2PerDof": chi2_per_dof,
        "dof": None,
        "threshold": None,
        "maxAbsPull": None,
        "maxPullBin": None,
    }


def extract_comparison(path: Path | None, *, label: str, required: bool) -> dict[str, Any]:
    if path is None:
        return {
            "label": label,
            "path": None,
            "present": False,
            "required": required,
            "status": "missing",
            "missingFields": ["comparison.chi2PerDof", "comparison.chi2", "comparison.status"],
        }
    if not path.exists():
        return {
            "label": label,
            "path": str(path),
            "present": False,
            "required": required,
            "status": "missing-file",
            "missingFields": ["comparison.chi2PerDof", "comparison.chi2", "comparison.status"],
        }

    payload = load_json(path)
    comparison = payload.get("comparison")
    if not isinstance(comparison, dict):
        comparison = {}
    chi2 = comparison.get("chi2")
    chi2_per_dof = comparison.get("chi2PerDof", comparison.get("chi2_dof"))
    missing = []
    if not isinstance(chi2, (int, float)) or not math.isfinite(float(chi2)):
        missing.append("comparison.chi2")
    if not isinstance(chi2_per_dof, (int, float)) or not math.isfinite(float(chi2_per_dof)):
        missing.append("comparison.chi2PerDof")

    per_bin = payload.get("perBin", payload.get("per_bin", []))
    max_abs_pull = None
    max_pull_bin = None
    if isinstance(per_bin, list):
        for item in per_bin:
            if not isinstance(item, dict):
                continue
            raw_pull = item.get("absPull")
            if raw_pull is None and isinstance(item.get("pull"), (int, float)):
                raw_pull = abs(float(item["pull"]))
            if isinstance(raw_pull, (int, float)) and math.isfinite(float(raw_pull)):
                if max_abs_pull is None or float(raw_pull) > max_abs_pull:
                    max_abs_pull = float(raw_pull)
                    max_pull_bin = item.get("binIndex", item.get("bin"))

    return {
        "label": label,
        "path": str(path),
        "present": True,
        "required": required,
        "status": "ok" if not missing else "incomplete",
        "missingFields": missing,
        "sha256": sha256_file(path),
        "artifactSchema": payload.get("artifactSchema"),
        "comparisonStatus": comparison.get("status"),
        "chi2": None if "comparison.chi2" in missing else float(chi2),
        "chi2PerDof": None if "comparison.chi2PerDof" in missing else float(chi2_per_dof),
        "dof": comparison.get("dof"),
        "threshold": comparison.get("threshold"),
        "maxAbsPull": max_abs_pull,
        "maxPullBin": max_pull_bin,
    }


def build_decomposition(authority: dict[str, Any], t43: dict[str, Any], w4: dict[str, Any]) -> dict[str, Any]:
    blocked_reasons = []
    if not authority["accepted"]:
        blocked_reasons.append("missingAcceptedDYLuminosityConventionAuthority")
    for comparison in (t43, w4):
        if comparison["required"] and comparison["status"] not in {"ok", "status-doc-observed"}:
            blocked_reasons.append(f"missingRequired{comparison['label']}ComparisonFields")

    convention_missing = [
        field for field in authority["missingFields"]
        if field in {
            "scale_convention",
            "rapidity_window",
            "mass_bin_rule",
            "flavour_weight_rule",
            "integration_method",
            "luminosity_values",
            "normalization_preservation_law",
            "conversion_law",
            "L43",
            "L45",
            "W4_per_bin_luminosities",
        }
    ]
    pdf_missing = [
        field for field in authority["missingFields"]
        if field in {"pdf_set_version", "lhapdf_id", "member_id", "grid_checksum"}
    ]
    efficiency_missing = [
        field for field in authority["missingFields"]
        if field in {"efficiency_acceptance_model", "systematic_budget", "cms_smp_publication_pointer"}
    ]

    return {
        "artifactSchema": "dashi-dy-chi2-pressure-decomposition-v1",
        "schemaVersion": "0.2.0",
        "status": "blocked-non-promoting" if blocked_reasons else "computed-non-promoting",
        "blockedReasons": blocked_reasons,
        "firstMissing": {
            "field": authority.get("authorityGate", {}).get("firstMissing"),
            "group": authority.get("authorityGate", {}).get("firstMissingGroup"),
            "reason": (
                "accepted DY convention authority is absent or incomplete"
                if not authority["accepted"] else
                None
            ),
        },
        "inputs": {
            "authority": authority,
            "t43Comparison": t43,
            "w4Comparison": w4,
        },
        "pressureDomains": {
            "convention_bin_normalization": {
                "status": "blocked" if convention_missing else "authority-fields-present",
                "missingFields": convention_missing,
                "missingByGroup": group_missing(convention_missing),
                "attribution": (
                    "cannot separate convention/bin-normalization from PDF/model pressure until the accepted "
                    "provider conversion law supplies L43, L45, W4 ell_i, and normalization preservation"
                    if convention_missing else
                    "provider convention/bin-normalization fields are present; downstream review still required"
                ),
            },
            "pdf": {
                "status": "indeterminate" if pdf_missing else "authority-fields-present",
                "missingFields": pdf_missing,
                "missingByGroup": group_missing(pdf_missing),
                "attribution": (
                    "local CT18 material is candidate provenance only; no accepted PDF authority attribution"
                    if pdf_missing else
                    "accepted PDF identity/checksum fields are present; PDF uncertainty still needs provider budget"
                ),
            },
            "model": {
                "status": "candidate-pressure-observed" if t43.get("chi2PerDof") is not None or w4.get("chi2PerDof") is not None else "missing-comparison",
                "t43Chi2PerDof": t43.get("chi2PerDof"),
                "w4Chi2PerDof": w4.get("chi2PerDof"),
                "attribution": "observed chi2 pressure is candidate/model-side only until authority and bin normalization are accepted",
            },
            "efficiency_acceptance": {
                "status": "missing" if efficiency_missing else "authority-fields-present",
                "missingFields": efficiency_missing,
                "missingByGroup": group_missing(efficiency_missing),
                "attribution": "missing efficiency/acceptance is not proof for any pressure domain; it remains an explicit provider gap",
            },
        },
        "pressureAttributionStatus": {
            "t43": (
                f"candidate ratio pressure observed at chi2/dof={t43['chi2PerDof']}"
                if t43.get("chi2PerDof") is not None else
                "not localized; comparison fields missing"
            ),
            "w4": (
                f"dirty Z-peak pressure observed at chi2/dof={w4['chi2PerDof']}"
                if w4.get("chi2PerDof") is not None else
                "not localized by this artifact; required W4 comparison fields absent"
            ),
            "authority": "accepted DY convention authority present" if authority["accepted"] else "missing accepted DY convention authority",
            "final": (
                "no promotable attribution; convention/bin-normalization, PDF, model, and efficiency/acceptance remain entangled"
                if blocked_reasons else
                "candidate decomposition computed; still non-promoting pending typed receipt review"
            ),
        },
        "nonPromotionBoundary": [
            "no W4 promotion",
            "no W5 promotion",
            "no DY convention receipt constructed",
            "no Candidate256 physical calibration promotion",
            "no placeholder efficiency/acceptance treated as proof",
        ],
    }


def write_json(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Build non-promoting DY chi2 pressure decomposition artifact.")
    parser.add_argument("--t43-comparison", type=Path, default=Path("logs/research/w3_frozen_3205d74_t43_comparison_20260513.json"))
    parser.add_argument("--w4-comparison", type=Path)
    parser.add_argument("--w4-status-doc", type=Path, default=Path("Docs/W4W5DYConventionCurrentBlocker.md"))
    parser.add_argument("--accepted-dy-authority", type=Path, default=Path("scripts/data/authority_packet.example.json"))
    parser.add_argument("--output", type=Path, default=Path("/tmp/dashi_dy_pressure_decomposition.json"))
    parser.add_argument("--w4-optional", action="store_true", help="Record absent W4 comparison as a gap but do not use it as a blocked exit condition.")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    try:
        authority = inspect_authority(args.accepted_dy_authority)
        t43 = extract_comparison(args.t43_comparison, label="T43", required=True)
        w4 = extract_comparison(args.w4_comparison, label="W4", required=not args.w4_optional)
        if w4["status"] in {"missing", "missing-file"}:
            w4 = extract_w4_status_doc(args.w4_status_doc) or w4
            w4["required"] = not args.w4_optional
        artifact = build_decomposition(authority, t43, w4)
        artifact["artifactDigest"] = stable_digest(artifact)
        write_json(args.output, artifact)
    except (OSError, ValueError, json.JSONDecodeError) as exc:
        print(f"pressure decomposition input error: {exc}", file=sys.stderr)
        return EXIT_INPUT_ERROR

    print(
        "pressure decomposition: "
        f"status={artifact['status']} "
        f"t43_chi2_dof={artifact['pressureDomains']['model']['t43Chi2PerDof']} "
        f"w4_chi2_dof={artifact['pressureDomains']['model']['w4Chi2PerDof']} "
        f"authority={artifact['pressureAttributionStatus']['authority']} "
        f"output={args.output}"
    )
    return EXIT_BLOCKED if artifact["blockedReasons"] else EXIT_OK


if __name__ == "__main__":
    raise SystemExit(main())
