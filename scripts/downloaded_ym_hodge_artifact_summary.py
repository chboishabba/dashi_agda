#!/usr/bin/env python3
"""Summarize downloaded YM/Hodge context artifacts.

This is a downloaded-context intake surface only. It hashes the supplied
artifacts, parses structured CSV/JSON where available, extracts the numeric
YM/Hodge gates used by later formal lanes, and emits JSON plus Markdown.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
import re
from pathlib import Path
from typing import Any


SCHEMA = "dashi-downloaded-ym-hodge-artifact-summary-v1"
VERSION = "1.0.0"
DEFAULT_INPUT_DIR = Path("temp-DOWNLOADED/new additions")
DEFAULT_OUTPUT_DIR = Path("outputs/downloaded_ym_hodge_artifact_summary")

TARGET_FILES = [
    "ym_sprint82_summary.json",
    "ym_sprint82_eta_thresholds.csv",
    "ym_sprint82_assumption_a_oscillation.csv",
    "ym_sprint93_summary.json",
    "ym_sprint93_rows.json",
    "ym_sprint93_master_wc3_calcs.py",
    "sprint69_constants_table.csv",
    "sprint73_lemma_stack.csv",
    "ym_slab_geometry.csv",
    "ym_spatial_slab_entropy_count.csv",
    "ym_temporal_support_noncreation_table.csv",
    "YMSprint93ContinuumGapAttempt.agda",
]


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def coerce_scalar(value: str) -> Any:
    stripped = value.strip()
    if stripped == "":
        return ""
    if stripped in {"True", "False"}:
        return stripped == "True"
    try:
        if re.fullmatch(r"[-+]?\d+", stripped):
            return int(stripped)
        return float(stripped)
    except ValueError:
        return stripped


def read_csv(path: Path) -> list[dict[str, Any]]:
    with path.open(newline="", encoding="utf-8-sig") as handle:
        reader = csv.DictReader(handle)
        return [
            {key: coerce_scalar(value or "") for key, value in row.items()}
            for row in reader
        ]


def read_json(path: Path) -> Any:
    return json.loads(path.read_text(encoding="utf-8"))


def parse_agda_surface(text: str) -> dict[str, Any]:
    records = re.findall(r"^record\s+([A-Za-z0-9_']+)", text, flags=re.MULTILINE)
    functions = re.findall(
        r"^([a-zA-Z][A-Za-z0-9_']*)\s*:", text, flags=re.MULTILINE
    )
    hard_wall_terms = [
        "ContinuumLimitMassGap",
        "noSpectralPollutionUnderContinuumLimit",
        "positiveContinuumMassGap",
        "OSWightmanReconstruction",
        "ClayYangMillsCandidate",
    ]
    return {
        "records": records,
        "functions": functions,
        "record_count": len(records),
        "function_count": len(functions),
        "hard_wall_terms_present": {
            term: term in text for term in hard_wall_terms
        },
        "promotion_claim_present": False,
        "downloaded_context_only": True,
    }


def summarize_artifact(path: Path, root: Path) -> dict[str, Any]:
    item: dict[str, Any] = {
        "name": path.name,
        "relative_path": str(path.relative_to(root.parent.parent))
        if root.parent.parent in path.parents
        else str(path),
        "size_bytes": path.stat().st_size,
        "sha256": sha256_file(path),
        "exists": True,
    }
    suffix = path.suffix.lower()
    if suffix == ".json":
        payload = read_json(path)
        item["kind"] = "json"
        item["top_level_type"] = type(payload).__name__
        if isinstance(payload, dict):
            item["keys"] = sorted(payload.keys())
            item["payload"] = payload
        elif isinstance(payload, list):
            item["row_count"] = len(payload)
            item["sample"] = payload[:3]
            item["payload"] = payload
    elif suffix == ".csv":
        rows = read_csv(path)
        item["kind"] = "csv"
        item["row_count"] = len(rows)
        item["columns"] = list(rows[0].keys()) if rows else []
        item["rows"] = rows
    elif suffix == ".agda":
        text = path.read_text(encoding="utf-8")
        item["kind"] = "agda"
        item["surface"] = parse_agda_surface(text)
    elif suffix == ".py":
        text = path.read_text(encoding="utf-8")
        item["kind"] = "python"
        item["defined_constants"] = {
            key: coerce_scalar(value)
            for key, value in re.findall(
                r"^([A-Za-z_][A-Za-z0-9_]*)\s*=\s*([0-9./-]+)",
                text,
                flags=re.MULTILINE,
            )
        }
        item["mentions"] = {
            "SU3_conservative": "SU3_conservative" in text,
            "row_lt_exp_minus_4": "passes_row_lt_exp_minus_4" in text,
            "k11": "k11" in text or "11" in text,
        }
    else:
        item["kind"] = suffix.lstrip(".") or "unknown"
    return item


def by_name(artifacts: list[dict[str, Any]]) -> dict[str, dict[str, Any]]:
    return {artifact["name"]: artifact for artifact in artifacts}


def first_row(rows: list[dict[str, Any]], **conditions: Any) -> dict[str, Any] | None:
    for row in rows:
        if all(row.get(key) == value for key, value in conditions.items()):
            return row
    return None


def extract_key_gates(artifacts: list[dict[str, Any]]) -> dict[str, Any]:
    named = by_name(artifacts)
    gates: dict[str, Any] = {
        "downloaded_context_only": True,
        "clay_yang_mills_promoted": False,
        "continuum_mass_gap_promoted": False,
        "hodge_field_equations_promoted": False,
    }

    sprint82 = named.get("ym_sprint82_summary.json", {}).get("payload", {})
    sprint93 = named.get("ym_sprint93_summary.json", {}).get("payload", {})
    for key in [
        "q",
        "eta4_q",
        "eta6_q",
        "eta8_q",
        "eta_threshold",
        "q_threshold_eta4",
        "next_unconditional_gate",
        "next_authority_lane_gate",
    ]:
        if key in sprint82:
            gates[key] = sprint82[key]
    for key in [
        "exp_minus_4",
        "su2_first_safe_k",
        "su3_first_safe_k",
        "su3_k11_row",
        "su3_k11_delta",
        "su3_k11_m0",
        "route_decision",
    ]:
        if key in sprint93:
            gates[key] = sprint93[key]

    rows93 = named.get("ym_sprint93_rows.json", {}).get("payload", [])
    if isinstance(rows93, list):
        su3_k11 = first_row(rows93, group="SU3_conservative", k=11)
        if su3_k11:
            gates["su3_k11_row_detail"] = su3_k11
        gates["safe_rows"] = [
            row
            for row in rows93
            if row.get("passes_row_lt_exp_minus_4") is True
        ]

    constants_rows = named.get("sprint69_constants_table.csv", {}).get("rows", [])
    if constants_rows:
        gates["constants_table"] = {
            row["constant"]: row
            for row in constants_rows
            if "constant" in row
        }

    eta_rows = named.get("ym_sprint82_eta_thresholds.csv", {}).get("rows", [])
    if eta_rows:
        gates["eta_threshold_rows"] = eta_rows

    slab_rows = named.get("ym_slab_geometry.csv", {}).get("rows", [])
    if slab_rows:
        gates["kp_closing_slab_rows"] = [
            row for row in slab_rows if row.get("KP_closes") is True
        ]
        gates["blocked_slab_rows"] = [
            row for row in slab_rows if row.get("KP_closes") is False
        ]

    spatial_rows = named.get("ym_spatial_slab_entropy_count.csv", {}).get("rows", [])
    if spatial_rows:
        gates["spatial_entropy_safe_rows"] = [
            row for row in spatial_rows if row.get("KP_closes") is True
        ]

    temporal_rows = named.get(
        "ym_temporal_support_noncreation_table.csv", {}
    ).get("rows", [])
    if temporal_rows:
        gates["temporal_noncreation_rows"] = [
            row
            for row in temporal_rows
            if row.get("temporal_noncreation_holds") is True
        ]

    lemma_rows = named.get("sprint73_lemma_stack.csv", {}).get("rows", [])
    if lemma_rows:
        gates["closed_or_packageable_lemmas"] = [
            row
            for row in lemma_rows
            if row.get("Status") in {"Closed arithmetic", "Closed Sprint72", "Packageable"}
        ]
        gates["open_or_key_gate_lemmas"] = [
            row
            for row in lemma_rows
            if row.get("Status") not in {"Closed arithmetic", "Closed Sprint72", "Packageable"}
        ]

    agda_surface = named.get("YMSprint93ContinuumGapAttempt.agda", {}).get("surface")
    if agda_surface:
        gates["agda_continuum_gap_surface"] = agda_surface

    return gates


def build_summary(input_dir: Path, generated_at: str | None) -> dict[str, Any]:
    artifacts: list[dict[str, Any]] = []
    missing: list[str] = []
    for name in TARGET_FILES:
        path = input_dir / name
        if path.exists():
            artifacts.append(summarize_artifact(path, input_dir))
        else:
            missing.append(name)

    return {
        "schema": SCHEMA,
        "version": VERSION,
        "generated_at": generated_at,
        "input_dir": str(input_dir),
        "output_claim": "downloaded-context-only; no Clay/YM/Hodge promotion",
        "promotion": {
            "clay_yang_mills_promoted": False,
            "continuum_mass_gap_promoted": False,
            "maxwell_hodge_promoted": False,
            "standard_model_promoted": False,
        },
        "artifact_count": len(artifacts),
        "missing_artifacts": missing,
        "artifacts": artifacts,
        "key_gates": extract_key_gates(artifacts),
    }


def md_value(value: Any) -> str:
    if isinstance(value, float):
        return f"{value:.15g}"
    return str(value)


def render_markdown(summary: dict[str, Any]) -> str:
    gates = summary["key_gates"]
    lines = [
        "# Downloaded YM/Hodge Artifact Summary",
        "",
        f"- Schema: `{summary['schema']}`",
        f"- Version: `{summary['version']}`",
        f"- Input dir: `{summary['input_dir']}`",
        f"- Artifact count: `{summary['artifact_count']}`",
        "- Claim boundary: downloaded-context only; no Clay/YM/Hodge promotion.",
        "",
        "## Key Gates",
        "",
        "| Gate | Value |",
        "|---|---:|",
    ]
    for key in [
        "q",
        "eta4_q",
        "eta6_q",
        "eta8_q",
        "eta_threshold",
        "exp_minus_4",
        "su2_first_safe_k",
        "su3_first_safe_k",
        "su3_k11_row",
        "su3_k11_delta",
        "su3_k11_m0",
    ]:
        if key in gates:
            lines.append(f"| `{key}` | `{md_value(gates[key])}` |")
    if "route_decision" in gates:
        lines.extend(["", f"- Route decision: `{gates['route_decision']}`"])
    if "next_unconditional_gate" in gates:
        lines.append(f"- Next unconditional gate: `{gates['next_unconditional_gate']}`")
    if "next_authority_lane_gate" in gates:
        lines.append(f"- Next authority lane gate: `{gates['next_authority_lane_gate']}`")

    lines.extend(["", "## Artifact Hashes", "", "| Artifact | Kind | Size | SHA-256 |", "|---|---|---:|---|"])
    for artifact in summary["artifacts"]:
        lines.append(
            f"| `{artifact['name']}` | `{artifact.get('kind', 'unknown')}` | "
            f"{artifact['size_bytes']} | `{artifact['sha256']}` |"
        )

    if summary["missing_artifacts"]:
        lines.extend(["", "## Missing Artifacts", ""])
        lines.extend(f"- `{name}`" for name in summary["missing_artifacts"])

    if "closed_or_packageable_lemmas" in gates:
        lines.extend(["", "## Closed Or Packageable Lemmas", ""])
        for row in gates["closed_or_packageable_lemmas"]:
            lines.append(
                f"- `{row.get('Lemma')}`: {row.get('Status')} "
                f"({row.get('Key value')})"
            )

    if "open_or_key_gate_lemmas" in gates:
        lines.extend(["", "## Open Or Key-Gate Lemmas", ""])
        for row in gates["open_or_key_gate_lemmas"]:
            lines.append(
                f"- `{row.get('Lemma')}`: {row.get('Status')} "
                f"({row.get('Key value')})"
            )

    agda = gates.get("agda_continuum_gap_surface")
    if agda:
        lines.extend(
            [
                "",
                "## Agda Continuum Gap Surface",
                "",
                f"- Records: `{agda['record_count']}`",
                f"- Functions: `{agda['function_count']}`",
                "- Hard wall terms present: "
                + ", ".join(
                    f"`{term}`={present}"
                    for term, present in agda["hard_wall_terms_present"].items()
                ),
            ]
        )

    lines.extend(["", "## Promotion", "", "- `clay_yang_mills_promoted = false`", "- `continuum_mass_gap_promoted = false`", "- `hodge_field_equations_promoted = false`", ""])
    return "\n".join(lines)


def write_outputs(summary: dict[str, Any], output_dir: Path) -> dict[str, str]:
    output_dir.mkdir(parents=True, exist_ok=True)
    json_path = output_dir / "downloaded_ym_hodge_artifact_summary.json"
    md_path = output_dir / "downloaded_ym_hodge_artifact_summary.md"
    json_path.write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    md_path.write_text(render_markdown(summary), encoding="utf-8")
    return {"json": str(json_path), "markdown": str(md_path)}


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input-dir", "--source-dir", dest="input_dir", type=Path, default=DEFAULT_INPUT_DIR)
    parser.add_argument("--output-dir", type=Path, default=DEFAULT_OUTPUT_DIR)
    parser.add_argument("--generated-at", default=None)
    parser.add_argument("--json", action="store_true", help="print output paths as JSON")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    summary = build_summary(args.input_dir, args.generated_at)
    paths = write_outputs(summary, args.output_dir)
    if args.json:
        print(json.dumps(paths, indent=2, sort_keys=True))
    else:
        print(f"Wrote {paths['json']}")
        print(f"Wrote {paths['markdown']}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
