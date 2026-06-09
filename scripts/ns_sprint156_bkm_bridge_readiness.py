#!/usr/bin/env python3
"""Sprint 156 BKM bridge-readiness assembler.

This checker consumes the Sprint 155 model-validity assembler receipt when it
is present and encodes the Sprint 156 bridge state for the next BKM
translation.  It records model validity and the corrected Omega ODE as closed
readiness inputs, while keeping the BKM integral estimate, continuation theorem
bridge, and full Clay mechanism-exhaustion claims unpromoted.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
import os
import shutil
import sys
import tempfile
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any


CONTRACT = "ns_sprint156_bkm_bridge_readiness"
OUT_DIR_DEFAULT = Path("outputs") / CONTRACT
SUMMARY_NAME = f"{CONTRACT}_summary.json"
ROWS_JSON_NAME = f"{CONTRACT}_rows.json"
ROWS_CSV_NAME = f"{CONTRACT}_rows.csv"
REPORT_NAME = f"{CONTRACT}.md"
MANIFEST_NAME = f"{CONTRACT}_manifest.json"

SPRINT = 156
LANE = 4
PROGRAM = "BKMBridgeReadinessAssembler"
DECISION = "ready_for_next_bkm_translation_not_promoted"

SOURCE_ARTIFACTS = {
    "s155_model_validity": Path(
        "outputs/ns_sprint155_model_validity_assembler/"
        "ns_sprint155_model_validity_assembler_summary.json"
    ),
    "s155_model_validity_rows": Path(
        "outputs/ns_sprint155_model_validity_assembler/"
        "ns_sprint155_model_validity_assembler_rows.json"
    ),
    "s155_localized_ibp": Path(
        "outputs/ns_sprint155_localized_enstrophy_ibp_identity/"
        "ns_sprint155_localized_enstrophy_ibp_identity_summary.json"
    ),
    "s155_operator_boundary": Path(
        "outputs/ns_sprint155_operator_boundary_term_checker/"
        "ns_sprint155_operator_boundary_term_checker_summary.json"
    ),
}

SPRINT156_ENCODED_STATE = {
    "ModelValidityForWidthODE": "closed",
    "CorrectedOmegaODE": "available",
    "BKMIntegralEstimate": "not_promoted",
    "ContinuationTheoremBridge": "pending",
    "FullClayMechanismExhaustion": "absent",
}

CONTROL_CARD = {
    "O": (
        "Worker 4 owns scripts/ns_sprint156_bkm_bridge_readiness.py and "
        "outputs/ns_sprint156_bkm_bridge_readiness/."
    ),
    "R": (
        "Emit readiness rows for the next BKM translation after Sprint 155/156: "
        "ModelValidityForWidthODE closed, corrected Omega ODE available, BKM "
        "integral estimate not promoted, continuation theorem bridge pending, "
        "and full Clay mechanism exhaustion absent."
    ),
    "C": (
        "A deterministic Python stdlib checker reads Sprint 155 receipts when "
        "available, encodes the Sprint 156 bridge state, and writes JSON, CSV, "
        "Markdown, and manifest artifacts."
    ),
    "S": (
        "Sprint 155 closed the upstream model-validity support ledger. Sprint "
        "156 records readiness for BKM translation, not a BKM finiteness proof "
        "or a Clay Navier-Stokes solution."
    ),
    "L": (
        "Only rows marked readiness_closed=true are inputs for the next BKM "
        "translation. Promotion gates remain false until separate theorem "
        "receipts close them."
    ),
    "P": (
        "Use this artifact as a normalized bridge-readiness ledger, not as an "
        "analytic proof, Agda theorem, BKM finite proof, continuation theorem, "
        "or Clay solution."
    ),
    "G": (
        "bkm_finite and full_clay_ns_solved are hard-guarded false. BKM "
        "promotion requires a future integral-estimate receipt plus a future "
        "continuation-theorem bridge."
    ),
    "F": (
        "Open blockers: BKM integral estimate promotion, continuation theorem "
        "bridge, and full Clay mechanism exhaustion."
    ),
}


@dataclass(frozen=True)
class ReadinessRow:
    row_id: str
    normalized_name: str
    sprint_span: str
    category: str
    readiness_closed: bool
    status: str
    next_bkm_translation_input: bool
    bkm_promoted: bool
    continuation_bridge_promoted: bool
    full_clay_mechanism_exhausted: bool
    evidence_sources: tuple[str, ...]
    encoded_state: str
    blocking_reasons: tuple[str, ...]

    def as_row(self) -> dict[str, Any]:
        row = asdict(self)
        row.update(
            {
                "sprint": SPRINT,
                "lane": LANE,
                "contract": CONTRACT,
                "program": PROGRAM,
                "decision": DECISION,
                "bkm_finite": False,
                "full_clay_ns_solved": False,
                "full_clay_can_promote": False,
                "clay_navier_stokes_promoted": False,
            }
        )
        row["evidence_sources"] = list(self.evidence_sources)
        row["blocking_reasons"] = list(self.blocking_reasons)
        row["row_hash"] = stable_hash({k: v for k, v in row.items() if k != "row_hash"})
        return row


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, default=Path.cwd())
    parser.add_argument("--out-dir", type=Path, default=OUT_DIR_DEFAULT)
    return parser.parse_args()


def stable_hash(value: Any) -> str:
    payload = json.dumps(value, sort_keys=True, separators=(",", ":")).encode("utf-8")
    return hashlib.sha256(payload).hexdigest()


def file_sha256(path: Path) -> str | None:
    if not path.exists():
        return None
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


def read_json(path: Path) -> Any | None:
    if not path.exists():
        return None
    with path.open("r", encoding="utf-8") as handle:
        return json.load(handle)


def source_name(key: str) -> str:
    return str(SOURCE_ARTIFACTS[key])


def s155_model_validity_closed(summary: dict[str, Any] | None) -> bool:
    if not isinstance(summary, dict):
        return False
    promotion_status = summary.get("promotion_status")
    if isinstance(promotion_status, dict) and promotion_status.get("ModelValidityForWidthODE") is True:
        return True
    closed_status = summary.get("closed_status")
    if isinstance(closed_status, dict) and closed_status and all(value is True for value in closed_status.values()):
        return True
    open_obligations = summary.get("open_obligations")
    return isinstance(open_obligations, list) and not open_obligations


def build_rows(repo_root: Path) -> list[dict[str, Any]]:
    s155_summary = read_json(repo_root / SOURCE_ARTIFACTS["s155_model_validity"])
    model_validity_supported = s155_model_validity_closed(s155_summary)
    model_validity_closed = model_validity_supported and (
        SPRINT156_ENCODED_STATE["ModelValidityForWidthODE"] == "closed"
    )

    row_specs = [
        ReadinessRow(
            row_id="model_validity_for_width_ode_closed",
            normalized_name="ModelValidityForWidthODE",
            sprint_span="155-156",
            category="bkm_translation_input",
            readiness_closed=model_validity_closed,
            status="CLOSED" if model_validity_closed else "OPEN_FAIL_CLOSED",
            next_bkm_translation_input=model_validity_closed,
            bkm_promoted=False,
            continuation_bridge_promoted=False,
            full_clay_mechanism_exhausted=False,
            evidence_sources=(source_name("s155_model_validity"),),
            encoded_state=SPRINT156_ENCODED_STATE["ModelValidityForWidthODE"],
            blocking_reasons=()
            if model_validity_closed
            else ("Sprint155 model-validity support receipt missing or open",),
        ),
        ReadinessRow(
            row_id="corrected_omega_ode_available",
            normalized_name="CorrectedOmegaODE",
            sprint_span="156",
            category="bkm_translation_input",
            readiness_closed=True,
            status="AVAILABLE",
            next_bkm_translation_input=True,
            bkm_promoted=False,
            continuation_bridge_promoted=False,
            full_clay_mechanism_exhausted=False,
            evidence_sources=(source_name("s155_model_validity"), source_name("s155_localized_ibp")),
            encoded_state=SPRINT156_ENCODED_STATE["CorrectedOmegaODE"],
            blocking_reasons=(),
        ),
        ReadinessRow(
            row_id="bkm_integral_estimate_not_promoted",
            normalized_name="BKMIntegralEstimate",
            sprint_span="156",
            category="promotion_gate",
            readiness_closed=False,
            status="NOT_PROMOTED",
            next_bkm_translation_input=False,
            bkm_promoted=False,
            continuation_bridge_promoted=False,
            full_clay_mechanism_exhausted=False,
            evidence_sources=(source_name("s155_model_validity_rows"),),
            encoded_state=SPRINT156_ENCODED_STATE["BKMIntegralEstimate"],
            blocking_reasons=("BKM integral estimate requires a separate promotion receipt",),
        ),
        ReadinessRow(
            row_id="continuation_theorem_bridge_pending",
            normalized_name="ContinuationTheoremBridge",
            sprint_span="156",
            category="promotion_gate",
            readiness_closed=False,
            status="PENDING",
            next_bkm_translation_input=False,
            bkm_promoted=False,
            continuation_bridge_promoted=False,
            full_clay_mechanism_exhausted=False,
            evidence_sources=(source_name("s155_operator_boundary"),),
            encoded_state=SPRINT156_ENCODED_STATE["ContinuationTheoremBridge"],
            blocking_reasons=("Continuation theorem bridge is pending",),
        ),
        ReadinessRow(
            row_id="full_clay_mechanism_exhaustion_absent",
            normalized_name="FullClayMechanismExhaustion",
            sprint_span="156",
            category="hard_guard",
            readiness_closed=False,
            status="ABSENT_HARD_GUARD_FALSE",
            next_bkm_translation_input=False,
            bkm_promoted=False,
            continuation_bridge_promoted=False,
            full_clay_mechanism_exhausted=False,
            evidence_sources=tuple(source_name(key) for key in SOURCE_ARTIFACTS),
            encoded_state=SPRINT156_ENCODED_STATE["FullClayMechanismExhaustion"],
            blocking_reasons=(
                "Full Clay mechanism exhaustion is absent",
                "full_clay_ns_solved is hard-guarded false",
            ),
        ),
    ]
    return [row.as_row() for row in row_specs]


def validate(rows: list[dict[str, Any]], summary: dict[str, Any]) -> list[str]:
    errors: list[str] = []
    expected = {
        "ModelValidityForWidthODE",
        "CorrectedOmegaODE",
        "BKMIntegralEstimate",
        "ContinuationTheoremBridge",
        "FullClayMechanismExhaustion",
    }
    observed = {str(row.get("normalized_name")) for row in rows}
    if missing := sorted(expected - observed):
        errors.append("missing readiness rows: " + ", ".join(missing))
    if extra := sorted(observed - expected):
        errors.append("unexpected readiness rows: " + ", ".join(extra))
    if summary.get("bkm_finite") is not False:
        errors.append("summary bkm_finite must be false")
    if summary.get("full_clay_ns_solved") is not False:
        errors.append("summary full_clay_ns_solved must be false")
    if summary.get("promotion_status", {}).get("BKMIntegralEstimate") is not False:
        errors.append("BKM integral estimate must not promote")
    if summary.get("promotion_status", {}).get("ContinuationTheoremBridge") is not False:
        errors.append("continuation theorem bridge must not promote")
    if summary.get("promotion_status", {}).get("FullClayMechanismExhaustion") is not False:
        errors.append("full Clay mechanism exhaustion must not promote")
    for row in rows:
        if row.get("bkm_finite") is not False:
            errors.append(f"{row.get('row_id')} sets bkm_finite true")
        if row.get("full_clay_ns_solved") is not False:
            errors.append(f"{row.get('row_id')} sets full_clay_ns_solved true")
        if row.get("full_clay_can_promote") is not False:
            errors.append(f"{row.get('row_id')} sets full_clay_can_promote true")
    return errors


def build_summary(rows: list[dict[str, Any]], repo_root: Path) -> dict[str, Any]:
    readiness_status = {row["normalized_name"]: bool(row["readiness_closed"]) for row in rows}
    promotion_status = {
        "BKMIntegralEstimate": False,
        "ContinuationTheoremBridge": False,
        "FullClayMechanismExhaustion": False,
        "bkm_finite": False,
        "full_clay_ns_solved": False,
        "full_clay_can_promote": False,
        "clay_navier_stokes_promoted": False,
    }
    summary: dict[str, Any] = {
        "contract": CONTRACT,
        "sprint": SPRINT,
        "lane": LANE,
        "program": PROGRAM,
        "decision": DECISION,
        "row_count": len(rows),
        "readiness_status": readiness_status,
        "next_bkm_translation_inputs": [
            row["normalized_name"] for row in rows if row["next_bkm_translation_input"]
        ],
        "blocked_promotions": [
            row["normalized_name"]
            for row in rows
            if row["category"] in {"promotion_gate", "hard_guard"} and not row["readiness_closed"]
        ],
        "promotion_status": promotion_status,
        "bkm_finite": False,
        "full_clay_ns_solved": False,
        "full_clay_hard_guard": True,
        "promotion_allowed": False,
        "source_presence": {
            key: {
                "path": str(path),
                "exists": (repo_root / path).exists(),
                "sha256": file_sha256(repo_root / path),
            }
            for key, path in SOURCE_ARTIFACTS.items()
        },
        "encoded_sprint156_state": SPRINT156_ENCODED_STATE,
        "control_card": CONTROL_CARD,
    }
    errors = validate(rows, summary)
    summary["validation_passed"] = not errors
    summary["validation_errors"] = errors
    summary["summary_hash"] = stable_hash(
        {key: value for key, value in summary.items() if key != "summary_hash"}
    )
    return summary


def write_json(path: Path, value: Any) -> None:
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def write_csv(path: Path, rows: list[dict[str, Any]]) -> None:
    with path.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(rows[0].keys()))
        writer.writeheader()
        writer.writerows(rows)


def render_markdown(summary: dict[str, Any], rows: list[dict[str, Any]]) -> str:
    lines = [
        "# Sprint 156 BKM Bridge Readiness",
        "",
        f"- Decision: `{summary['decision']}`",
        f"- Validation passed: `{summary['validation_passed']}`",
        f"- BKM finite: `{summary['bkm_finite']}`",
        f"- Full Clay NS solved: `{summary['full_clay_ns_solved']}`",
        "",
        "## Readiness Rows",
        "",
        "| row_id | normalized_name | status | readiness_closed | next_bkm_input | blockers |",
        "| --- | --- | --- | ---: | ---: | --- |",
    ]
    for row in rows:
        blockers = "; ".join(row["blocking_reasons"]) if row["blocking_reasons"] else "none"
        lines.append(
            "| {row_id} | {normalized_name} | {status} | {readiness_closed} | "
            "{next_bkm_translation_input} | {blockers} |".format(**row, blockers=blockers)
        )
    lines.extend(
        [
            "",
            "## Promotion Guards",
            "",
            "| guard | value |",
            "| --- | ---: |",
            f"| bkm_finite | {summary['bkm_finite']} |",
            f"| full_clay_ns_solved | {summary['full_clay_ns_solved']} |",
            f"| full_clay_can_promote | {summary['promotion_status']['full_clay_can_promote']} |",
            f"| clay_navier_stokes_promoted | {summary['promotion_status']['clay_navier_stokes_promoted']} |",
            "",
            "## Source Presence",
            "",
            "| source | exists | path |",
            "| --- | ---: | --- |",
        ]
    )
    for key, source in summary["source_presence"].items():
        lines.append(f"| {key} | {source['exists']} | `{source['path']}` |")
    lines.extend(["", "## O/R/C/S/L/P/G/F", ""])
    for key in ("O", "R", "C", "S", "L", "P", "G", "F"):
        lines.append(f"- {key}: {CONTROL_CARD[key]}")
    lines.append("")
    return "\n".join(lines)


def build_manifest(repo_root: Path, out_dir: Path, summary: dict[str, Any]) -> dict[str, Any]:
    files = {
        "summary": out_dir / SUMMARY_NAME,
        "rows_json": out_dir / ROWS_JSON_NAME,
        "rows_csv": out_dir / ROWS_CSV_NAME,
        "markdown": out_dir / REPORT_NAME,
        "manifest": out_dir / MANIFEST_NAME,
    }
    manifest: dict[str, Any] = {
        "contract": CONTRACT,
        "sprint": SPRINT,
        "lane": LANE,
        "decision": DECISION,
        "validation_passed": summary["validation_passed"],
        "bkm_finite": summary["bkm_finite"],
        "full_clay_ns_solved": summary["full_clay_ns_solved"],
        "files": {
            key: {
                "path": display_path(path, repo_root),
                "exists": path.exists(),
                "sha256": file_sha256(path),
            }
            for key, path in files.items()
        },
    }
    manifest["manifest_hash"] = stable_hash(
        {key: value for key, value in manifest.items() if key != "manifest_hash"}
    )
    return manifest


def write_outputs(repo_root: Path, out_dir: Path, rows: list[dict[str, Any]], summary: dict[str, Any]) -> None:
    final_out = out_dir if out_dir.is_absolute() else repo_root / out_dir
    final_out.parent.mkdir(parents=True, exist_ok=True)
    temp_dir = Path(tempfile.mkdtemp(prefix=f".{CONTRACT}.", dir=final_out.parent))
    try:
        write_json(temp_dir / ROWS_JSON_NAME, rows)
        write_csv(temp_dir / ROWS_CSV_NAME, rows)
        write_json(temp_dir / SUMMARY_NAME, summary)
        (temp_dir / REPORT_NAME).write_text(render_markdown(summary, rows), encoding="utf-8")
        write_json(temp_dir / MANIFEST_NAME, build_manifest(repo_root, temp_dir, summary))
        if final_out.exists():
            shutil.rmtree(final_out)
        os.replace(temp_dir, final_out)
        write_json(final_out / MANIFEST_NAME, build_manifest(repo_root, final_out, summary))
    except Exception:
        shutil.rmtree(temp_dir, ignore_errors=True)
        raise


def main() -> int:
    args = parse_args()
    repo_root = args.repo_root.resolve()
    rows = build_rows(repo_root)
    summary = build_summary(rows, repo_root)
    write_outputs(repo_root, args.out_dir, rows, summary)
    print(
        json.dumps(
            {
                "contract": CONTRACT,
                "validation_passed": summary["validation_passed"],
                "bkm_finite": summary["bkm_finite"],
                "full_clay_ns_solved": summary["full_clay_ns_solved"],
                "readiness_status": summary["readiness_status"],
                "blocked_promotions": summary["blocked_promotions"],
                "out_dir": display_path(
                    args.out_dir if args.out_dir.is_absolute() else repo_root / args.out_dir,
                    repo_root,
                ),
            },
            sort_keys=True,
        )
    )
    return 0 if summary["validation_passed"] else 1


if __name__ == "__main__":
    sys.exit(main())
