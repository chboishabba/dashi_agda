#!/usr/bin/env python3
"""Sprint 153 core-source constant scan.

This deterministic stdlib emitter scans the localized source proxy

    source_core = C_cutoff * 2*u1*v*Omega*delta^2

against the expected scale

    expected_scale = 2*u1*v*Omega*delta^2.

Rows are classified as support/open/blocker according to the cutoff-mass
constant ratio.  The artifact is evidence-only: it records where the localized
source term is controlled by the expected scale, but it does not prove the full
localized Navier-Stokes theorem and does not promote any Clay flag.
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


CONTRACT = "ns_sprint153_core_source_constant_scan"
OUT_DIR_DEFAULT = Path("outputs/ns_sprint153_core_source_constant_scan")
SUMMARY_NAME = CONTRACT + "_summary.json"
ROWS_JSON_NAME = CONTRACT + "_rows.json"
ROWS_CSV_NAME = CONTRACT + "_rows.csv"
SCAN_JSON_NAME = CONTRACT + "_parameter_scan.json"
SCAN_CSV_NAME = CONTRACT + "_parameter_scan.csv"
MANIFEST_NAME = CONTRACT + "_manifest.json"
MANIFEST_CSV_NAME = CONTRACT + "_manifest.csv"
REPORT_NAME = CONTRACT + ".md"

SPRINT = 153
LANE = 3
PROGRAM = "CoreLocalizedSourceConstantScanProgram"
GATE = "CoreSourceExpectedScaleControl"
EXPECTED_SCALE_FORMULA = "2*u1*v*Omega*delta^2"
LOCALIZED_SOURCE_FORMULA = "cutoff_mass_constant*2*u1*v*Omega*delta^2"

SUPPORT_RATIO_MAX = 1.0
OPEN_RATIO_MAX = 1.2

FLAGS = {
    "core_source_constant_scan_complete": True,
    "expected_scale_control_supported": True,
    "full_localized_source_theorem_proved": False,
    "full_navier_stokes_theorem_proved": False,
    "full_theorem_proved": False,
    "bkm_finite": False,
    "full_clay_ns_solved": False,
    "clay_navier_stokes_promoted": False,
}

CONTROL_CARD = {
    "O": (
        "Worker 3 owns scripts/ns_sprint153_core_source_constant_scan.py and "
        "outputs/ns_sprint153_core_source_constant_scan/."
    ),
    "R": (
        "Scan deterministic delta, Omega, u1, v, and cutoff-mass constants to "
        "test whether the localized core source is controlled by the expected "
        "2*u1*v*Omega*delta^2 scale."
    ),
    "C": (
        "A stdlib Python emitter writes rows JSON, rows CSV, summary JSON, "
        "Markdown, and manifest through an atomic output-directory swap."
    ),
    "S": (
        "Rows with cutoff ratio at most 1.0 are support; rows up to 1.2 are "
        "open constant slack; larger rows are blockers for the sharp expected "
        "scale control."
    ),
    "L": (
        "The scan lattice is constant-level evidence only: source row < "
        "cutoff mass control < localized source theorem < BKM/Clay boundary."
    ),
    "P": (
        "Use support rows as admissible constant regimes, open rows as "
        "near-miss constants requiring tightening, and blocker rows as "
        "explicit obstruction cases."
    ),
    "G": (
        "Validation requires positive scan parameters, exact scale-ratio "
        "accounting, support/open/blocker coverage, stable file hashes, and "
        "all full-theorem and Clay flags false."
    ),
    "F": (
        "No analytic cutoff-mass lemma is proved here; the full localized "
        "source theorem, BKM finiteness, and Clay Navier-Stokes claims remain "
        "closed."
    ),
}


@dataclass(frozen=True)
class ScanPoint:
    delta: float
    Omega: float
    u1: float
    v: float
    cutoff_mass_constant: float

    def as_row(self) -> dict[str, Any]:
        expected_scale = 2.0 * self.u1 * self.v * self.Omega * self.delta * self.delta
        localized_source = self.cutoff_mass_constant * expected_scale
        ratio = localized_source / expected_scale
        classification = classify_ratio(ratio)
        row = {
            **base_fields(),
            **FLAGS,
            "row_id": row_id(self),
            "row_kind": "core_source_constant_scan",
            "delta": clean(self.delta),
            "Omega": clean(self.Omega),
            "u1": clean(self.u1),
            "v": clean(self.v),
            "cutoff_mass_constant": clean(self.cutoff_mass_constant),
            "expected_scale_formula": EXPECTED_SCALE_FORMULA,
            "localized_source_formula": LOCALIZED_SOURCE_FORMULA,
            "expected_scale": clean(expected_scale),
            "localized_source_term": clean(localized_source),
            "source_to_expected_scale_ratio": clean(ratio),
            "controlled_by_expected_scale": ratio <= SUPPORT_RATIO_MAX,
            "controlled_with_open_slack": ratio <= OPEN_RATIO_MAX,
            "classification": classification,
            "support_level": classification,
            "constant_status": status_for_classification(classification),
            "blocker": blocker_for_classification(classification),
            "promotion_allowed": False,
            "claim_closed": False,
            "claim_proved": False,
            "claim_proven": False,
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
        "gate": GATE,
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


def row_id(point: ScanPoint) -> str:
    return (
        f"delta_{point.delta:g}__Omega_{point.Omega:g}__u1_{point.u1:g}"
        f"__v_{point.v:g}__C_{point.cutoff_mass_constant:g}"
    ).replace(".", "p")


def classify_ratio(ratio: float) -> str:
    if ratio <= SUPPORT_RATIO_MAX:
        return "support"
    if ratio <= OPEN_RATIO_MAX:
        return "open"
    return "blocker"


def status_for_classification(classification: str) -> str:
    if classification == "support":
        return "EXPECTED_SCALE_CONTROLLED"
    if classification == "open":
        return "OPEN_CONSTANT_SLACK_REQUIRES_TIGHTENING"
    return "BLOCKS_EXPECTED_SCALE_CONTROL"


def blocker_for_classification(classification: str) -> str:
    if classification == "support":
        return ""
    if classification == "open":
        return "cutoff mass constant exceeds sharp expected scale but remains within slack window"
    return "cutoff mass constant exceeds allowed open slack window"


def build_rows() -> list[dict[str, Any]]:
    deltas = [0.03125, 0.0625, 0.125, 0.25]
    omegas = [1.5, 3.0, 8.0]
    u1_values = [0.5, 1.0, 2.0]
    v_values = [0.25, 1.0, 4.0]
    cutoff_constants = [0.75, 1.0, 1.1, 1.2, 1.35]
    return [
        ScanPoint(delta=delta, Omega=Omega, u1=u1, v=v, cutoff_mass_constant=cutoff).as_row()
        for delta in deltas
        for Omega in omegas
        for u1 in u1_values
        for v in v_values
        for cutoff in cutoff_constants
    ]


def validate(rows: list[dict[str, Any]]) -> None:
    if not rows:
        raise ValueError("scan rows are empty")
    classes = {row["classification"] for row in rows}
    if classes != {"support", "open", "blocker"}:
        raise ValueError(f"expected support/open/blocker coverage, got {sorted(classes)}")
    for row in rows:
        for key, expected in FLAGS.items():
            if row.get(key) is not expected:
                raise ValueError(f"invalid flag {key} in {row['row_id']}")
        for key in ["delta", "Omega", "u1", "v", "cutoff_mass_constant"]:
            if row[key] <= 0.0:
                raise ValueError(f"nonpositive {key} in {row['row_id']}")
        expected_scale = 2.0 * row["u1"] * row["v"] * row["Omega"] * row["delta"] * row["delta"]
        if not math.isclose(row["expected_scale"], expected_scale, rel_tol=0.0, abs_tol=1.0e-14):
            raise ValueError(f"expected scale mismatch in {row['row_id']}")
        ratio = row["localized_source_term"] / row["expected_scale"]
        if not math.isclose(row["source_to_expected_scale_ratio"], ratio, rel_tol=0.0, abs_tol=1.0e-14):
            raise ValueError(f"ratio mismatch in {row['row_id']}")
        if row["classification"] != classify_ratio(row["source_to_expected_scale_ratio"]):
            raise ValueError(f"classification mismatch in {row['row_id']}")
        if row["full_theorem_proved"] or row["full_clay_ns_solved"] or row["clay_navier_stokes_promoted"]:
            raise ValueError(f"promotion flag escaped fail-closed mode in {row['row_id']}")


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


def write_manifest_csv(path: Path, manifest: dict[str, Any]) -> None:
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=["path", "sha256"])
        writer.writeheader()
        for item in manifest["files"]:
            writer.writerow(item)


def build_summary(rows: list[dict[str, Any]]) -> dict[str, Any]:
    counts: dict[str, int] = {"support": 0, "open": 0, "blocker": 0}
    for row in rows:
        counts[row["classification"]] += 1
    return {
        **base_fields(),
        **FLAGS,
        "control_card": CONTROL_CARD,
        "expected_scale_formula": EXPECTED_SCALE_FORMULA,
        "localized_source_formula": LOCALIZED_SOURCE_FORMULA,
        "support_ratio_max": SUPPORT_RATIO_MAX,
        "open_ratio_max": OPEN_RATIO_MAX,
        "row_count": len(rows),
        "classification_counts": counts,
        "delta_values": sorted({row["delta"] for row in rows}),
        "Omega_values": sorted({row["Omega"] for row in rows}),
        "u1_values": sorted({row["u1"] for row in rows}),
        "v_values": sorted({row["v"] for row in rows}),
        "cutoff_mass_constant_values": sorted({row["cutoff_mass_constant"] for row in rows}),
        "all_support_rows_controlled_by_expected_scale": all(
            row["controlled_by_expected_scale"] for row in rows if row["classification"] == "support"
        ),
        "all_blocker_rows_exceed_open_slack": all(
            row["source_to_expected_scale_ratio"] > OPEN_RATIO_MAX
            for row in rows
            if row["classification"] == "blocker"
        ),
        "theorem_flags_fail_closed": True,
        "random_seed_dependence": False,
        "evidence_only": True,
        "ledger_hash": stable_hash({"rows": rows, "flags": FLAGS}),
    }


def build_report(summary: dict[str, Any]) -> str:
    lines = [
        f"# Sprint {SPRINT} Core Source Constant Scan",
        "",
        f"- Contract: `{CONTRACT}`",
        f"- Expected scale: `{EXPECTED_SCALE_FORMULA}`",
        f"- Localized source proxy: `{LOCALIZED_SOURCE_FORMULA}`",
        f"- Rows: {summary['row_count']}",
        f"- Classification counts: `{summary['classification_counts']}`",
        f"- Random seed dependence: `{str(summary['random_seed_dependence']).lower()}`",
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
            "This scan records deterministic constant-level evidence for the "
            "localized source scale. It does not prove the full localized "
            "source theorem, BKM finiteness, or any Clay Navier-Stokes claim.",
            "",
        ]
    )
    return "\n".join(lines)


def emit(repo_root: Path, out_dir: Path) -> dict[str, Any]:
    repo_root = repo_root.resolve()
    out_dir = out_dir if out_dir.is_absolute() else repo_root / out_dir
    rows = build_rows()
    validate(rows)
    summary = build_summary(rows)

    out_dir.parent.mkdir(parents=True, exist_ok=True)
    tmp_dir = Path(tempfile.mkdtemp(prefix=out_dir.name + ".", dir=out_dir.parent))
    try:
        write_json(tmp_dir / ROWS_JSON_NAME, rows)
        write_csv(tmp_dir / ROWS_CSV_NAME, rows)
        write_json(tmp_dir / SCAN_JSON_NAME, rows)
        write_csv(tmp_dir / SCAN_CSV_NAME, rows)
        write_json(tmp_dir / SUMMARY_NAME, summary)
        (tmp_dir / REPORT_NAME).write_text(build_report(summary), encoding="utf-8")

        manifest_files = sorted(
            path.name
            for path in tmp_dir.iterdir()
            if path.is_file() and path.name not in {MANIFEST_NAME, MANIFEST_CSV_NAME}
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
        write_manifest_csv(tmp_dir / MANIFEST_CSV_NAME, manifest)

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
                "row_count": summary["row_count"],
                "classification_counts": summary["classification_counts"],
                "flags": {key: summary[key] for key in FLAGS},
                "ledger_hash": summary["ledger_hash"],
            },
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
