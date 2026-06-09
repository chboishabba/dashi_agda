#!/usr/bin/env python3
"""Generate Sprint 121 compact group parameter table for GG1."""

from __future__ import annotations

import argparse
import json
from dataclasses import dataclass
from pathlib import Path
from typing import Any


DEFAULT_OUT_DIR = Path("outputs/ym_sprint121_compact_group_parameter_table")
SUMMARY_NAME = "ym_sprint121_compact_group_parameter_table.json"
REPORT_NAME = "ym_sprint121_compact_group_parameter_table.md"


@dataclass(frozen=True)
class GroupEntry:
    key: str
    family: str
    display_name: str
    class_type: str
    compact_simple: bool
    parameter_domain: str
    adjoint_dimension_formula: str
    adjoint_dimension_value: int | None
    rank_formula: str
    rank_value: int | None
    notes: str

    def k_g_value(self) -> int | str:
        if self.adjoint_dimension_value is not None:
            return self.adjoint_dimension_value
        return self.adjoint_dimension_formula

    def to_json(self) -> dict[str, Any]:
        return {
            "key": self.key,
            "family": self.family,
            "display_name": self.display_name,
            "class_type": self.class_type,
            "compact_simple": self.compact_simple,
            "parameter_domain": self.parameter_domain,
            "adjoint_dimension_formula": self.adjoint_dimension_formula,
            "adjoint_dimension_value": self.adjoint_dimension_value,
            "rank_formula": self.rank_formula,
            "rank_value": self.rank_value,
            "k_G_conservative": self.k_g_value(),
            "k_G_rule": "Use k_G = dim(ad G) as the conservative finite Lie-algebra component count; for symbolic families retain the exact dimension formula.",
            "notes": self.notes,
        }


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out-dir", type=Path, default=DEFAULT_OUT_DIR)
    return parser.parse_args()


def entries() -> list[GroupEntry]:
    return [
        GroupEntry(
            key="SU2",
            family="SU(N)",
            display_name="SU(2)",
            class_type="classical",
            compact_simple=True,
            parameter_domain="N = 2",
            adjoint_dimension_formula="N^2 - 1",
            adjoint_dimension_value=3,
            rank_formula="N - 1",
            rank_value=1,
            notes="Compact simply connected A1 representative; locally isomorphic to SO(3).",
        ),
        GroupEntry(
            key="SU3",
            family="SU(N)",
            display_name="SU(3)",
            class_type="classical",
            compact_simple=True,
            parameter_domain="N = 3",
            adjoint_dimension_formula="N^2 - 1",
            adjoint_dimension_value=8,
            rank_formula="N - 1",
            rank_value=2,
            notes="Compact A2 representative used as the non-abelian color baseline.",
        ),
        GroupEntry(
            key="SUN",
            family="SU(N)",
            display_name="SU(N)",
            class_type="classical family",
            compact_simple=True,
            parameter_domain="N >= 2",
            adjoint_dimension_formula="N^2 - 1",
            adjoint_dimension_value=None,
            rank_formula="N - 1",
            rank_value=None,
            notes="Symbolic A_{N-1} family; dimension is retained as an exact formula.",
        ),
        GroupEntry(
            key="SON",
            family="SO(N)",
            display_name="SO(N)",
            class_type="classical family",
            compact_simple=True,
            parameter_domain="N >= 3, excluding the non-simple SO(4) Lie algebra split",
            adjoint_dimension_formula="N(N - 1)/2",
            adjoint_dimension_value=None,
            rank_formula="floor(N/2)",
            rank_value=None,
            notes="Compact orthogonal family; SO(4) is recorded as excluded because so(4) = su(2) + su(2).",
        ),
        GroupEntry(
            key="SpN",
            family="Sp(N)",
            display_name="Sp(N)",
            class_type="classical family",
            compact_simple=True,
            parameter_domain="N >= 1",
            adjoint_dimension_formula="N(2N + 1)",
            adjoint_dimension_value=None,
            rank_formula="N",
            rank_value=None,
            notes="Compact symplectic C_N convention, also written USp(2N).",
        ),
        GroupEntry("G2", "exceptional", "G2", "exceptional", True, "fixed", "14", 14, "2", 2, "Smallest exceptional compact simple Lie group."),
        GroupEntry("F4", "exceptional", "F4", "exceptional", True, "fixed", "52", 52, "4", 4, "Exceptional compact simple Lie group."),
        GroupEntry("E6", "exceptional", "E6", "exceptional", True, "fixed", "78", 78, "6", 6, "Exceptional compact simple Lie group."),
        GroupEntry("E7", "exceptional", "E7", "exceptional", True, "fixed", "133", 133, "7", 7, "Exceptional compact simple Lie group."),
        GroupEntry("E8", "exceptional", "E8", "exceptional", True, "fixed", "248", 248, "8", 8, "Exceptional compact simple Lie group."),
    ]


def build_payload(rows: list[GroupEntry]) -> dict[str, Any]:
    concrete = [row for row in rows if row.adjoint_dimension_value is not None]
    return {
        "artifact": "ym_sprint121_compact_group_parameter_table",
        "schema_version": 1,
        "lane": "GG1-Parameter-Code",
        "worker": "Worker 4",
        "route_decision": "finite-computation-artifact-only",
        "clay_promotion": False,
        "clay_promotion_reason": "Parameter table only; no analytic mass-gap theorem or Clay promotion is claimed.",
        "k_G_conservative_rule": {
            "statement": "Set k_G conservatively to dim(ad G), the real dimension of the compact simple Lie algebra.",
            "concrete_entries": "For fixed entries, k_G is the listed integer adjoint dimension.",
            "symbolic_families": "For SU(N), SO(N), and Sp(N), k_G remains the exact symbolic adjoint-dimension formula over the stated parameter domain.",
            "exclusions": ["SO(4) is excluded from the simple SO(N) family row because so(4) splits as su(2) + su(2)."],
        },
        "entry_count": len(rows),
        "concrete_entry_count": len(concrete),
        "max_concrete_k_G": max(row.adjoint_dimension_value for row in concrete if row.adjoint_dimension_value is not None),
        "entries": [row.to_json() for row in rows],
        "governance": {
            "deterministic": True,
            "external_inputs": [],
            "tests_touched": False,
            "promotion_claimed": False,
        },
    }


def markdown_table(rows: list[GroupEntry]) -> str:
    lines = [
        "| Key | Class | Domain | dim(ad G) | Rank | conservative k_G | Notes |",
        "| --- | --- | --- | --- | --- | --- | --- |",
    ]
    for row in rows:
        rank = str(row.rank_value) if row.rank_value is not None else row.rank_formula
        lines.append(
            "| {key} | {class_type} | {domain} | `{dim}` | `{rank}` | `{kg}` | {notes} |".format(
                key=row.display_name,
                class_type=row.class_type,
                domain=row.parameter_domain,
                dim=row.adjoint_dimension_value
                if row.adjoint_dimension_value is not None
                else row.adjoint_dimension_formula,
                rank=rank,
                kg=row.k_g_value(),
                notes=row.notes,
            )
        )
    return "\n".join(lines)


def build_report(payload: dict[str, Any], rows: list[GroupEntry]) -> str:
    return "\n".join(
        [
            "# YM Sprint 121 GG1 Compact Group Parameter Table",
            "",
            "Route decision: `finite-computation-artifact-only`",
            "",
            "Clay promotion: `false`",
            "",
            "## Conservative k_G rule",
            "",
            "Set `k_G = dim(ad G)` as the conservative real Lie-algebra component count. "
            "Fixed compact simple groups receive integer values; symbolic families retain exact formulas over the stated domains.",
            "",
            "## Table",
            "",
            markdown_table(rows),
            "",
            "## Boundary",
            "",
            "- Deterministic finite computation only.",
            "- No external data inputs.",
            "- No tests edited.",
            "- No Clay promotion, continuum theorem, or mass-gap claim is emitted.",
            "",
            "## Summary",
            "",
            f"- Entries: `{payload['entry_count']}`",
            f"- Concrete entries: `{payload['concrete_entry_count']}`",
            f"- Max concrete conservative k_G: `{payload['max_concrete_k_G']}`",
            "",
        ]
    )


def main() -> None:
    args = parse_args()
    out_dir = args.out_dir
    out_dir.mkdir(parents=True, exist_ok=True)

    rows = entries()
    payload = build_payload(rows)
    (out_dir / SUMMARY_NAME).write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    (out_dir / REPORT_NAME).write_text(build_report(payload, rows))


if __name__ == "__main__":
    main()
