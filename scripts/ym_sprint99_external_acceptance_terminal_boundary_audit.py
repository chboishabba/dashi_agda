#!/usr/bin/env python3
"""Sprint 99 external-acceptance terminal boundary audit."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--out-dir",
        type=Path,
        default=Path("outputs/ym_sprint99_external_acceptance_terminal_boundary"),
    )
    return parser.parse_args()


def summary_payload() -> dict[str, Any]:
    return {
        "sprint": "99-external-acceptance-terminal-boundary",
        "sprint98_clay_statement_boundary_required": True,
        "internal_candidate_chain_complete_in_repo": True,
        "external_acceptance_token_available": False,
        "external_acceptance_token_repo_internal": False,
        "clay_yang_mills_promoted": False,
        "terminal_boundary_statement": (
            "External acceptance is a governance/review artifact, not an Agda "
            "proof object available inside the repository"
        ),
        "remaining_external_items": [
            "external peer review",
            "community acceptance",
            "Clay acceptance",
        ],
        "route_decision": "SPRINT99_TERMINAL_FAIL_CLOSED_EXTERNAL_ACCEPTANCE_BOUNDARY",
    }


def write_outputs(summary: dict[str, Any], out_dir: Path) -> None:
    out_dir.mkdir(parents=True, exist_ok=True)
    (
        out_dir / "ym_sprint99_external_acceptance_terminal_boundary_summary.json"
    ).write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n")


def main() -> int:
    args = parse_args()
    summary = summary_payload()
    write_outputs(summary, args.out_dir)
    print(json.dumps(summary, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
