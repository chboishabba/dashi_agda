#!/usr/bin/env python3
"""Check that publication diagram assets have reproducible source routes."""

from __future__ import annotations

import argparse
import json
import sys
from dataclasses import asdict, dataclass
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]


@dataclass(frozen=True)
class DiagramRoute:
    name: str
    source: str
    rendered: str
    command: str
    paper: str


ROUTES: tuple[DiagramRoute, ...] = (
    DiagramRoute(
        "Paper 1 NS receipt graph",
        "DASHI/Physics/Closure/NSPaper1ClayTargetReceipt.agda",
        "Docs/diagrams/NSPaper1ClayTargetReceipt.svg",
        "./scripts/render_agda_dependency_graph.sh DASHI/Physics/Closure/NSPaper1ClayTargetReceipt.agda Docs/diagrams",
        "Paper1 NS",
    ),
    DiagramRoute(
        "Paper 3 YM receipt graph",
        "DASHI/Physics/Closure/YMPaper3ClayTargetReceipt.agda",
        "Docs/diagrams/YMPaper3ClayTargetReceipt.svg",
        "./scripts/render_agda_dependency_graph.sh DASHI/Physics/Closure/YMPaper3ClayTargetReceipt.agda Docs/diagrams",
        "Paper3 YM",
    ),
    DiagramRoute(
        "Paper 8 unification theorem map",
        "Docs/diagrams/Paper8UnificationMap.puml",
        "Docs/diagrams/Paper8UnificationMap.puml",
        "plantuml Docs/diagrams/Paper8UnificationMap.puml",
        "Paper8 Unification",
    ),
    DiagramRoute(
        "Unified physics theorem graph",
        "DASHI/Physics/Closure/UnifiedPhysicsTheorem.agda",
        "Docs/diagrams/UnifiedPhysicsTheorem.svg",
        "./scripts/render_agda_dependency_graph.sh DASHI/Physics/Closure/UnifiedPhysicsTheorem.agda Docs/diagrams",
        "Paper8 Unification",
    ),
)


def parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, default=REPO_ROOT)
    parser.add_argument("--json", action="store_true", help="emit route status as JSON")
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = parse_args(sys.argv[1:] if argv is None else argv)
    repo_root = args.repo_root.resolve()
    router = repo_root / "scripts/render_agda_dependency_graph.sh"
    rows = []
    ok = True
    for route in ROUTES:
        source_exists = (repo_root / route.source).exists()
        rendered_exists = (repo_root / route.rendered).exists()
        command_exists = router.exists() if route.command.startswith("./scripts/render_agda_dependency_graph.sh") else True
        route_ok = source_exists and rendered_exists and command_exists
        ok = ok and route_ok
        rows.append(
            {
                **asdict(route),
                "source_exists": source_exists,
                "rendered_exists": rendered_exists,
                "command_exists": command_exists,
                "ok": route_ok,
            }
        )

    if args.json:
        print(json.dumps({"routes": rows, "ok": ok}, indent=2, sort_keys=True))
    else:
        for row in rows:
            status = "PASS" if row["ok"] else "FAIL"
            print(f"{status} {row['paper']}: {row['name']} -> {row['command']}")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
