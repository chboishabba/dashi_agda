#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any

SCHEMA = "slr-world-research-tranche-join-v1"
VALID_STATES = {"world-ready", "retained-source-ready", "source-unpaid"}


def read_jsonl(path: Path) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for line in path.read_text(encoding="utf-8").splitlines():
        if not line.strip():
            continue
        value = json.loads(line)
        if not isinstance(value, dict):
            raise SystemExit(f"expected object row in {path}")
        rows.append(value)
    return rows


def validate(rows: list[dict[str, Any]]) -> None:
    seen: set[str] = set()
    for row in rows:
        tid = str(row.get("tranche_id", ""))
        state = str(row.get("readiness", ""))
        may = bool(row.get("may_contribute_semantic_atoms", False))
        if not tid or tid in seen:
            raise SystemExit(f"duplicate/missing tranche_id: {tid!r}")
        seen.add(tid)
        if state not in VALID_STATES:
            raise SystemExit(f"invalid readiness for {tid}: {state!r}")
        if state != "world-ready" and may:
            raise SystemExit(f"non-world-ready tranche may not contribute semantic atoms: {tid}")
        if bool(row.get("semantic_promotion", False)):
            raise SystemExit(f"semantic promotion forbidden in tranche ledger: {tid}")


def self_check() -> int:
    bad = [{
        "tranche_id": "brexit",
        "readiness": "source-unpaid",
        "may_contribute_semantic_atoms": True,
        "semantic_promotion": False,
    }]
    failed = False
    try:
        validate(bad)
    except SystemExit:
        failed = True
    assert failed, "source-unpaid tranche must not contribute semantic atoms"
    print("SLR_WORLD_RESEARCH_TRANCHE_JOIN_SELF_CHECK schema=slr-world-research-tranche-join-v1 passed=true source_unpaid_contributes_atoms=false", file=sys.stderr)
    return 0


def parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser()
    p.add_argument("--ledger", type=Path)
    p.add_argument("--output", type=Path)
    p.add_argument("--self-check", action="store_true")
    return p.parse_args()


def main() -> int:
    args = parse_args()
    if args.self_check:
        return self_check()
    if not args.ledger or not args.output:
        raise SystemExit("--ledger and --output are required unless --self-check")
    rows = read_jsonl(args.ledger)
    validate(rows)
    payload = {
        "schema": SCHEMA,
        "tranches": rows,
        "summary": {
            "tranches": len(rows),
            "world_ready": sum(1 for r in rows if r["readiness"] == "world-ready"),
            "retained_source_ready": sum(1 for r in rows if r["readiness"] == "retained-source-ready"),
            "source_unpaid": sum(1 for r in rows if r["readiness"] == "source-unpaid"),
            "semantic_atom_contributors": sum(1 for r in rows if bool(r.get("may_contribute_semantic_atoms", False))),
        },
        "source_unpaid_contributes_semantic_atoms": False,
        "readiness_creates_truth": False,
        "candidate_only": True,
        "semantic_promotion": False,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    s = payload["summary"]
    print(
        "SLR_WORLD_RESEARCH_TRANCHE_JOIN_RECEIPT "
        f"schema={SCHEMA} tranches={s['tranches']} world_ready={s['world_ready']} "
        f"retained_source_ready={s['retained_source_ready']} source_unpaid={s['source_unpaid']} "
        f"semantic_atom_contributors={s['semantic_atom_contributors']} "
        "source_unpaid_contributes_atoms=false readiness_creates_truth=false candidate_only=true semantic_promotion=false",
        file=sys.stderr,
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
