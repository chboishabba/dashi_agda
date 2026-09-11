#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any

SCHEMA = "slr-review-disposition-v1"


def load(path: Path) -> dict[str, Any]:
    value = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise SystemExit(f"expected JSON object: {path}")
    return value


def unresolved_dimension(fibre: dict[str, Any]) -> bool:
    # Only genuinely open/ambiguous states block separate promotion review.
    # Bounded provenance states such as source-date or claim-relative-primary
    # scope are constraints that are attached, not residual debt by themselves.
    unresolved = {
        "residual-fibre",
        "residual-observed",
        "unresolved",
        "alternatives-retained",
    }
    for value in (fibre.get("dimensions") or {}).values():
        if str((value or {}).get("status", "")) in unresolved:
            return True
    return False


def disposition(fibre: dict[str, Any], adequate: bool | None) -> tuple[str, list[str]]:
    reasons: list[str] = []
    if not bool(fibre.get("compatible", False)):
        reasons.append("consumer-veto")
        return "reject-by-consumer-veto", reasons
    if adequate is not True:
        reasons.append("consumer-adequacy-unpaid" if adequate is False else "consumer-adequacy-unsupplied")
        if unresolved_dimension(fibre):
            reasons.append("world-constraint-residual-open")
        return "abstain-for-residual", reasons
    if unresolved_dimension(fibre):
        reasons.append("world-constraint-residual-open")
        return "abstain-for-residual", reasons
    reasons.append("compatible-and-consumer-adequate")
    return "eligible-for-separate-promotion-review", reasons


def parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser()
    p.add_argument("--world-model", type=Path, required=True)
    p.add_argument("--fibres", type=Path, required=True)
    p.add_argument("--consumer-gates", type=Path)
    p.add_argument("--output", type=Path, required=True)
    return p.parse_args()


def main() -> int:
    args = parse_args()
    model = load(args.world_model)
    sidecar = load(args.fibres)
    gates: dict[str, Any] = load(args.consumer_gates) if args.consumer_gates else {}

    if model.get("model_status") != "candidate":
        raise SystemExit("review consumer only accepts candidate world models")
    metadata = model.get("metadata") or {}
    if metadata.get("world_constraint_status") != "attached-candidate-only":
        raise SystemExit("typed world constraint fibre must be attached before review")
    if bool(metadata.get("semantic_promotion", False)):
        raise SystemExit("input candidate model already claims semantic promotion")
    if sidecar.get("schema") != "slr-world-constraint-fibre-v1":
        raise SystemExit("unexpected world constraint fibre schema")

    default_adequate_raw = gates.get("consumer_adequate", None)
    default_adequate = default_adequate_raw if isinstance(default_adequate_raw, bool) else None
    per_candidate = gates.get("candidate_adequacy") or {}

    rows: list[dict[str, Any]] = []
    for fibre in sidecar.get("constraint_fibres", []):
        candidate_id = str(fibre.get("candidate_id", ""))
        raw = per_candidate.get(candidate_id, default_adequate)
        adequate = raw if isinstance(raw, bool) else None
        disp, reasons = disposition(fibre, adequate)
        rows.append(
            {
                "candidate_id": candidate_id,
                "candidate_kind": fibre.get("candidate_kind", ""),
                "disposition": disp,
                "reasons": reasons,
                "compatible": bool(fibre.get("compatible", False)),
                "consumer_adequate": adequate,
                "promotion_performed": False,
                "truth_promoted": False,
            }
        )

    counts: dict[str, int] = {}
    for row in rows:
        counts[row["disposition"]] = counts.get(row["disposition"], 0) + 1

    output = {
        "schema": SCHEMA,
        "model_id": model.get("model_id", ""),
        "world_constraint_schema": sidecar.get("schema", ""),
        "consumer_gate_reference": str(args.consumer_gates) if args.consumer_gates else "unsupplied",
        "consumer_reference": gates.get("consumer_reference", "generic-unsupplied-consumer"),
        "current_residual": gates.get("current_residual", "unsupplied"),
        "dispositions": rows,
        "summary": counts,
        "promotion_performed": False,
        "semantic_promotion": False,
        "candidate_only": True,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(output, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(
        "SLR_REVIEW_DISPOSITION_RECEIPT "
        f"schema={SCHEMA} model_id={output['model_id']} candidates={len(rows)} "
        f"reject={counts.get('reject-by-consumer-veto',0)} "
        f"abstain={counts.get('abstain-for-residual',0)} "
        f"eligible={counts.get('eligible-for-separate-promotion-review',0)} "
        f"consumer={output['consumer_reference']} current_residual={output['current_residual']} "
        "promotion_performed=false semantic_promotion=false candidate_only=true",
        file=sys.stderr,
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
