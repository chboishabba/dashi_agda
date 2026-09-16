#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys
from typing import Any

SCHEMA = "slr-world-round-accounting-v1"


def world_growth_receipt(*, prior_canonical_atoms: int, structural_canonical_atoms: int,
                         final_canonical_atoms: int) -> dict[str, Any]:
    prior = int(prior_canonical_atoms)
    structural = int(structural_canonical_atoms)
    final = int(final_canonical_atoms)
    if prior < 0 or structural < 0 or final < 0:
        raise ValueError("canonical atom counts must be non-negative")
    if structural < prior:
        raise ValueError("structural stage cannot delete canonical atoms")
    if final < structural:
        raise ValueError("article-PNF stage cannot delete canonical atoms")
    structural_added = structural - prior
    pnf_added = final - structural
    total_added = final - prior
    return {
        "schema": SCHEMA,
        "prior_canonical_atoms": prior,
        "structural_canonical_atoms": structural,
        "final_canonical_atoms": final,
        "structural_atoms_added": structural_added,
        "article_pnf_atoms_added": pnf_added,
        "total_atoms_added": total_added,
        "component_sum_matches_total": structural_added + pnf_added == total_added,
        "atom_growth_creates_claim_truth": False,
        "candidate_only": True,
        "semantic_promotion": False,
    }


def _load(path: Path) -> dict[str, Any]:
    value = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise RuntimeError(f"expected JSON object: {path}")
    return value


def _canonical_count(payload: dict[str, Any]) -> int:
    summary = payload.get("summary") or {}
    return int(summary.get("canonical_atoms", len(payload.get("canonical_atoms") or [])) or 0)


def parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser()
    p.add_argument("--previous", type=Path, required=True)
    p.add_argument("--structural", type=Path, required=True)
    p.add_argument("--final", type=Path, required=True)
    p.add_argument("--output", type=Path, required=True)
    return p.parse_args()


def main() -> int:
    args = parse_args()
    receipt = world_growth_receipt(
        prior_canonical_atoms=_canonical_count(_load(args.previous)),
        structural_canonical_atoms=_canonical_count(_load(args.structural)),
        final_canonical_atoms=_canonical_count(_load(args.final)),
    )
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(
        "SLR_WORLD_ROUND_ACCOUNTING_RECEIPT "
        f"schema={SCHEMA} structural_atoms_added={receipt['structural_atoms_added']} "
        f"article_pnf_atoms_added={receipt['article_pnf_atoms_added']} "
        f"total_atoms_added={receipt['total_atoms_added']} component_sum_matches_total=true "
        "atom_growth_creates_claim_truth=false candidate_only=true semantic_promotion=false",
        file=sys.stderr,
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
