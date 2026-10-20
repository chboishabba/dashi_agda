#!/usr/bin/env python3
"""Join SABIO kinetic parameter candidates to the executed BH4 reaction network.

This is an adjudication worklist, not a flux-bound generator. Each normalized
SABIO parameter candidate inherits its exact panel protein and the finite Rhea
columns linked to that protein. The output deliberately leaves
`usable_for_flux_bound=false` until assay context, same-object/compartment/time
coordinates, unit normalization and a justified kinetic-to-flux translation are
supplied.
"""

from __future__ import annotations

import argparse
import json
from collections import Counter, defaultdict
from pathlib import Path
from typing import Any


def reaction_links(rhea: dict) -> dict[str, list[str]]:
    out: dict[str, set[str]] = defaultdict(set)
    for row in rhea.get("protein_reaction_links", []):
        acc = str(row.get("accession") or "").strip()
        rid = str(row.get("rhea_id") or "").strip()
        if acc and rid:
            out[acc].add(rid)
    return {acc: sorted(ids) for acc, ids in out.items()}


def parameter_kind_hint(candidate: dict) -> str:
    text = " ".join(str(candidate.get(k) or "") for k in ("parameter_name", "parameter_type", "sbo_term")).lower()
    if any(token in text for token in ("kcat", "turnover number", "catalytic constant")):
        return "catalytic-constant-like"
    if any(token in text for token in ("ki", "inhibition constant", "inhibitory constant", "ic50")):
        return "inhibitory-like"
    if any(token in text for token in ("km", "michaelis", "affinity", "kd", "dissociation constant")):
        return "affinity-like"
    if any(token in text for token in ("vmax", "v_max", "maximum velocity", "specific activity", "reaction rate", "velocity", "rate constant")):
        return "rate-like"
    if any(token in text for token in ("concentration", "substrate concentration", "enzyme concentration")):
        return "concentration-like"
    if "turnover" in text:
        return "turnover-like"
    return "unclassified"


def build(sabio: dict, rhea: dict, matrix: dict) -> dict:
    finite = set(str(x) for x in matrix.get("reaction_index", []))
    links = reaction_links(rhea)
    candidates = list(sabio.get("kinetic_parameter_candidates", []))
    rows: list[dict[str, Any]] = []

    for candidate in candidates:
        acc = str(candidate.get("accession") or "").strip()
        all_rhea = links.get(acc, [])
        finite_rhea = sorted(rid for rid in all_rhea if rid in finite)
        rows.append({
            "symbol": candidate.get("symbol"),
            "accession": acc,
            "entry_id": candidate.get("entry_id"),
            "parameter_name": candidate.get("parameter_name"),
            "parameter_type": candidate.get("parameter_type"),
            "sbo_term": candidate.get("sbo_term"),
            "n_start_value": candidate.get("n_start_value"),
            "n_end_value": candidate.get("n_end_value"),
            "unit": candidate.get("unit"),
            "parameter_kind_hint": parameter_kind_hint(candidate),
            "protein_rhea_ids": all_rhea,
            "finite_matrix_rhea_ids": finite_rhea,
            "maps_to_finite_matrix_column": bool(finite_rhea),
            "usable_for_flux_bound": False,
            "unpaid_obligations": [
                "assay/context identity",
                "same-object/compartment/time translation",
                "normalized solver flux unit",
                "kinetic-parameter-to-network-flux justification",
            ],
            "raw_parameter": candidate.get("raw"),
        })

    by_kind = Counter(row["parameter_kind_hint"] for row in rows)
    mapped = [row for row in rows if row["maps_to_finite_matrix_column"]]
    mapped_reactions = sorted({rid for row in mapped for rid in row["finite_matrix_rhea_ids"]})
    uncovered = sorted(finite - set(mapped_reactions))
    accessions_with_candidates = sorted({row["accession"] for row in rows if row["accession"]})

    return {
        "schema": "dashi.bh4-sabio-adjudication.v2",
        "source_sabio_schema": sabio.get("schema"),
        "source_rhea_schema": rhea.get("schema"),
        "source_matrix_schema": matrix.get("schema"),
        "kinetic_entry_count": sabio.get("kinetic_entry_count"),
        "parameter_candidate_count": len(rows),
        "parameter_candidates_mapped_to_finite_matrix": len(mapped),
        "proteins_with_parameter_candidates": len(accessions_with_candidates),
        "finite_reactions_with_parameter_candidates": mapped_reactions,
        "uncovered_finite_reactions": uncovered,
        "finite_reaction_candidate_coverage": len(mapped_reactions),
        "parameter_kind_counts": dict(sorted(by_kind.items())),
        "rows": rows,
        "promotion_boundary": {
            "parameter_candidate_creates_flux_bound": False,
            "rate_like_hint_creates_flux_bound": False,
            "sbo_term_creates_flux_bound": False,
            "protein_to_rhea_link_creates_same_assay_reaction_identity": False,
            "mapped_parameter_creates_same_compartment_state": False,
            "candidate_coverage_creates_allocator_causality": False,
            "candidate_coverage_creates_disease_mechanism": False,
        },
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--sabio", type=Path, required=True)
    parser.add_argument("--rhea", type=Path, required=True)
    parser.add_argument("--matrix", type=Path, required=True)
    parser.add_argument("-o", "--output", type=Path)
    args = parser.parse_args()
    result = build(
        json.loads(args.sabio.read_text(encoding="utf-8")),
        json.loads(args.rhea.read_text(encoding="utf-8")),
        json.loads(args.matrix.read_text(encoding="utf-8")),
    )
    text = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text, encoding="utf-8")
    else:
        print(text, end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
