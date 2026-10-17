#!/usr/bin/env python3

from __future__ import annotations

import argparse
import csv
import json

from collections import defaultdict
from pathlib import Path

from _stranded_common import *


def topo_ancestors(start, parents):
    seen = set()
    stack = [start]

    while stack:
        module = stack.pop()
        if module in seen:
            continue
        seen.add(module)
        stack.extend(parents.get(module, ()))

    return seen


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--db", default=".dashi/repository.sqlite3")
    ap.add_argument("--config", default=".dashi/canonical-roots.json")
    ap.add_argument(
        "--candidates",
        default=".dashi/round-stranded/stranded-candidates.csv",
    )
    ap.add_argument(
        "--out",
        default=".dashi/round-stranded/lineage-receipts.jsonl",
    )
    args = ap.parse_args()

    conn = connect(Path(args.db))
    cfg = json.loads(Path(args.config).read_text())

    paths = module_paths(conn)
    available = set(paths)
    imports, _ = load_import_graph(conn)

    roots = [root for root in cfg["roots"] if root in available]
    canon = closure(imports, roots, available)
    cexact, csig, cname = indexes(decls_for_modules(conn, canon))

    rounds = {module for module in available if is_round(module)}
    parents = defaultdict(set)
    children = defaultdict(set)

    for child in rounds:
        for parent in imports.get(child, ()):
            if parent in rounds:
                parents[child].add(parent)
                children[parent].add(child)

    candidate_rows = list(
        csv.DictReader(open(args.candidates, encoding="utf-8"))
    )
    leaves = sorted({row["leaf_module"] for row in candidate_rows})
    receipts = []

    for leaf in leaves:
        ancestors = topo_ancestors(leaf, parents)
        decls = decls_for_modules(conn, ancestors)
        by_sig = defaultdict(list)

        for d in decls:
            by_sig[d["signature_sha256"]].append(d)

        leaf_candidates = [
            row for row in candidate_rows if row["leaf_module"] == leaf
        ]
        dispositions = []

        for candidate in leaf_candidates:
            sig = candidate["signature_sha256"]
            body = candidate["body_sha256"]
            name = candidate["name"]

            occurrences = by_sig.get(sig, [])
            modules = sorted({d["module"] for d in occurrences})
            bodies = sorted({d["body_sha256"] for d in occurrences})

            exact = cexact.get((sig, body), [])
            sig_matches = csig.get(sig, [])
            name_matches = cname.get(name, [])

            if exact:
                disposition = "CANONICAL_EXACT"
            elif sig_matches:
                disposition = "CANONICAL_SIGNATURE"
            elif name_matches:
                disposition = "CANONICAL_NAME_COLLISION"
            elif len(bodies) > 1:
                disposition = "HISTORICAL_MUTATION_UNMATCHED"
            else:
                disposition = "UNMATCHED_LINEAGE_VALUE"

            dispositions.append(
                {
                    "record_id": candidate["record_id"],
                    "name": name,
                    "signature_sha256": sig,
                    "body_sha256": body,
                    "classification": candidate["classification"],
                    "lineage_occurrence_modules": modules,
                    "lineage_distinct_bodies": len(bodies),
                    "disposition": disposition,
                    "canonical_examples": [
                        x["symbol_id"]
                        for x in (exact or sig_matches or name_matches)[:5]
                    ],
                }
            )

        unresolved = [
            d
            for d in dispositions
            if d["disposition"]
            in {
                "CANONICAL_NAME_COLLISION",
                "HISTORICAL_MUTATION_UNMATCHED",
                "UNMATCHED_LINEAGE_VALUE",
            }
        ]

        receipts.append(
            {
                "receipt_version": 1,
                "leaf": leaf,
                "family": family_of(leaf),
                "ancestor_round_count": len(ancestors),
                "candidate_count": len(dispositions),
                "unresolved_count": len(unresolved),
                "archive_status": (
                    "UNRESOLVED"
                    if unresolved
                    else "EXTRACTED_OR_SUPERSEDED"
                ),
                "candidates": dispositions,
            }
        )

    out = Path(args.out)
    out.parent.mkdir(parents=True, exist_ok=True)

    with out.open("w", encoding="utf-8") as f:
        for receipt in receipts:
            f.write(json.dumps(receipt, sort_keys=True) + "\n")

    print(
        json.dumps(
            {
                "receipt_count": len(receipts),
                "unresolved_lineages": sum(
                    r["archive_status"] == "UNRESOLVED" for r in receipts
                ),
                "output": str(out),
            },
            indent=2,
        )
    )


if __name__ == "__main__":
    main()
