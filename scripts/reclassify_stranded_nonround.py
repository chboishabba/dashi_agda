#!/usr/bin/env python3

from __future__ import annotations

import argparse
import csv
import json

from collections import Counter
from pathlib import Path

from _stranded_common import connect, decls_for_modules, indexes, is_round, module_paths


def domain_for(module: str) -> str:
    if module.startswith("DASHI.Physics.Closure."):
        return "NS"
    if module.startswith("DASHI.Papers.NavierStokes."):
        return "NS"
    if module.startswith("DASHI.Physics.YangMills."):
        return "YM"
    return "OTHER"


def same_domain(candidate_module: str, match_module: str) -> bool:
    a = domain_for(candidate_module)
    b = domain_for(match_module)
    return a != "OTHER" and a == b


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--db", default=".dashi/repository.sqlite3")
    ap.add_argument(
        "--candidates",
        default=".dashi/round-stranded/stranded-candidates.csv",
    )
    ap.add_argument(
        "--out",
        default=".dashi/round-stranded/nonround-reclassification.csv",
    )
    ap.add_argument(
        "--summary",
        default=".dashi/round-stranded/nonround-summary.json",
    )
    args = ap.parse_args()

    conn = connect(Path(args.db))
    paths = module_paths(conn)
    nonround_modules = sorted(module for module in paths if not is_round(module))

    print(
        f"loading declarations from {len(nonround_modules):,} non-Round modules..."
    )

    decls = decls_for_modules(conn, nonround_modules)
    exact, by_sig, by_name = indexes(decls)

    rows = list(csv.DictReader(open(args.candidates, encoding="utf-8")))
    output = []
    counts = Counter()

    for row in rows:
        module = row["leaf_module"]
        sig = row["signature_sha256"]
        body = row["body_sha256"]
        name = row["name"]

        exact_matches = exact.get((sig, body), [])
        signature_matches = by_sig.get(sig, [])
        name_matches = by_name.get(name, [])

        domain_exact = [
            match
            for match in exact_matches
            if same_domain(module, match["module"])
        ]
        domain_signature = [
            match
            for match in signature_matches
            if same_domain(module, match["module"])
        ]
        domain_name = [
            match
            for match in name_matches
            if same_domain(module, match["module"])
        ]

        if domain_exact:
            disposition = "DOMAIN_NONROUND_EXACT"
        elif domain_signature:
            disposition = "DOMAIN_NONROUND_SIGNATURE"
        elif exact_matches:
            disposition = "GLOBAL_NONROUND_EXACT"
        elif signature_matches:
            disposition = "GLOBAL_NONROUND_SIGNATURE"
        elif domain_name:
            disposition = "DOMAIN_NAME_COLLISION"
        elif name_matches:
            disposition = "GLOBAL_NAME_COLLISION"
        else:
            disposition = "TRULY_UNMATCHED_NONROUND"

        counts[disposition] += 1

        preferred = (
            domain_exact
            or domain_signature
            or exact_matches
            or signature_matches
            or domain_name
            or name_matches
        )

        output.append(
            {
                **row,
                "nonround_disposition": disposition,
                "domain": domain_for(module),
                "nonround_exact_matches": len(exact_matches),
                "nonround_signature_matches": len(signature_matches),
                "nonround_name_matches": len(name_matches),
                "domain_exact_matches": len(domain_exact),
                "domain_signature_matches": len(domain_signature),
                "domain_name_matches": len(domain_name),
                "nonround_examples": " | ".join(
                    match["symbol_id"] for match in preferred[:5]
                ),
            }
        )

    Path(args.out).parent.mkdir(parents=True, exist_ok=True)

    if output:
        fields = list(output[0].keys())
        with open(args.out, "w", newline="", encoding="utf-8") as f:
            writer = csv.DictWriter(f, fieldnames=fields)
            writer.writeheader()
            writer.writerows(output)

    summary = {
        "candidate_count": len(rows),
        "nonround_module_count": len(nonround_modules),
        "nonround_declaration_count": len(decls),
        "dispositions": dict(counts),
        "truly_unmatched_count": counts["TRULY_UNMATCHED_NONROUND"],
    }

    Path(args.summary).write_text(
        json.dumps(summary, indent=2, sort_keys=True) + "\n"
    )
    print(json.dumps(summary, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
