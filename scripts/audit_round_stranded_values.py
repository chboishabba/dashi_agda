#!/usr/bin/env python3

from __future__ import annotations

import argparse
import csv
import json

from collections import Counter, defaultdict
from pathlib import Path

from _stranded_common import *


CANDIDATE_CLASSES = {
    "stranded_signature",
    "canonical_name_collision",
    "stranded_proof_change",
    "alternate_proof",
    "alternate_implementation",
}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--db", default=".dashi/repository.sqlite3")
    ap.add_argument("--config", default=".dashi/canonical-roots.json")
    ap.add_argument("--out", default=".dashi/round-stranded")
    args = ap.parse_args()

    db = Path(args.db)
    cfgp = Path(args.config)
    out = Path(args.out)
    out.mkdir(parents=True, exist_ok=True)

    cfg = json.loads(cfgp.read_text())
    requested = cfg["roots"]

    conn = connect(db)
    paths = module_paths(conn)
    available = set(paths)
    imports, reverse = load_import_graph(conn)

    roots = [m for m in requested if m in available]
    missing = [m for m in requested if m not in available]

    if not roots:
        raise SystemExit("none of the configured canonical roots exists")

    canon = closure(imports, roots, available)
    canon_rounds = sorted(m for m in canon if is_round(m))

    rounds = {m: p for m, p in paths.items() if is_round(m)}
    round_parents = defaultdict(set)
    round_children = defaultdict(set)

    for child in rounds:
        for parent in imports.get(child, ()):
            if parent in rounds:
                round_parents[child].add(parent)
                round_children[parent].add(child)

    leaves = sorted(m for m in rounds if not round_children.get(m))

    cdecls = decls_for_modules(conn, canon)
    cexact, csig, cname = indexes(cdecls)

    cache = {}

    def mdecls(module):
        if module not in cache:
            cache[module] = decls_for_modules(conn, [module])
        return cache[module]

    records = []
    summaries = []

    for leaf in leaves:
        parents = sorted(round_parents.get(leaf, ()))
        pdecls = [d for parent in parents for d in mdecls(parent)]
        pexact, psig, _ = indexes(pdecls)
        counts = Counter()

        for d in mdecls(leaf):
            sig = d["signature_sha256"]
            body = d["body_sha256"]
            key = (sig, body)

            if pexact.get(key):
                cls = "inherited_exact"
            elif psig.get(sig):
                if cexact.get(key):
                    cls = "proof_change_already_canonical"
                elif csig.get(sig):
                    cls = "alternate_proof"
                else:
                    cls = "stranded_proof_change"
            else:
                if cexact.get(key):
                    cls = "introduced_but_already_canonical"
                elif csig.get(sig):
                    cls = "alternate_implementation"
                elif cname.get(d["name"]):
                    cls = "canonical_name_collision"
                else:
                    cls = "stranded_signature"

            counts[cls] += 1
            examples = (
                cexact.get(key)
                or csig.get(sig)
                or cname.get(d["name"])
                or []
            )

            records.append(
                {
                    "record_id": stable_id(leaf, d["symbol_id"], cls),
                    "leaf_module": leaf,
                    "leaf_file": rounds[leaf],
                    "family": family_of(leaf),
                    "direct_round_parents": " | ".join(parents),
                    "parent_count": len(parents),
                    "symbol_id": d["symbol_id"],
                    "name": d["name"],
                    "normalized_signature": d["normalized_signature"],
                    "signature_sha256": sig,
                    "body_sha256": body,
                    "classification": cls,
                    "canonical_signature_matches": len(csig.get(sig, [])),
                    "canonical_exact_matches": len(cexact.get(key, [])),
                    "canonical_same_name_matches": len(cname.get(d["name"], [])),
                    "canonical_examples": " | ".join(
                        x["symbol_id"] for x in examples[:3]
                    ),
                }
            )

        summaries.append(
            {
                "leaf_module": leaf,
                "leaf_file": rounds[leaf],
                "family": family_of(leaf),
                "direct_round_parents": " | ".join(parents),
                "parent_count": len(parents),
                "signature_count": sum(counts.values()),
                **counts,
            }
        )

    def write_csv(path, rows):
        if not rows:
            path.write_text("")
            return
        fields = sorted({key for row in rows for key in row})
        with path.open("w", newline="", encoding="utf-8") as f:
            writer = csv.DictWriter(f, fieldnames=fields)
            writer.writeheader()
            writer.writerows(rows)

    candidates = [
        r for r in records if r["classification"] in CANDIDATE_CLASSES
    ]

    write_csv(out / "terminal-round-symbols.csv", records)
    write_csv(out / "terminal-round-leaves.csv", summaries)
    write_csv(out / "stranded-candidates.csv", candidates)

    totals = Counter(r["classification"] for r in records)
    summary = {
        "canonical_roots": roots,
        "missing_canonical_roots": missing,
        "canonical_module_count": len(canon),
        "canonical_round_module_count": len(canon_rounds),
        "canonical_round_modules": canon_rounds,
        "round_module_count": len(rounds),
        "terminal_leaf_count": len(leaves),
        "terminal_signature_count": len(records),
        "candidate_count": len(candidates),
        "classification_counts": dict(totals),
    }

    (out / "summary.json").write_text(
        json.dumps(summary, indent=2, sort_keys=True) + "\n"
    )
    print(json.dumps(summary, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
