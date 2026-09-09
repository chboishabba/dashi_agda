#!/usr/bin/env python3
"""Build deterministic Wikidata QID coverage indexes for Agda modules.

This scanner is deliberately syntactic.  A Q123 token observed in a module is
an *observed external identity token*, not proof that the item is correct,
resolved, publication-identical, or authoritative.

If Docs/DashiDeweyModuleCatalog.tsv exists, its Dewey parent cluster is joined
onto the QID catalog.  The script therefore composes with the Dewey projection
without making Dewey IDs and QIDs interchangeable.
"""

from __future__ import annotations

import argparse
import csv
import re
from collections import Counter, defaultdict
from pathlib import Path

QID_RE = re.compile(r"(?<![A-Za-z0-9_])Q([1-9][0-9]{0,15})(?![A-Za-z0-9_])")
DOI_RE = re.compile(r"10\.\d{4,9}/[-._;()/:A-Z0-9]+", re.IGNORECASE)


def agda_modules(root: Path) -> list[Path]:
    return sorted(
        p for p in root.rglob("*.agda")
        if ".git" not in p.parts
    )


def load_dewey(path: Path) -> dict[str, str]:
    if not path.exists():
        return {}
    with path.open(newline="", encoding="utf-8") as fh:
        reader = csv.DictReader(fh, delimiter="\t")
        fields = reader.fieldnames or []
        module_field = next(
            (x for x in ("module", "path", "module_path") if x in fields),
            None,
        )
        dewey_field = next(
            (x for x in ("dewey_id", "dewey", "parent_cluster_id") if x in fields),
            None,
        )
        if not module_field or not dewey_field:
            raise SystemExit(
                f"Cannot join Dewey catalog {path}: expected module/path and dewey column"
            )
        out: dict[str, str] = {}
        for row in reader:
            key = row[module_field].replace("\\", "/")
            out[key] = row[dewey_field]
        return out


def module_name(rel: str) -> str:
    if rel.endswith(".agda"):
        rel = rel[:-5]
    return rel.replace("/", ".")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", type=Path, default=Path("."))
    parser.add_argument(
        "--dewey-catalog",
        type=Path,
        default=Path("Docs/DashiDeweyModuleCatalog.tsv"),
    )
    parser.add_argument(
        "--module-output",
        type=Path,
        default=Path("Docs/DashiQidModuleCatalog.tsv"),
    )
    parser.add_argument(
        "--cluster-output",
        type=Path,
        default=Path("Docs/DashiQidParentClusterCoverage.tsv"),
    )
    args = parser.parse_args()

    root = args.root.resolve()
    dewey_path = args.dewey_catalog
    if not dewey_path.is_absolute():
        dewey_path = root / dewey_path
    dewey = load_dewey(dewey_path)

    rows: list[dict[str, object]] = []
    cluster_stats: dict[str, Counter[str]] = defaultdict(Counter)
    cluster_qids: dict[str, set[str]] = defaultdict(set)

    for path in agda_modules(root):
        rel = path.relative_to(root).as_posix()
        text = path.read_text(encoding="utf-8", errors="replace")
        qids = sorted({f"Q{m.group(1)}" for m in QID_RE.finditer(text)})
        dois = sorted(set(DOI_RE.findall(text)))
        dewey_id = dewey.get(rel, dewey.get(module_name(rel), "unjoined"))
        rows.append(
            {
                "module_path": rel,
                "dewey_id": dewey_id,
                "qid_count": len(qids),
                "qids": ";".join(qids) if qids else "none-observed",
                "doi_count": len(dois),
                "has_qid": int(bool(qids)),
                "has_doi": int(bool(dois)),
            }
        )
        s = cluster_stats[dewey_id]
        s["modules"] += 1
        s["modules_with_qid"] += int(bool(qids))
        s["modules_with_doi"] += int(bool(dois))
        s["modules_with_both"] += int(bool(qids) and bool(dois))
        cluster_qids[dewey_id].update(qids)

    module_out = args.module_output
    cluster_out = args.cluster_output
    if not module_out.is_absolute():
        module_out = root / module_out
    if not cluster_out.is_absolute():
        cluster_out = root / cluster_out
    module_out.parent.mkdir(parents=True, exist_ok=True)
    cluster_out.parent.mkdir(parents=True, exist_ok=True)

    module_fields = [
        "module_path", "dewey_id", "qid_count", "qids",
        "doi_count", "has_qid", "has_doi",
    ]
    with module_out.open("w", newline="", encoding="utf-8") as fh:
        writer = csv.DictWriter(fh, fieldnames=module_fields, delimiter="\t")
        writer.writeheader()
        writer.writerows(rows)

    cluster_fields = [
        "dewey_id", "modules", "modules_with_qid", "qid_module_coverage",
        "distinct_qids", "modules_with_doi", "doi_module_coverage",
        "modules_with_both", "joint_module_coverage",
    ]
    with cluster_out.open("w", newline="", encoding="utf-8") as fh:
        writer = csv.DictWriter(fh, fieldnames=cluster_fields, delimiter="\t")
        writer.writeheader()
        for dewey_id in sorted(cluster_stats):
            s = cluster_stats[dewey_id]
            n = s["modules"]
            writer.writerow(
                {
                    "dewey_id": dewey_id,
                    "modules": n,
                    "modules_with_qid": s["modules_with_qid"],
                    "qid_module_coverage": f"{s['modules_with_qid']/n:.6f}",
                    "distinct_qids": len(cluster_qids[dewey_id]),
                    "modules_with_doi": s["modules_with_doi"],
                    "doi_module_coverage": f"{s['modules_with_doi']/n:.6f}",
                    "modules_with_both": s["modules_with_both"],
                    "joint_module_coverage": f"{s['modules_with_both']/n:.6f}",
                }
            )

    total = len(rows)
    with_qid = sum(int(r["has_qid"]) for r in rows)
    distinct = len({q for r in rows for q in str(r["qids"]).split(";") if q.startswith("Q")})
    print(f"modules={total}")
    print(f"modules_with_qid={with_qid}")
    print(f"qid_module_coverage={with_qid/total:.6f}" if total else "qid_module_coverage=0")
    print(f"distinct_qids={distinct}")
    print(f"dewey_join={'yes' if dewey else 'no'}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
