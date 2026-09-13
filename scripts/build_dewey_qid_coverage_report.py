#!/usr/bin/env python3
"""Build a parent-cluster knowledge-coverage quality report.

Input is the deterministic cluster TSV produced by build_qid_coverage_index.py.
The report keeps subject volume, DOI density, QID density and DOI+QID joint
coverage separate.  Thresholds are policy parameters, not mathematical facts.

No row is allowed to infer source absence, theorem authority, or semantic truth
from missing DOI/QID metadata.
"""

from __future__ import annotations

import argparse
import csv
from dataclasses import dataclass
from pathlib import Path


@dataclass(frozen=True)
class Thresholds:
    developing: float
    strong: float


def band(value: float, t: Thresholds) -> str:
    if value >= t.strong:
        return "strong"
    if value >= t.developing:
        return "developing"
    return "sparse"


def ffloat(row: dict[str, str], key: str) -> float:
    try:
        return float(row[key])
    except (KeyError, ValueError):
        raise SystemExit(f"missing/invalid numeric column: {key}")


def fint(row: dict[str, str], key: str) -> int:
    try:
        return int(row[key])
    except (KeyError, ValueError):
        raise SystemExit(f"missing/invalid integer column: {key}")


def load_labels(path: Path | None) -> dict[str, str]:
    if path is None or not path.exists():
        return {}
    labels: dict[str, str] = {}
    with path.open(newline="", encoding="utf-8") as fh:
        reader = csv.DictReader(fh, delimiter="\t")
        fields = reader.fieldnames or []
        id_field = next(
            (x for x in ("dewey_id", "dewey", "parent_cluster_id") if x in fields),
            None,
        )
        label_field = next(
            (x for x in ("cluster", "label", "cluster_label", "description") if x in fields),
            None,
        )
        if id_field and label_field:
            for row in reader:
                labels[row[id_field]] = row[label_field]
    return labels


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--cluster-tsv",
        type=Path,
        default=Path("Docs/DashiQidParentClusterCoverage.tsv"),
    )
    parser.add_argument(
        "--dewey-map",
        type=Path,
        default=Path("Docs/DashiDeweyMap.tsv"),
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=Path("Docs/DashiKnowledgeCoverageAudit.md"),
    )
    parser.add_argument(
        "--developing-threshold",
        type=float,
        default=0.10,
        help="metadata module-density threshold for developing coverage",
    )
    parser.add_argument(
        "--strong-threshold",
        type=float,
        default=0.40,
        help="metadata module-density threshold for strong coverage",
    )
    args = parser.parse_args()

    if not (0.0 <= args.developing_threshold <= args.strong_threshold <= 1.0):
        raise SystemExit("thresholds must satisfy 0 <= developing <= strong <= 1")

    t = Thresholds(args.developing_threshold, args.strong_threshold)
    labels = load_labels(args.dewey_map)

    with args.cluster_tsv.open(newline="", encoding="utf-8") as fh:
        rows = list(csv.DictReader(fh, delimiter="\t"))
    if not rows:
        raise SystemExit(f"no cluster rows in {args.cluster_tsv}")

    audited: list[dict[str, object]] = []
    for row in rows:
        dewey = row.get("dewey_id", "")
        modules = fint(row, "modules")
        doi = ffloat(row, "doi_module_coverage")
        qid = ffloat(row, "qid_module_coverage")
        joint = ffloat(row, "joint_module_coverage")
        audited.append(
            {
                "dewey": dewey,
                "label": labels.get(dewey, ""),
                "modules": modules,
                "doi": doi,
                "qid": qid,
                "joint": joint,
                "doi_band": band(doi, t),
                "qid_band": band(qid, t),
                "joint_band": band(joint, t),
                "distinct_qids": fint(row, "distinct_qids"),
            }
        )

    by_volume = sorted(audited, key=lambda r: (-int(r["modules"]), str(r["dewey"])))
    by_joint = sorted(
        audited,
        key=lambda r: (-float(r["joint"]), -int(r["modules"]), str(r["dewey"])),
    )
    weak_joint = sorted(
        audited,
        key=lambda r: (float(r["joint"]), -int(r["modules"]), str(r["dewey"])),
    )

    total_modules = sum(int(r["modules"]) for r in audited)
    weighted_doi = sum(int(r["modules"]) * float(r["doi"]) for r in audited) / total_modules
    weighted_qid = sum(int(r["modules"]) * float(r["qid"]) for r in audited) / total_modules
    weighted_joint = sum(int(r["modules"]) * float(r["joint"]) for r in audited) / total_modules

    lines: list[str] = []
    lines += [
        "# DASHI knowledge coverage audit",
        "",
        "This report separates **subject volume**, **DOI/source addressability**, "
        "**Wikidata QID/entity addressability**, and **joint DOI+QID coverage**.",
        "",
        "> Boundary: Dewey coverage is classification coverage. A DOI is bibliographic "
        "identity, not theorem authority. A QID is external entity identity metadata, "
        "not source truth. Missing metadata is not negative knowledge.",
        "",
        f"Policy bands in this generated report: `sparse < {t.developing:.0%}`, "
        f"`developing >= {t.developing:.0%}`, `strong >= {t.strong:.0%}`.",
        "These thresholds are reporting policy and may be changed without changing theorem status.",
        "",
        "## Repository-weighted metadata density",
        "",
        f"- DOI module density: **{weighted_doi:.1%}**",
        f"- QID module density: **{weighted_qid:.1%}**",
        f"- joint DOI+QID module density: **{weighted_joint:.1%}**",
        "",
        "## Largest subject clusters",
        "",
        "| Dewey | Cluster | Modules | DOI | QID | Joint |",
        "|---|---|---:|---:|---:|---:|",
    ]
    for r in by_volume[:20]:
        lines.append(
            f"| `{r['dewey']}` | {r['label']} | {r['modules']:,} | "
            f"{r['doi']:.1%} ({r['doi_band']}) | "
            f"{r['qid']:.1%} ({r['qid_band']}) | "
            f"{r['joint']:.1%} ({r['joint_band']}) |"
        )

    lines += [
        "",
        "## Strongest joint-addressability clusters",
        "",
        "Ranked by joint DOI+QID module density, with module count as a secondary key.",
        "",
        "| Dewey | Cluster | Modules | Joint | Distinct QIDs |",
        "|---|---|---:|---:|---:|",
    ]
    for r in by_joint[:15]:
        lines.append(
            f"| `{r['dewey']}` | {r['label']} | {r['modules']:,} | "
            f"{r['joint']:.1%} | {r['distinct_qids']:,} |"
        )

    lines += [
        "",
        "## Highest-priority metadata gaps",
        "",
        "Low joint coverage is ranked with larger clusters first, so the table favors "
        "high-impact enrichment rather than tiny perfectly sparse clusters.",
        "",
        "| Dewey | Cluster | Modules | DOI | QID | Joint |",
        "|---|---|---:|---:|---:|---:|",
    ]
    for r in weak_joint[:20]:
        lines.append(
            f"| `{r['dewey']}` | {r['label']} | {r['modules']:,} | "
            f"{r['doi']:.1%} | {r['qid']:.1%} | {r['joint']:.1%} |"
        )

    lines += [
        "",
        "## Interpretation rule",
        "",
        "A cluster can be **strong by formal volume but weak by graph addressability**, "
        "or small by volume but strong by source/entity metadata. These dimensions must not be averaged into theorem status.",
        "",
        "Wikipedia first-link reachability is intentionally excluded from this ranking. "
        "It is a navigation/topology metric indexed by language, revision and parser/link-selection policy, "
        "not a measure of theorem/source coverage.",
        "",
    ]

    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text("\n".join(lines), encoding="utf-8")
    print(f"wrote {args.output}")
    print(f"clusters={len(audited)} modules={total_modules}")
    print(f"doi_density={weighted_doi:.6f}")
    print(f"qid_density={weighted_qid:.6f}")
    print(f"joint_density={weighted_joint:.6f}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
