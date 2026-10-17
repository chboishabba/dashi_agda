#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
from collections import defaultdict
from pathlib import Path

from _stranded_common import connect, decls_for_modules, is_round, module_paths
from cluster_ym_round_packages import cluster_packages, load_targets


ARCHIVE_STATUS = {
    "SUPERSEDED_EXACT": "SUPERSEDED",
    "SUPERSEDED_RENAMED": "SUPERSEDED",
    "CANONICAL_COMPILER_EXISTS": "EXTRACTED",
    "ALTERNATE_PROOF": "HISTORICAL-ONLY",
    "NEGATIVE_RESULT": "NEGATIVE-RESULT",
    "STATUS_ONLY": "HISTORICAL-ONLY",
    "GENUINE_OPEN_OBLIGATION": "EXTRACTED",
    "UNRESOLVED": "UNRESOLVED",
}


def _as_dict(row) -> dict:
    if isinstance(row, dict):
        return row
    return {k: row[k] for k in row.keys()}


def build_nonround_indexes(conn) -> dict:
    modules = {m for m in module_paths(conn) if not is_round(m)}
    decls = [_as_dict(r) for r in decls_for_modules(conn, modules)]
    exact = defaultdict(list)
    sig = defaultdict(list)
    name = defaultdict(list)
    body = defaultdict(list)
    for d in decls:
        exact[(d["signature_sha256"], d["body_sha256"])].append(d)
        sig[d["signature_sha256"]].append(d)
        name[d["name"]].append(d)
        body[d["body_sha256"]].append(d)
    return {"exact": exact, "sig": sig, "name": name, "body": body}


def _matches_for_package(package: dict, indexes: dict) -> tuple[list[dict], list[dict]]:
    exact_matches: list[dict] = []
    sig_matches: list[dict] = []
    seen_exact = set()
    seen_sig = set()
    for d in package["declarations"]:
        for m in indexes["exact"].get((d["signature_sha256"], d["body_sha256"]), []):
            key = m["symbol_id"]
            if key not in seen_exact:
                exact_matches.append(m)
                seen_exact.add(key)
        for m in indexes["sig"].get(d["signature_sha256"], []):
            key = m["symbol_id"]
            if key not in seen_sig:
                sig_matches.append(m)
                seen_sig.add(key)
    return exact_matches, sig_matches


def _public_match(d: dict) -> dict:
    return {
        "symbol_id": d.get("symbol_id"),
        "module": d.get("module"),
        "name": d.get("name"),
        "signature_sha256": d.get("signature_sha256"),
        "body_sha256": d.get("body_sha256"),
    }


def classify_package(package: dict, nonround_indexes: dict, cfg: dict) -> dict:
    result = dict(package)
    names = set(package.get("candidate_names", ()))
    status_names = set(cfg.get("status_count_names", ()))
    negative_terms = tuple(x.lower() for x in cfg.get("negative_name_terms", ()))
    positive_names = set(cfg.get("candidate_positive_names", ()))
    evidence: list[str] = []
    retained_negative: list[str] = []
    unresolved: list[str] = []
    matches: list[dict] = []
    owner = None

    if names & status_names or package.get("status_only_evidence"):
        disposition = "STATUS_ONLY"
        evidence.append("configured status/count declaration; never theorem authority")
    elif package.get("negative_result_evidence") or any(
        term in name.lower() for name in names for term in negative_terms
    ):
        disposition = "NEGATIVE_RESULT"
        retained_negative = sorted(names)
        evidence.append("explicit negative/no-go/firewall naming evidence preserved")
    else:
        exact_matches, sig_matches = _matches_for_package(package, nonround_indexes)
        if exact_matches:
            disposition = "SUPERSEDED_EXACT"
            matches = [_public_match(x) for x in exact_matches]
            evidence.append("identical normalized signature and proof-body fingerprint")
        elif sig_matches:
            same_name = [x for x in sig_matches if x["name"] in names]
            matches = [_public_match(x) for x in sig_matches]
            if same_name:
                disposition = "ALTERNATE_PROOF"
                evidence.append("identical normalized signature with a distinct proof body")
            else:
                disposition = "SUPERSEDED_RENAMED"
                evidence.append(
                    "identical normalized signature under a different current non-Round declaration name"
                )
        else:
            compiler_hits: list[dict] = []
            for name in names:
                for hint in cfg.get("compiler_hints", {}).get(name, ()): 
                    compiler_hits.extend(nonround_indexes["name"].get(hint, ()))
            if compiler_hits:
                disposition = "CANONICAL_COMPILER_EXISTS"
                matches = [_public_match(x) for x in compiler_hits]
                unresolved = sorted(names)
                evidence.append(
                    "current non-Round compiler exists; selected same-object/source premise remains an explicit residual"
                )
            elif names & positive_names:
                disposition = "GENUINE_OPEN_OBLIGATION"
                unresolved = sorted(names)
                evidence.append(
                    "configured theorem-bearing candidate has no exact/signature/compiler match in the non-Round universe"
                )
            else:
                disposition = "UNRESOLVED"
                unresolved = sorted(names)
                evidence.append("insufficient semantic evidence; classification fails closed")

    if disposition in {"GENUINE_OPEN_OBLIGATION", "CANONICAL_COMPILER_EXISTS"}:
        for name in sorted(names):
            owner = cfg.get("canonical_owner_by_name", {}).get(name) or owner
        owner = cfg.get("canonical_owner_by_family", {}).get(package.get("family"), owner)

    result.update(
        {
            "disposition": disposition,
            "evidence": evidence,
            "nonround_matches": sorted(
                matches, key=lambda x: (x.get("module") or "", x.get("name") or "")
            ),
            "retained_negative_results": retained_negative,
            "unresolved_residuals": unresolved,
            "selected_canonical_owner": owner,
            "archive_status": ARCHIVE_STATUS[disposition],
        }
    )
    return result


def classify_packages(conn, cfg: dict, packages: list[dict]) -> list[dict]:
    indexes = build_nonround_indexes(conn)
    return sorted(
        [classify_package(p, indexes, cfg) for p in packages],
        key=lambda r: (r["family"], r["package_id"]),
    )


def write_receipts(rows: list[dict], out: Path, max_matches: int = 10) -> None:
    out.parent.mkdir(parents=True, exist_ok=True)
    with out.open("w", encoding="utf-8") as f:
        for row in sorted(rows, key=lambda r: (r["family"], r["package_id"])):
            material = dict(row)
            material["archive_status"] = ARCHIVE_STATUS[material["disposition"]]
            if material["disposition"] == "STATUS_ONLY":
                material["selected_canonical_owner"] = None
            if len(material.get("nonround_matches", [])) > max_matches:
                material["nonround_matches"] = material["nonround_matches"][:max_matches]
            f.write(json.dumps(material, sort_keys=True) + "\n")


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--db", default=".dashi/repository.sqlite3")
    ap.add_argument("--config", default="config/ym-round-extraction-targets.json")
    ap.add_argument("--out")
    args = ap.parse_args()

    cfg = load_targets(Path(args.config))
    conn = connect(Path(args.db))
    packages = cluster_packages(conn, cfg)
    rows = classify_packages(conn, cfg, packages)
    out = Path(args.out or cfg["outputs"]["receipts"])
    write_receipts(rows, out)
    counts = defaultdict(int)
    for row in rows:
        counts[row["disposition"]] += 1
    print(
        json.dumps(
            {
                "package_count": len(rows),
                "dispositions": dict(sorted(counts.items())),
                "output": str(out),
            },
            indent=2,
            sort_keys=True,
        )
    )


if __name__ == "__main__":
    main()
