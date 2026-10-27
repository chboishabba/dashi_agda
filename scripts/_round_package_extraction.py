from __future__ import annotations

import json
import re
from collections import defaultdict
from pathlib import Path

from _stranded_common import (
    decls_for_modules,
    family_of,
    is_round,
    load_import_graph,
    module_paths,
    stable_id,
)


BASE_ARCHIVE_STATUS = {
    "SUPERSEDED_EXACT": "SUPERSEDED",
    "SUPERSEDED_RENAMED": "SUPERSEDED",
    "CANONICAL_COMPILER_EXISTS": "EXTRACTED",
    "ALTERNATE_PROOF": "HISTORICAL-ONLY",
    "NEGATIVE_RESULT": "NEGATIVE-RESULT",
    "STATUS_ONLY": "HISTORICAL-ONLY",
    "GENUINE_OPEN_OBLIGATION": "EXTRACTED",
    "UNRESOLVED": "UNRESOLVED",
    "CANONICAL_ENDPOINT": "SUPERSEDED",
    "PROVENANCE_ONLY": "HISTORICAL-ONLY",
}


def load_targets(path: Path, *, require_seed_families: bool = False) -> dict:
    cfg = json.loads(path.read_text(encoding="utf-8"))
    required = {
        "schema_version",
        "candidate_positive_names",
        "status_count_names",
        "outputs",
    }
    if require_seed_families:
        required.add("seed_families")
    if "target_prefixes" not in cfg and "target_prefix" not in cfg:
        raise SystemExit("missing extraction config key: target_prefixes or target_prefix")
    missing = required - set(cfg)
    if missing:
        raise SystemExit(f"missing extraction config keys: {sorted(missing)}")
    return cfg


def target_prefixes(cfg: dict) -> tuple[str, ...]:
    if "target_prefixes" in cfg:
        return tuple(cfg["target_prefixes"])
    return (cfg["target_prefix"],)


def discover_round_modules(paths: dict[str, str], prefixes: tuple[str, ...]) -> set[str]:
    return {
        module
        for module in paths
        if any(module.startswith(prefix) for prefix in prefixes) and is_round(module)
    }


def build_round_graph(imports, modules):
    modules = set(modules)
    parents = defaultdict(set)
    children = defaultdict(set)
    for child in sorted(modules):
        for parent in imports.get(child, ()):
            if parent in modules and is_round(parent):
                parents[child].add(parent)
                children[parent].add(child)
    return parents, children


def _ancestors(start: str, parents) -> set[str]:
    seen: set[str] = set()
    stack = [start]
    while stack:
        module = stack.pop()
        if module in seen:
            continue
        seen.add(module)
        stack.extend(sorted(parents.get(module, ())))
    return seen


def _as_dict(row) -> dict:
    if isinstance(row, dict):
        return row
    return {k: row[k] for k in row.keys()}


def _decl_dict(row) -> dict:
    row = _as_dict(row)
    return {
        "symbol_id": row["symbol_id"],
        "module": row["module"],
        "file": row["file"],
        "name": row["name"],
        "kind": row["kind"],
        "normalized_signature": row["normalized_signature"],
        "signature_sha256": row["signature_sha256"],
        "body_sha256": row["body_sha256"],
    }


def _status_name_evidence(name: str, cfg: dict) -> list[str]:
    evidence: list[str] = []
    if name in set(cfg.get("status_count_names", ())):
        evidence.append(name)
    for pattern in cfg.get("status_name_patterns", ()):
        if re.search(pattern, name):
            evidence.append(pattern)
    return evidence


def cluster_packages(conn, cfg: dict) -> list[dict]:
    paths = module_paths(conn)
    imports, _ = load_import_graph(conn)
    prefixes = target_prefixes(cfg)
    discovered = discover_round_modules(paths, prefixes)
    seeds = set(cfg.get("seed_families", ()))
    if seeds:
        round_modules = {m for m in discovered if family_of(m) in seeds}
        families = seeds
    else:
        round_modules = discovered
        families = {family_of(m) for m in round_modules}

    parents, children = build_round_graph(imports, round_modules)
    negative_terms = tuple(x.lower() for x in cfg.get("negative_name_terms", ()))
    namespace = cfg.get("package_namespace", "ym-round-package")

    packages: list[dict] = []
    for family in sorted(families):
        family_modules = {m for m in round_modules if family_of(m) == family}
        if not family_modules:
            continue
        terminal_leaves = sorted(
            m for m in family_modules if not (children.get(m, set()) & family_modules)
        )
        ancestry_by_leaf = {
            leaf: _ancestors(leaf, parents) & family_modules for leaf in terminal_leaves
        }
        all_ancestry = set().union(*ancestry_by_leaf.values()) if ancestry_by_leaf else set()
        decls = [_decl_dict(r) for r in decls_for_modules(conn, all_ancestry)]
        by_name: dict[str, list[dict]] = defaultdict(list)
        for decl in decls:
            by_name[decl["name"]].append(decl)

        for name in sorted(by_name):
            occurrences = sorted(by_name[name], key=lambda d: (d["module"], d["symbol_id"]))
            occurrence_modules = {d["module"] for d in occurrences}
            leaves = sorted(
                leaf for leaf, ancestry in ancestry_by_leaf.items()
                if ancestry & occurrence_modules
            )
            signatures = sorted({d["signature_sha256"] for d in occurrences})
            bodies = sorted({d["body_sha256"] for d in occurrences})
            neighbors = sorted({
                imported
                for module in occurrence_modules
                for imported in imports.get(module, ())
                if imported in family_modules
            })
            lower = name.lower()
            package_id = stable_id(namespace, family, name, ",".join(signatures))
            domain = next((p for p in prefixes if family.startswith(p)), prefixes[0])
            packages.append({
                "package_id": package_id,
                "domain": domain,
                "family": family,
                "terminal_leaves": leaves,
                "round_modules": sorted(occurrence_modules),
                "ancestor_round_count": len(all_ancestry),
                "declarations": occurrences,
                "candidate_names": [name],
                "signature_hashes": signatures,
                "body_hashes": bodies,
                "historical_mutation_count": max(0, len(bodies) - 1),
                "dependency_neighbors": neighbors,
                "status_only_evidence": _status_name_evidence(name, cfg),
                "negative_result_evidence": [
                    term for term in negative_terms if term and term in lower
                ],
                "source_locations": sorted(
                    {f"{d['file']}::{d['name']}" for d in occurrences}
                ),
            })

    return sorted(packages, key=lambda p: (p["family"], p["package_id"]))


def build_nonround_indexes(conn, cfg: dict | None = None) -> dict:
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


def matches_for_package(package: dict, indexes: dict) -> tuple[list[dict], list[dict]]:
    exact_matches: list[dict] = []
    sig_matches: list[dict] = []
    seen_exact: set[str] = set()
    seen_sig: set[str] = set()
    for d in package["declarations"]:
        for m in indexes["exact"].get((d["signature_sha256"], d["body_sha256"]), []):
            if m["symbol_id"] not in seen_exact:
                exact_matches.append(m)
                seen_exact.add(m["symbol_id"])
        for m in indexes["sig"].get(d["signature_sha256"], []):
            if m["symbol_id"] not in seen_sig:
                sig_matches.append(m)
                seen_sig.add(m["symbol_id"])
    return exact_matches, sig_matches


def public_match(d: dict) -> dict:
    return {
        "symbol_id": d.get("symbol_id"),
        "module": d.get("module"),
        "name": d.get("name"),
        "signature_sha256": d.get("signature_sha256"),
        "body_sha256": d.get("body_sha256"),
    }


def bounded_matches(matches: list[dict], limit: int) -> tuple[int, list[dict], bool]:
    ordered = sorted(matches, key=lambda x: (x.get("module") or "", x.get("name") or "", x.get("symbol_id") or ""))
    count = len(ordered)
    sample = ordered[:limit]
    return count, sample, count > len(sample)


def classify_package(package: dict, nonround_indexes: dict, cfg: dict) -> dict:
    result = dict(package)
    names = set(package.get("candidate_names", ()))
    status_names = set(cfg.get("status_count_names", ()))
    status_patterns = tuple(cfg.get("status_name_patterns", ()))
    negative_terms = tuple(x.lower() for x in cfg.get("negative_name_terms", ()))
    positive_names = set(cfg.get("candidate_positive_names", ()))
    evidence: list[str] = []
    retained_negative: list[str] = []
    unresolved: list[str] = []
    matches: list[dict] = []
    owner = None

    pattern_status = any(
        re.search(pattern, name) for name in names for pattern in status_patterns
    )
    if names & status_names or package.get("status_only_evidence") or pattern_status:
        disposition = "STATUS_ONLY"
        evidence.append("configured status/count/regression declaration; never theorem authority")
    elif package.get("negative_result_evidence") or any(
        term in name.lower() for name in names for term in negative_terms
    ):
        disposition = "NEGATIVE_RESULT"
        retained_negative = sorted(names)
        evidence.append("explicit negative/no-go/firewall naming evidence preserved")
    else:
        exact_matches, sig_matches = matches_for_package(package, nonround_indexes)
        if exact_matches:
            disposition = "SUPERSEDED_EXACT"
            matches = [public_match(x) for x in exact_matches]
            evidence.append("identical normalized signature and proof-body fingerprint")
        elif sig_matches:
            same_name = [x for x in sig_matches if x["name"] in names]
            matches = [public_match(x) for x in sig_matches]
            if same_name:
                disposition = "ALTERNATE_PROOF"
                evidence.append("identical normalized signature with a distinct proof body")
            else:
                disposition = "SUPERSEDED_RENAMED"
                evidence.append("identical normalized signature under a different current non-Round declaration name")
        else:
            compiler_hits: list[dict] = []
            for name in names:
                for hint in cfg.get("compiler_hints", {}).get(name, ()):
                    compiler_hits.extend(nonround_indexes["name"].get(hint, ()))
            if compiler_hits:
                disposition = "CANONICAL_COMPILER_EXISTS"
                matches = [public_match(x) for x in compiler_hits]
                unresolved = sorted(names)
                evidence.append("current non-Round compiler exists; selected same-object/source premise remains an explicit residual")
            elif names & set(cfg.get("canonical_endpoint_names", ())):
                disposition = "CANONICAL_ENDPOINT"
                unresolved = []
                evidence.append("configured canonical endpoint marker with explicit current endpoint evidence")
            elif names & set(cfg.get("provenance_only_names", ())):
                disposition = "PROVENANCE_ONLY"
                evidence.append("configured provenance-only package; mathematical coordinates are owned elsewhere")
            elif names & positive_names:
                disposition = "GENUINE_OPEN_OBLIGATION"
                unresolved = sorted(names)
                evidence.append("configured theorem-bearing candidate has no exact/signature/compiler match in the non-Round universe")
            else:
                disposition = "UNRESOLVED"
                unresolved = sorted(names)
                evidence.append("insufficient semantic evidence; classification fails closed")

    if disposition in {"GENUINE_OPEN_OBLIGATION", "CANONICAL_COMPILER_EXISTS"}:
        for name in sorted(names):
            owner = cfg.get("canonical_owner_by_name", {}).get(name) or owner
        owner = cfg.get("canonical_owner_by_family", {}).get(package.get("family"), owner)

    limit = int(cfg.get("nonround_match_sample_limit", 10))
    count, sample, truncated = bounded_matches(matches, limit)
    result.update({
        "disposition": disposition,
        "evidence": evidence,
        "nonround_match_count": count,
        "nonround_matches": sample,
        "nonround_matches_truncated": truncated,
        "retained_negative_results": retained_negative,
        "unresolved_residuals": unresolved,
        "selected_canonical_owner": owner,
        "archive_status": BASE_ARCHIVE_STATUS[disposition],
    })
    return result


def classify_packages(conn, cfg: dict, packages: list[dict]) -> list[dict]:
    indexes = build_nonround_indexes(conn, cfg)
    return sorted(
        [classify_package(p, indexes, cfg) for p in packages],
        key=lambda r: (r["family"], r["package_id"]),
    )


def write_jsonl(rows: list[dict], out: Path) -> None:
    out.parent.mkdir(parents=True, exist_ok=True)
    with out.open("w", encoding="utf-8") as f:
        for row in sorted(rows, key=lambda r: (r["family"], r["package_id"])):
            f.write(json.dumps(row, sort_keys=True) + "\n")


def write_receipts(rows: list[dict], out: Path) -> None:
    write_jsonl(rows, out)
