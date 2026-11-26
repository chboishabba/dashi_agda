#!/usr/bin/env python3
"""Bounded, streaming presence-based similarity analysis for round packages.

The input is intentionally treated as evidence, not as a proof of theorem
equivalence.  Packages are selected by their non-empty body hash and all
declarations in a selected package contribute to its presence sets.
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
from collections import Counter, defaultdict
from pathlib import Path
from typing import Any, Iterable, Iterator


EMPTY_HASH = ""
ROUND_TOKEN = "<ROUND>"
ROUND_PATTERN = re.compile(r"(?:literalRound|Round)\d+")


def normalize_round_name(value: str) -> str:
    """Normalize both ``Round123`` and ``literalRound123`` deterministically."""

    return ROUND_PATTERN.sub(ROUND_TOKEN, value)


def _nonempty(values: Iterable[Any]) -> Iterator[str]:
    for value in values or ():
        if isinstance(value, str) and value:
            yield value


def _iter_jsonl(path: Path) -> Iterator[dict[str, Any]]:
    with path.open(encoding="utf-8") as stream:
        for line_number, line in enumerate(stream, 1):
            if not line.strip():
                continue
            try:
                row = json.loads(line)
            except json.JSONDecodeError as exc:
                raise ValueError(f"invalid JSON at {path}:{line_number}") from exc
            if not isinstance(row, dict):
                raise ValueError(f"expected an object at {path}:{line_number}")
            yield row


def _load_config(path: Path) -> dict[str, Any]:
    with path.open(encoding="utf-8") as stream:
        return json.load(stream)


def _group_specs(config: dict[str, Any], ranks: list[int] | None) -> list[dict[str, Any]]:
    rows = config["first_pass_results"]["ym_body_hash_groups"]
    wanted = set(ranks) if ranks else {row["rank"] for row in rows}
    selected = [row for row in rows if row["rank"] in wanted]
    if len(selected) != len(wanted):
        missing = sorted(wanted - {row["rank"] for row in selected})
        raise ValueError(f"unknown YM group rank(s): {missing}")
    return sorted(selected, key=lambda row: row["rank"])


def _new_presence() -> dict[str, set[str]]:
    return {
        "exact_declaration_names": set(),
        "normalized_declaration_names": set(),
        "signature_hashes": set(),
        "body_hashes": set(),
        "modules": set(),
        "dependency_neighbors": set(),
        "canonical_owners": set(),
        "archive_statuses": set(),
        "dispositions": set(),
        "residual_markers": set(),
    }


def _sorted_counter(counter: Counter[str]) -> dict[str, int]:
    return {key: counter[key] for key in sorted(counter)}


def _set_map(values: set[str]) -> list[str]:
    return sorted(values)


def _module_path(repo_root: Path, module: str) -> Path | None:
    if not module:
        return None
    path = repo_root / (module.replace(".", "/") + ".agda")
    return path if path.is_file() else None


def _git_file_exists(repo_root: Path, ref: str, path: Path) -> bool:
    relative = path.relative_to(repo_root).as_posix()
    result = subprocess.run(
        ["git", "cat-file", "-e", f"{ref}:{relative}"],
        cwd=repo_root,
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
    )
    return result.returncode == 0


def _validation_refl(path: Path, name: str) -> bool:
    if not path or "Validation" not in path.name:
        return False
    text = path.read_text(encoding="utf-8")
    return bool(re.search(rf"^\s*{re.escape(name)}\s*=\s*refl\s*$", text, re.MULTILINE))


IMPORT_PATTERN = re.compile(r"^[ \t]*(?:open[ \t]+)?import[ \t]+([A-Za-z0-9_.]+)(?:[ \t]+as[ \t]+([A-Za-z0-9_]+))?", re.MULTILINE)
PROOF_DECL_PATTERN = re.compile(r"^[ \t]*([A-Za-z0-9_']+)[ \t]*:[ \t]*ProofLevel[ \t]*$", re.MULTILINE)
PROOF_ASSIGN_PATTERN = re.compile(
    r"^[ \t]*([A-Za-z0-9_']+)[ \t]*=[ \t]*(conditional|standardImported|machineChecked|computed|conjectural)[ \t]*$",
    re.MULTILINE,
)


def _proof_leaf_closure(repo_root: Path, start: Path, cache: dict[Path, list[dict[str, str]]] | None = None) -> list[dict[str, str]]:
    """Find explicit conditional/imported proof-level leaves in an import closure."""

    if cache is not None and start in cache:
        return cache[start]
    queue = [(start, 0)]
    visited: set[Path] = set()
    leaves: list[dict[str, str]] = []
    max_depth = 3
    max_files = 300
    while queue and len(visited) < max_files:
        path, depth = queue.pop()
        if path in visited or not path.is_file():
            continue
        visited.add(path)
        text = path.read_text(encoding="utf-8")
        declared = {match.group(1) for match in PROOF_DECL_PATTERN.finditer(text)}
        assignments = {match.group(1): match.group(2) for match in PROOF_ASSIGN_PATTERN.finditer(text)}
        for name, level in sorted(assignments.items()):
            if name in declared and level in {"conditional", "standardImported"}:
                leaves.append({"level": level, "module": path.relative_to(repo_root).with_suffix("").as_posix().replace("/", "."), "name": name})
        if depth >= max_depth:
            continue
        for module, _alias in IMPORT_PATTERN.findall(text):
            imported = _module_path(repo_root, module)
            if imported:
                queue.append((imported, depth + 1))
    result = sorted(leaves, key=lambda item: (item["level"], item["module"], item["name"]))
    if cache is not None:
        cache[start] = result
    return result


def _audit_residuals(
    report_groups: list[dict[str, Any]],
    repo_root: Path,
    master_ref: str,
    comparison_refs: list[str] | None = None,
) -> dict[str, Any]:
    audited: list[dict[str, Any]] = []
    closure_cache: dict[Path, list[dict[str, str]]] = {}
    refs = comparison_refs or [master_ref]
    for group in report_groups:
        for residual in group.get("residuals", []):
            file_value = residual.get("file")
            source_file = repo_root / file_value if file_value else None
            source_exists = bool(source_file and source_file.is_file())
            master_exists = bool(source_file and source_file.is_file() and _git_file_exists(repo_root, master_ref, source_file))
            ref_presence = {
                ref: bool(source_file and source_file.is_file() and _git_file_exists(repo_root, ref, source_file))
                for ref in refs
            }
            audited.append(
                {
                    "group": group["rank"],
                    "family": residual.get("family"),
                    "name": residual.get("name"),
                    "file": file_value,
                    "source_present": source_exists,
                    "master_present": master_exists,
                    "ref_presence": ref_presence,
                    "validation_refl": bool(source_file and _validation_refl(source_file, residual.get("name", ""))),
                    "classification": "existing-validation-marker" if source_exists and master_exists else "missing-source",
                    "proof_level_leaves": _proof_leaf_closure(repo_root, source_file, closure_cache)
                    if source_file and source_file.is_file() and "CriticalPath" in source_file.name and "Validation" in source_file.name
                    else [],
                }
            )
    return {
        "master_ref": master_ref,
        "comparison_refs": refs,
        "residual_count": len(audited),
        "existing_validation_marker_count": sum(item["classification"] == "existing-validation-marker" for item in audited),
        "missing_source_count": sum(item["classification"] == "missing-source" for item in audited),
        "interpretation": "formal residual markers are present; any listed conditional/imported leaves are source-input obligations, not missing formal constructors",
        "residuals": audited,
    }


def analyze(
    source: Path,
    config_path: Path,
    ranks: list[int] | None = None,
) -> dict[str, Any]:
    """Build a deterministic report using one streaming pass over *source*."""

    config = _load_config(config_path)
    specs = _group_specs(config, ranks)
    by_hash = {spec["body_sha256"]: spec for spec in specs}
    accumulators: dict[str, dict[str, Any]] = {}
    for spec in specs:
        accumulators[spec["body_sha256"]] = {
            "spec": spec,
            "presence": _new_presence(),
            "package_ids": set(),
            "modules": set(),
            "declarations": [],
            "signature_occurrences": defaultdict(list),
            "canonical_owner_count": 0,
            "archive_status": Counter(),
            "disposition": Counter(),
            "residual_count": 0,
            "status_only_count": 0,
            "residuals": [],
        }

    for package in _iter_jsonl(source):
        package_hashes = set(_nonempty(package.get("body_hashes", [])))
        matched = package_hashes.intersection(by_hash)
        if not matched:
            continue
        # A package may list more than one body hash. It belongs to each
        # selected group, preserving the source package's own grouping.
        for body_hash in sorted(matched):
            acc = accumulators[body_hash]
            presence = acc["presence"]
            acc["package_ids"].add(str(package.get("package_id", "")))
            status = package.get("archive_status")
            disposition = package.get("disposition")
            if isinstance(status, str) and status:
                presence["archive_statuses"].add(status)
                acc["archive_status"][status] += 1
            if isinstance(disposition, str) and disposition:
                presence["dispositions"].add(disposition)
                acc["disposition"][disposition] += 1
            owner = package.get("selected_canonical_owner")
            if isinstance(owner, str) and owner:
                presence["canonical_owners"].add(owner)
                acc["canonical_owner_count"] += 1
            residuals = list(_nonempty(package.get("unresolved_residuals", [])))
            status_only = list(_nonempty(package.get("status_only_evidence", [])))
            presence["residual_markers"].update(residuals)
            presence["residual_markers"].update(status_only)
            acc["residual_count"] += len(residuals)
            acc["status_only_count"] += len(status_only)
            for neighbor in _nonempty(package.get("dependency_neighbors", [])):
                presence["dependency_neighbors"].add(neighbor)
            for module in _nonempty(package.get("round_modules", [])):
                presence["modules"].add(module)
                acc["modules"].add(module)
            for declaration in package.get("declarations", []):
                if not isinstance(declaration, dict):
                    continue
                name = declaration.get("name")
                if isinstance(name, str) and name:
                    presence["exact_declaration_names"].add(name)
                    presence["normalized_declaration_names"].add(normalize_round_name(name))
                for key in ("signature_sha256", "body_sha256"):
                    value = declaration.get(key)
                    if isinstance(value, str) and value:
                        presence["signature_hashes" if key.startswith("signature") else "body_hashes"].add(value)
                module = declaration.get("module")
                if isinstance(module, str) and module:
                    presence["modules"].add(module)
                    acc["modules"].add(module)
                acc["declarations"].append(
                    {
                        "name": name,
                        "module": module,
                        "source_location": next(
                            (location for location in package.get("source_locations", [])
                             if isinstance(location, str) and (not name or location.endswith(f"::{name}"))),
                            None,
                        ),
                    }
                )
                signature = declaration.get("signature_sha256")
                if isinstance(signature, str) and signature:
                    acc["signature_occurrences"][signature].append(
                        {
                            "name": name,
                            "module": module,
                            "source_location": acc["declarations"][-1]["source_location"],
                        }
                    )
            declarations_by_name = {
                declaration.get("name"): declaration
                for declaration in package.get("declarations", [])
                if isinstance(declaration, dict)
            }
            for residual in residuals:
                declaration = declarations_by_name.get(residual, {})
                acc["residuals"].append(
                    {
                        "name": residual,
                        "family": package.get("family"),
                        "file": declaration.get("file") or next(
                            (location.split("::", 1)[0] for location in package.get("source_locations", [])
                             if isinstance(location, str) and location.endswith(f"::{residual}")),
                            None,
                        ),
                    }
                )

    groups: list[dict[str, Any]] = []
    for spec in specs:
        acc = accumulators[spec["body_sha256"]]
        presence = acc["presence"]
        declarations = sorted(
            acc["declarations"],
            key=lambda item: (item.get("module") or "", item.get("name") or "", item.get("source_location") or ""),
        )
        representatives = declarations[:10]
        groups.append(
            {
                "rank": spec["rank"],
                "body_hash": spec["body_sha256"],
                "package_count": len(acc["package_ids"]),
                "module_count": len(acc["modules"]),
                "declaration_count": len(declarations),
                "presence": {key: _set_map(value) for key, value in sorted(presence.items())},
                "canonical_owner_coverage": {
                    "package_count_with_owner": acc["canonical_owner_count"],
                    "owner_count": len(presence["canonical_owners"]),
                    "owners": _set_map(presence["canonical_owners"]),
                },
                "status_counts": {
                    "archive_status": _sorted_counter(acc["archive_status"]),
                    "disposition": _sorted_counter(acc["disposition"]),
                    "unresolved_residual_entries": acc["residual_count"],
                    "status_only_evidence_entries": acc["status_only_count"],
                },
                "representative_source_locations": sorted(
                    {item["source_location"] for item in declarations if item["source_location"]}
                )[:10],
                "representative_declarations": representatives,
                "residuals": sorted(acc["residuals"], key=lambda item: (item.get("file") or "", item["name"])),
                "signature_occurrences": {
                    signature: sorted(
                        occurrences,
                        key=lambda item: (item.get("module") or "", item.get("name") or ""),
                    )
                    for signature, occurrences in sorted(acc["signature_occurrences"].items())
                },
            }
        )

    pairwise: list[dict[str, Any]] = []
    for left_index, left in enumerate(groups):
        for right in groups[left_index + 1 :]:
            lp, rp = left["presence"], right["presence"]
            def shared(key: str) -> list[str]:
                return sorted(set(lp[key]).intersection(rp[key]))

            def only(key: str, source_presence: dict[str, list[str]], other_presence: dict[str, list[str]]) -> list[str]:
                return sorted(set(source_presence[key]).difference(other_presence[key]))

            shared_symbols = shared("normalized_declaration_names")
            pairwise.append(
                {
                    "group_a": left["rank"],
                    "group_b": right["rank"],
                    "shared_normalized_symbols": shared_symbols,
                    "shared_signatures": shared("signature_hashes"),
                    "shared_modules": shared("modules"),
                    "group_a_only_normalized_symbols": only("normalized_declaration_names", lp, rp),
                    "group_b_only_normalized_symbols": only("normalized_declaration_names", rp, lp),
                    "jaccard": {
                        "normalized_symbols": _jaccard(lp["normalized_declaration_names"], rp["normalized_declaration_names"]),
                        "signatures": _jaccard(lp["signature_hashes"], rp["signature_hashes"]),
                        "modules": _jaccard(lp["modules"], rp["modules"]),
                    },
                }
            )

    result = {
        "schema_version": 1,
        "analyzer": "scripts/round_similarity_bidi.py",
        "source": str(source),
        "config": str(config_path),
        "family": "ym",
        "empty_hashes_excluded": True,
        "groups": groups,
        "pairwise": pairwise,
    }
    return result


def render_review_markdown(report: dict[str, Any]) -> str:
    """Render a bounded human-review surface from an analyzer report."""

    groups = {group["rank"]: group for group in report["groups"]}
    lines = [
        "# YM Round Similarity Review Digest",
        "",
        "Generated from the bounded presence report. Similarity is discovery evidence, not proof of theorem equivalence.",
        "",
        "## Selected groups",
        "",
        "| Group | Body hash | Packages | Declarations | Statuses |",
        "| ---: | --- | ---: | ---: | --- |",
    ]
    for group in report["groups"]:
        statuses = ", ".join(
            f"{key}={value}" for key, value in group["status_counts"]["archive_status"].items()
        )
        lines.append(
            f"| {group['rank']} | `{group['body_hash']}` | {group['package_count']} | "
            f"{group['declaration_count']} | {statuses} |"
        )

    audit = report.get("residual_audit")
    if audit:
        lines.extend(
            [
                "",
                "## Residual-marker audit",
                "",
                f"- Residual markers inspected: **{audit['residual_count']}**.",
                f"- Existing in source and `{audit['master_ref']}`: **{audit['existing_validation_marker_count']}**.",
                f"- Missing source declarations: **{audit['missing_source_count']}**.",
                "",
                "These counts distinguish stale/package residual markers from genuinely absent source. `refl` validation wrappers are routing evidence, not proof of the underlying conditional source payload. Presence in a PR/master ref is not promotion.",
            ]
        )
        leaves = {
            (leaf["level"], leaf["module"], leaf["name"])
            for item in audit["residuals"]
            for leaf in item.get("proof_level_leaves", [])
            if item.get("family", "").endswith("YangMillsClayCriticalPath")
        }
        if leaves:
            lines.extend(["", "### Conditional/imported leaves seen in critical-path closures", ""])
            for level, module, name in sorted(leaves)[:30]:
                lines.append(f"- `{level}` `{module}::{name}`")
            if len(leaves) > 30:
                lines.append(f"- … and {len(leaves) - 30} more (see JSON report).")

    for pair in report["pairwise"]:
        left, right = groups[pair["group_a"]], groups[pair["group_b"]]
        lines.extend(
            [
                "",
                f"## Groups {pair['group_a']} and {pair['group_b']}",
                "",
                f"- Shared normalized declaration names: **{len(pair['shared_normalized_symbols'])}**.",
                f"- Shared signature hashes: **{len(pair['shared_signatures'])}**.",
                f"- Shared modules: **{len(pair['shared_modules'])}**.",
                f"- Group {pair['group_a']}-only normalized names: **{len(pair['group_a_only_normalized_symbols'])}**.",
                f"- Group {pair['group_b']}-only normalized names: **{len(pair['group_b_only_normalized_symbols'])}**.",
            ]
        )
        if pair["shared_signatures"]:
            lines.extend(["", "### Shared signature occurrences", ""])
            for signature in pair["shared_signatures"]:
                lines.append(f"- `{signature}`")
                for group in (left, right):
                    occurrences = group["signature_occurrences"].get(signature, [])
                    sample_limit = 12
                    lines.append(
                        f"  - Group {group['rank']} ({len(occurrences)} occurrences; showing up to {sample_limit}):"
                    )
                    for occurrence in occurrences[:sample_limit]:
                        location = occurrence.get("source_location") or "(location unavailable)"
                        lines.append(f"    - `{location}`")
                    if len(occurrences) > sample_limit:
                        lines.append(f"    - … and {len(occurrences) - sample_limit} more (see JSON report).")
        lines.extend(["", "### Shared modules", ""])
        lines.extend(f"- `{module}`" for module in pair["shared_modules"][:25])
        if not pair["shared_modules"]:
            lines.append("- None")

    group_three = groups.get(3)
    if group_three:
        residuals = group_three["presence"]["residual_markers"]
        lines.extend(
            [
                "",
                "## Group 3 unresolved review queue",
                "",
                f"Unresolved residual entries: **{group_three['status_counts']['unresolved_residual_entries']}**.",
                "",
            ]
        )
        lines.extend(f"- `{residual}`" for residual in residuals[:50])
        if len(residuals) > 50:
            lines.append(f"- … and {len(residuals) - 50} more (see JSON report).")
    return "\n".join(lines) + "\n"


def _jaccard(left: Iterable[str], right: Iterable[str]) -> float:
    a, b = set(left), set(right)
    union = a | b
    return 0.0 if not union else len(a & b) / len(union)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", type=Path, default=Path(".dashi/round-stranded/ym-packages.jsonl"))
    parser.add_argument("--config", type=Path, default=Path("config/round-similarity-tranches.json"))
    parser.add_argument("--output", type=Path, default=Path(".dashi/round-stranded/ym-similarity-bidi.json"))
    parser.add_argument("--review-output", type=Path, default=Path(".dashi/round-stranded/ym-similarity-review.md"))
    parser.add_argument("--groups", type=int, nargs="+", metavar="RANK", help="selected YM group ranks")
    parser.add_argument("--repo-root", type=Path, default=Path("."), help="repository root for residual source auditing")
    parser.add_argument("--master-ref", default="master", help="git ref used for source-presence auditing")
    parser.add_argument(
        "--comparison-refs",
        nargs="+",
        default=["master", "origin/pr/1444", "origin/pr/1536", "origin/pr/1544"],
        help="git refs checked for residual source presence",
    )
    args = parser.parse_args()
    report = analyze(args.source, args.config, args.groups)
    report["residual_audit"] = _audit_residuals(
        report["groups"], args.repo_root.resolve(), args.master_ref, args.comparison_refs
    )
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    args.review_output.parent.mkdir(parents=True, exist_ok=True)
    args.review_output.write_text(render_review_markdown(report), encoding="utf-8")
    print(f"wrote {args.output} and {args.review_output} ({len(report['groups'])} groups, {len(report['pairwise'])} pairwise comparisons)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
