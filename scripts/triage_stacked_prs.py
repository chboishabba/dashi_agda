#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import re
import subprocess
from collections import Counter
from pathlib import Path

ROUND_RE = re.compile(r"Round[0-9]+")


def git(*args: str, check: bool = True) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        ["git", *args],
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=check,
    )


def exists_at(ref: str, path: str) -> bool:
    return git("cat-file", "-e", f"{ref}:{path}", check=False).returncode == 0


def blob_sha(ref: str, path: str) -> str | None:
    p = git("rev-parse", f"{ref}:{path}", check=False)
    if p.returncode != 0:
        return None
    return p.stdout.strip()


def diff_name_status(base: str, head: str) -> list[tuple[str, str]]:
    p = git("diff", "--name-status", base, head, "--")
    rows: list[tuple[str, str]] = []
    for line in p.stdout.splitlines():
        if not line.strip():
            continue
        parts = line.split("\t")
        status = parts[0]
        path = parts[-1]
        rows.append((status, path))
    return rows


def classify_path(base: str, head: str, status: str, path: str, role: str | None) -> dict:
    base_exists = exists_at(base, path)
    head_exists = exists_at(head, path)
    base_blob = blob_sha(base, path) if base_exists else None
    head_blob = blob_sha(head, path) if head_exists else None
    identical = bool(base_blob and head_blob and base_blob == head_blob)
    historical_round = bool(ROUND_RE.search(path))

    if historical_round:
        disposition = "HISTORICAL_ROUND"
    elif identical:
        disposition = "IDENTICAL_ON_BASE"
    elif not base_exists and head_exists:
        disposition = "ADDED_RELATIVE_TO_BASE"
    elif base_exists and head_exists:
        disposition = "DIFFERS_FROM_BASE"
    elif base_exists and not head_exists:
        disposition = "DELETED_ON_HEAD"
    else:
        disposition = "UNRESOLVED_PATH_STATE"

    if role == "integration_only" and disposition != "IDENTICAL_ON_BASE":
        semantic_priority = "integration_only"
    elif role == "dependency_scaffold" and disposition != "IDENTICAL_ON_BASE":
        semantic_priority = "dependency_scaffold"
    elif role in {"theorem_owner", "conditional_compiler", "authority_surface"}:
        semantic_priority = "high"
    elif role == "regression_surface":
        semantic_priority = "medium"
    elif historical_round:
        semantic_priority = "historical"
    else:
        semantic_priority = "normal"

    return {
        "status": status,
        "path": path,
        "role": role,
        "base_exists": base_exists,
        "head_exists": head_exists,
        "base_blob": base_blob,
        "head_blob": head_blob,
        "identical_blob": identical,
        "historical_round": historical_round,
        "disposition": disposition,
        "semantic_priority": semantic_priority,
    }


def main() -> None:
    ap = argparse.ArgumentParser(
        description=(
            "Triage stacked PR heads against the CURRENT base tree. "
            "This is intentionally a tree-delta sieve, not a semantic proof of novelty."
        )
    )
    ap.add_argument("--spec", default="config/stacked-pr-triage.json")
    ap.add_argument("--base", default=None, help="Override spec base, normally current master")
    ap.add_argument("--out", default=".dashi/round-stranded/stacked-pr-triage.json")
    args = ap.parse_args()

    spec = json.loads(Path(args.spec).read_text())
    base = args.base or spec.get("base", "master")

    # Fail early if the caller forgot to fetch the historical PR heads.
    missing_heads = []
    for pr in spec["pull_requests"]:
        if git("cat-file", "-e", f"{pr['head']}^{{commit}}", check=False).returncode != 0:
            missing_heads.append({"number": pr["number"], "head": pr["head"]})
    if missing_heads:
        raise SystemExit(
            "missing PR head commits locally; fetch them first: "
            + json.dumps(missing_heads, sort_keys=True)
        )

    reports = []
    for pr in spec["pull_requests"]:
        number = pr["number"]
        head = pr["head"]
        roles = {x["path"]: x["role"] for x in pr.get("seed_paths", [])}
        rows = diff_name_status(base, head)
        classified = [
            classify_path(base, head, status, path, roles.get(path))
            for status, path in rows
        ]

        # Ensure seed paths are represented even if the current base and head
        # are already blob-identical and therefore absent from git diff.
        present = {x["path"] for x in classified}
        for path, role in roles.items():
            if path not in present:
                classified.append(classify_path(base, head, "=", path, role))

        disposition_counts = Counter(x["disposition"] for x in classified)
        candidate_paths = [
            x for x in classified
            if x["disposition"] in {"ADDED_RELATIVE_TO_BASE", "DIFFERS_FROM_BASE"}
            and not x["historical_round"]
            and x["role"] != "integration_only"
        ]
        high_value = [
            x for x in candidate_paths
            if x["semantic_priority"] in {"high", "medium"}
        ]
        dependency_scaffold = [
            x for x in candidate_paths
            if x["semantic_priority"] == "dependency_scaffold"
        ]

        reports.append({
            "pr_number": number,
            "title": pr["title"],
            "base": base,
            "head": head,
            "notes": pr.get("notes", ""),
            "tree_delta_count": len(classified),
            "disposition_counts": dict(disposition_counts),
            "high_value_seed_candidates": high_value,
            "dependency_scaffold_candidates": dependency_scaffold,
            "all_nonround_candidates": candidate_paths,
            "files": sorted(classified, key=lambda x: (x["disposition"], x["path"])),
        })

    out = Path(args.out)
    out.parent.mkdir(parents=True, exist_ok=True)
    payload = {
        "schema_version": 1,
        "base": base,
        "warning": (
            "Tree difference is only a sieve. Run the candidate modules through "
            "the repository semantic index/fingerprint comparison before promotion."
        ),
        "pull_requests": reports,
    }
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")

    compact = {
        "base": base,
        "prs": [
            {
                "number": r["pr_number"],
                "counts": r["disposition_counts"],
                "high_value_seed_candidates": [x["path"] for x in r["high_value_seed_candidates"]],
                "dependency_scaffold_candidates": [x["path"] for x in r["dependency_scaffold_candidates"]],
                "all_nonround_candidate_count": len(r["all_nonround_candidates"]),
            }
            for r in reports
        ],
        "output": str(out),
    }
    print(json.dumps(compact, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
