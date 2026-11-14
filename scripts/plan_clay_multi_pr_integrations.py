#!/usr/bin/env python3
"""Read-only, fail-closed multi-PR source convergence planner for DASHI.

The input manifest pins exact commit hashes and lane/owner metadata. A missing
pin, diverging same-path source, or inconsistent repository is a BLOCKER, not a
permission to guess or merge. Nothing here checks an Agda/Lean proof, an
analytic theorem, or external source provenance. Git tree objects may be
computed by merge-tree, but no refs/worktrees are changed.

Use in each LOCAL repository after fetching pinned PR heads. Example:
  python3 scripts/plan_clay_multi_pr_integrations.py \
    --repo /path/to/dashi_agda \
    --manifest Docs/roadmaps/ClayPortfolioPinnedIntegration20261114.json \
    --group agda --json
"""
from __future__ import annotations

import argparse
import json
import re
import subprocess
from collections import defaultdict
from pathlib import Path

SHA = re.compile(r"^[0-9a-f]{40}$")


def git(repo: Path, *args: str) -> subprocess.CompletedProcess[bytes]:
    return subprocess.run(["git", "-C", str(repo), *args],
                          stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                          check=False)


def commit_exists(repo: Path, sha: str) -> bool:
    return bool(SHA.fullmatch(sha)) and git(repo, "cat-file", "-e", f"{sha}^{{commit}}").returncode == 0


def ancestor(repo: Path, older: str, newer: str) -> bool:
    return git(repo, "merge-base", "--is-ancestor", older, newer).returncode == 0


def merge_base(repo: Path, a: str, b: str) -> str | None:
    r = git(repo, "merge-base", a, b)
    return r.stdout.decode().strip() if r.returncode == 0 else None


def changes(repo: Path, base: str, donor: str) -> list[str]:
    r = git(repo, "diff", "--name-only", "-z", base, donor)
    if r.returncode:
        raise RuntimeError(f"cannot diff {base[:12]}..{donor[:12]}: {r.stderr.decode()}")
    return sorted(set(r.stdout.decode("utf-8").strip("\0").split("\0"))) if r.stdout else []


def object_id(repo: Path, commit: str, path: str) -> str | None:
    # Path derived only from git's diff and never executed as a ref.
    if "\n" in path or "\x00" in path or not path:
        raise ValueError("invalid git path")
    r = git(repo, "rev-parse", "--verify", f"{commit}:{path}")
    return r.stdout.decode().strip() if r.returncode == 0 else None


def check_manifest(data: dict, group: str) -> list[dict]:
    entries = [p for p in data["pr_heads"] if p["repository_group"] == group]
    ids = set()
    for p in entries:
        key = (p["repository_group"], p["pr"])
        if key in ids:
            raise ValueError(f"duplicate PR owner: {key}")
        ids.add(key)
        if not SHA.fullmatch(p["sha"]):
            raise ValueError(f"unpinned/malformed SHA for {key}")
        if p["state"] not in ("open", "merged"):
            raise ValueError(f"unsupported PR state for {key}")
    return entries


def plan(repo: Path, data: dict, group: str, baseline: str | None = None,
         check_merge_tree: bool = False) -> dict:
    entries = check_manifest(data, group)
    base_ref = baseline or data["repositories"][group]["baseline_ref"]
    resolved = git(repo, "rev-parse", "--verify", f"{base_ref}^{{commit}}")
    if resolved.returncode:
        raise RuntimeError(f"missing baseline {base_ref}")
    base = resolved.stdout.decode().strip()
    present, unavailable = [], []
    file_owners: dict[str, list[dict]] = defaultdict(list)
    statuses = []
    for p in entries:
        if not commit_exists(repo, p["sha"]):
            unavailable.append({"pr": p["pr"], "expected_sha": p["sha"],
                                "status": "PINNED_COMMIT_NOT_FETCHED"})
            continue
        mb = merge_base(repo, base, p["sha"])
        if mb is None:
            statuses.append({"pr":p["pr"],"status":"UNRELATED_HISTORY"})
            continue
        changed = changes(repo, mb, p["sha"])
        rec = {"pr": p["pr"], "sha": p["sha"], "lane": p["lane"],
               "changed_files": len(changed),
               "already_in_baseline": ancestor(repo, p["sha"], base),
               "baseline_ancestor_of_donor": ancestor(repo, base, p["sha"]),
               "status": "SOURCE_ONLY_INSPECTED"}
        if check_merge_tree and not rec["already_in_baseline"]:
            mt = git(repo, "merge-tree", "--write-tree", base, p["sha"])
            rec["merge_tree_clean"] = mt.returncode == 0
            if mt.returncode not in (0, 1):
                rec["merge_tree_error"] = mt.stderr.decode()[:2000]
        statuses.append(rec)
        present.append(p)
        if rec["already_in_baseline"]:
            continue
        for path in changed:
            blob = object_id(repo, p["sha"], path)
            file_owners[path].append({"pr":p["pr"], "blob":blob, "lane":p["lane"]})

    identical, divergent = [], []
    for path, rows in sorted(file_owners.items()):
        if len(rows) < 2:
            continue
        bl = {x["blob"] for x in rows}
        if len(bl) == 1 and None not in bl:
            identical.append({"path":path,"owners":rows,"action":"DEDUP_SAME_GIT_BLOB"})
        else:
            divergent.append({"path":path,"owners":rows,"action":"HUMAN_RESOLVE_SAME_OBJECT_OR_DIFFERENT_SEMANTICS"})
    missing = len(unavailable)
    bad_merges = [x for x in statuses if x.get("merge_tree_clean") is False]
    return {
        "schema": "dashi-multi-pr-source-plan-v1",
        "group": group, "baseline_sha":base,"pinned_count":len(entries),
        "present_pinned":len(present), "unavailable_pinned":unavailable,
        "per_pr":statuses,"identical_blob_overlaps":identical,
        "divergent_path_overlaps":divergent,
        "merge_tree_failures":bad_merges,
        "safe_for_unattended_bulk_merge":False,
        "needs_human_integrated_source_resolution":bool(divergent or bad_merges),
        "all_heads_fetched":missing == 0,
        "can_claim_kernel_acceptance":False,
        "can_claim_clay_result":False,
        "notes": "Exact SHA local source inventory only. No branch, file or PR is merged."
    }


def main() -> None:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--repo",type=Path,default=Path.cwd())
    p.add_argument("--manifest",type=Path,
                   default=Path("Docs/roadmaps/ClayPortfolioPinnedIntegration20261114.json"))
    p.add_argument("--group",choices=["agda","lean"],required=True)
    p.add_argument("--baseline")
    p.add_argument("--merge-tree",action="store_true",help="check pairwise textual conflicts without updating refs")
    p.add_argument("--strict",action="store_true",help="nonzero when commits not available or overlaps need review")
    p.add_argument("--json",action="store_true")
    args=p.parse_args()
    path = args.manifest if args.manifest.is_absolute() else args.repo / args.manifest
    try:
        result=plan(args.repo,json.loads(path.read_text(encoding="utf-8")),
                    args.group,args.baseline,args.merge_tree)
    except (RuntimeError,ValueError,KeyError,OSError,UnicodeError,json.JSONDecodeError) as exc:
        p.exit(2,f"BLOCKED: {exc}\n")
    if args.json:
        print(json.dumps(result,indent=2))
    else:
        print(f"{args.group.upper()} {result['present_pinned']}/{result['pinned_count']} exact heads available")
        print("Identical overlaps",len(result["identical_blob_overlaps"]))
        print("Divergent overlaps",len(result["divergent_path_overlaps"]))
        print("Pairwise merge-tree failures",len(result["merge_tree_failures"]))
        print("NO MERGES / NO KERNEL PROOF / NO CLAY PROMOTION")
    if args.strict and (not result["all_heads_fetched"] or
                        result["needs_human_integrated_source_resolution"]):
        p.exit(3,"BLOCKED: fetch all pinned donor commits and resolve conflicts first\n")


if __name__ == "__main__":
    main()
