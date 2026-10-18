#!/usr/bin/env python3

from __future__ import annotations

import argparse
import json
import subprocess

from pathlib import Path


def sh(*args):
    return subprocess.check_output(args, text=True).strip()


def main():
    ap = argparse.ArgumentParser(description="Read-only PR/branch delta manifest.")
    ap.add_argument("head", help="PR head ref/sha")
    ap.add_argument("--base", default="master")
    ap.add_argument("--out")
    args = ap.parse_args()

    merge_base = sh("git", "merge-base", args.base, args.head)
    changed_text = sh("git", "diff", "--name-status", merge_base, args.head)
    commits_text = sh(
        "git", "log", "--format=%H%x09%s", f"{merge_base}..{args.head}"
    )

    changed = changed_text.splitlines() if changed_text else []
    commits = commits_text.splitlines() if commits_text else []
    agda = [line for line in changed if line.rstrip().endswith(".agda")]
    rounds = [line for line in agda if "Round" in line]

    report = {
        "schema_version": 1,
        "base": args.base,
        "head": args.head,
        "merge_base": merge_base,
        "commit_count": len(commits),
        "commits": commits,
        "changed_file_count": len(changed),
        "changed_files": changed,
        "changed_agda_count": len(agda),
        "changed_round_agda_count": len(rounds),
        "changed_round_agda": rounds,
        "next_step": (
            "Index the head in a separate SQLite DB, then run canonical fingerprint "
            "comparison against the base DB. Do not classify semantic value from paths alone."
        ),
    }

    text = json.dumps(report, indent=2) + "\n"
    if args.out:
        Path(args.out).write_text(text)
    print(text, end="")


if __name__ == "__main__":
    main()
