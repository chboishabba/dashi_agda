#!/usr/bin/env python3
"""Build a deterministic first-path-implementation chronology from Git history.

This index establishes source chronology only.  It does not certify type-check,
kernel validation, mathematical correctness, semantic same-object identity
across renames/refactors, publication priority, or external novelty.

By default the script indexes files currently tracked by HEAD and searches all
reachable refs for the earliest commit in which each exact path appears.  That
is intentionally a path-level lower layer.  If a later filename is proved to be
the same mathematical object as an earlier differently named implementation,
record that semantic carryback separately in a typed priority ledger.
"""

from __future__ import annotations

import argparse
import csv
import datetime as dt
import subprocess
from pathlib import Path
from zoneinfo import ZoneInfo


def git(*args: str) -> str:
    return subprocess.check_output(["git", *args], text=True).strip()


def tracked_files() -> list[str]:
    out = git("ls-files")
    return [line for line in out.splitlines() if line]


def first_exact_path_commit(path: str) -> tuple[str, str] | None:
    # --all makes the chronology repository-wide across reachable refs.  We do
    # not use --follow here because rename equivalence is a semantic claim and
    # belongs in an explicit same-object ledger rather than this mechanical
    # path index.
    proc = subprocess.run(
        [
            "git",
            "log",
            "--all",
            "--reverse",
            "--format=%H%x09%cI",
            "--",
            path,
        ],
        text=True,
        stdout=subprocess.PIPE,
        check=True,
    )
    rows = [line for line in proc.stdout.splitlines() if line]
    if not rows:
        return None
    sha, iso = rows[0].split("\t", 1)
    return sha, iso


def normalize_times(iso: str, timezone: str) -> tuple[str, str]:
    stamp = dt.datetime.fromisoformat(iso.replace("Z", "+00:00"))
    utc = stamp.astimezone(dt.timezone.utc).isoformat().replace("+00:00", "Z")
    local = stamp.astimezone(ZoneInfo(timezone)).isoformat()
    return utc, local


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--timezone", default="Australia/Brisbane",
        help="IANA timezone used for the local-time column",
    )
    parser.add_argument(
        "--output", default="artifacts/FirstImplementationTimestampIndex.tsv",
        help="TSV output path",
    )
    parser.add_argument(
        "--suffix", action="append", default=[],
        help="optional suffix filter; repeat, e.g. --suffix .agda --suffix .lean",
    )
    args = parser.parse_args()

    files = tracked_files()
    if args.suffix:
        files = [p for p in files if any(p.endswith(s) for s in args.suffix)]

    output = Path(args.output)
    output.parent.mkdir(parents=True, exist_ok=True)

    rows: list[tuple[str, str, str, str, str]] = []
    for path in sorted(files):
        first = first_exact_path_commit(path)
        if first is None:
            continue
        sha, iso = first
        utc, local = normalize_times(iso, args.timezone)
        rows.append((path, sha, utc, local, args.timezone))

    with output.open("w", newline="", encoding="utf-8") as fh:
        writer = csv.writer(fh, delimiter="\t", lineterminator="\n")
        writer.writerow(
            [
                "path",
                "first_exact_path_commit",
                "first_commit_utc",
                "first_commit_local",
                "local_timezone",
            ]
        )
        writer.writerows(rows)

    print(f"wrote {len(rows)} chronology rows to {output}")
    print("boundary: source chronology only; semantic same-object and validation are separate")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
