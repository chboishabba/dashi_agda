#!/usr/bin/env bash
set -euo pipefail

repo="${1:-../../..}"
output="${2:-/tmp/dashi-history-smoke.json}"
quality="${3:--ql}"

python - "$repo" "$output" <<'PY'
import json
import subprocess
import sys

repo, output = sys.argv[1:3]
lines = subprocess.check_output(
    [
        "git",
        "-C",
        repo,
        "log",
        "--first-parent",
        "--reverse",
        "--max-count=120",
        "--format=%H%x09%ct%x09%P%x09%s",
        "HEAD",
    ],
    text=True,
).splitlines()

commits = []
for line in lines:
    sha, timestamp, parents, message = line.split("\t", 3)
    commits.append(
        {
            "commit": sha,
            "timestamp": int(timestamp),
            "parents": parents.split() if parents else [],
            "refs": [],
            "shape": "merge" if len(parents.split()) > 1 else "linear",
            "message": message,
        }
    )

payload = {
    "schema": "dashi.repo-history.v1",
    "commits": commits,
    "refs": {},
    "branch_episodes": [],
    "snapshots": [],
}
with open(output, "w", encoding="utf-8") as handle:
    json.dump(payload, handle, indent=2)
print(output)
PY

export DASHI_REPO_HISTORY_JSON="$output"
python -m manim "$quality" \
  tools/visualization/repo_history/examples/manim_history_smoke.py \
  DashiRepositoryHistorySmoke
