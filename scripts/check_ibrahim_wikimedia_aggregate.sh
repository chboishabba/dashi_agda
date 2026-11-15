#!/usr/bin/env bash
# M5: full Wikimedia aggregate Agda typecheck with bounded diagnostic receipt.
# A focused-module PASS never substitutes for full aggregate acceptance.
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
AGDA_BIN="${AGDA_BIN:-agda}"
LOGDIR="${IBRAHIM_M5_LOGDIR:-$ROOT/artifacts/ibrahim_wikimedia_aggregate_local}"
SECONDS_LIMIT="${IBRAHIM_M5_TIMEOUT_SECONDS:-3600}"
MEMORY_KIB="${IBRAHIM_M5_VIRTUAL_MEMORY_KIB:-16777216}"
if ! command -v "$AGDA_BIN" >/dev/null 2>&1; then
  echo "BLOCKED: Agda not installed; M5 not accepted" >&2
  exit 127
fi
if ! [[ "$SECONDS_LIMIT" =~ ^[1-9][0-9]*$ && "$MEMORY_KIB" =~ ^[1-9][0-9]*$ ]]; then
  echo "BLOCKED: positive decimal resource budgets required" >&2
  exit 2
fi
mkdir -p "$LOGDIR"
LOGDIR="$(cd "$LOGDIR" && pwd -P)"
if [ -e "$LOGDIR/receipt.json" ]; then
  echo "BLOCKED: M5 receipt exists; do not silently overwrite old exact-head evidence" >&2
  exit 2
fi
HEAD="$(git rev-parse HEAD)"
AGDA_VERSION="$("$AGDA_BIN" --version)"
printf 'M5 aggregate head=%s\nAgda=%s\n' "$HEAD" "$AGDA_VERSION"
# ulimit is subshell-scoped; build logs remain available even on timeout.
(
  ulimit -v "$MEMORY_KIB"
  timeout --signal=TERM --kill-after=30s "$SECONDS_LIMIT" "$AGDA_BIN" \
    --safe -i . -l standard-library DASHI/Wikimedia/Everything.agda
) >"$LOGDIR/stdout.log" 2>"$LOGDIR/stderr.log"
STATUS=$?
python3 - "$LOGDIR" "$HEAD" "$AGDA_VERSION" "$SECONDS_LIMIT" "$MEMORY_KIB" "$STATUS" <<'PY'
import hashlib, json
from pathlib import Path
import sys
d, head, version, timeout, mem, code = sys.argv[1:]
d = Path(d)
def digest(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()
n = int(code)
receipt = {
    "version": "dashi.ibrahim.wikimedia_aggregate_local.v1",
    "git_head": head, "agda_version": version,
    "agda_command": ["agda","--safe","-i",".","-l","standard-library",
                     "DASHI/Wikimedia/Everything.agda"],
    "resource_timeout_seconds": int(timeout),
    "memory_limit_kib": int(mem),
    "exit_code": n,
    "stdout_sha256": digest(d / "stdout.log"),
    "stderr_sha256": digest(d / "stderr.log"),
    "full_wikimedia_aggregate_kernel_accepted": n == 0,
    "resource_limited_or_failed": n != 0,
    "historical_wikipedia_corpus_authenticated": False,
}
(d / "receipt.json").write_text(json.dumps(receipt, sort_keys=True, indent=2) + "\n")
print(json.dumps(receipt, sort_keys=True, indent=2))
PY
if [ "$STATUS" -ne 0 ]; then
  echo "M5 OPEN: aggregate typecheck failed/resource-limited; inspect $LOGDIR/stderr.log" >&2
  exit "$STATUS"
fi
echo "M5 PASS: full Wikimedia aggregate accepted at exact head $HEAD"
