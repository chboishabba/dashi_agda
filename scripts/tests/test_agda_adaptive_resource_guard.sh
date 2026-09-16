#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
ADAPTIVE="$ROOT/scripts/run_agda29_adaptive_repo_check.sh"
CHECKER="$ROOT/scripts/run_agda29_parallel_check.sh"
PROFILE="$ROOT/scripts/agda_typecheck_resource_profiles.json"
TRIADIC="DASHI/Algebra/TriadicDepthTwoCyclotomicDFT.agda"

fail() {
  echo "FAIL: $*" >&2
  exit 1
}

# The observed OOM target must be scheduled as memory-risk.
python3 - "$PROFILE" "$TRIADIC" <<'PY'
import json, sys
profile = json.load(open(sys.argv[1]))
entry = profile.get("exact", {}).get(sys.argv[2], {})
if entry.get("class") != "memory-risk":
    raise SystemExit(f"expected memory-risk profile for {sys.argv[2]}, got {entry!r}")
PY

# A direct checker must refuse to launch Agda when host headroom is below the
# target RSS ceiling plus reserve.  Use a fake meminfo and /bin/true as Agda so
# this exercises the real launch boundary without compiling anything.
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT
mkdir -p "$tmp/DASHI" "$tmp/stdlib" "$tmp/cache" "$tmp/logs"
printf 'module DASHI.Test where\n' > "$tmp/DASHI/Test.agda"
cat > "$tmp/meminfo-low" <<'EOF'
MemTotal:       32768000 kB
MemAvailable:    4096000 kB
SwapTotal:      32768000 kB
SwapFree:              0 kB
EOF

set +e
DASHI_NO_TMUX=1 \
DASHI_REPO_ROOT="$tmp" \
DASHI_AGDA29_CACHE_ROOT="$tmp/cache" \
AGDA_BIN=/bin/true \
AGDA_STDLIB_SRC_29="$tmp/stdlib" \
AGDA_LOG_PATH="$tmp/logs/check.log" \
DASHI_MEMINFO_PATH="$tmp/meminfo-low" \
DASHI_AGDA_RSS_LIMIT_MB=5120 \
DASHI_AGDA_HOST_RESERVE_MB=2048 \
DASHI_AGDA_HOST_HEADROOM_FLOOR_MB=8192 \
"$CHECKER" DASHI/Test.agda >"$tmp/low.out" 2>&1
rc=$?
set -e
[ "$rc" -eq 75 ] || {
  cat "$tmp/low.out" >&2
  fail "low-host-headroom checker exit was $rc, expected 75"
}
grep -q 'host memory headroom' "$tmp/low.out" || fail "missing host-headroom diagnostic"

# Exercise adaptive resume and resource defaults without invoking Agda.
fixture="$tmp/fixture"
mkdir -p "$fixture/scripts" "$fixture/.cache"
cat > "$fixture/scripts/plan_agda_typecheck_targets.py" <<'PY'
#!/usr/bin/env python3
import argparse, json, os
from pathlib import Path
p = argparse.ArgumentParser()
p.add_argument('--root')
p.add_argument('--output', required=True)
p.add_argument('--heavy-output', required=True)
p.add_argument('--json', required=True)
p.add_argument('--include-heavy', action='store_true')
a = p.parse_args()
targets = [
  'DASHI/Before.agda',
  'DASHI/Algebra/TriadicDepthTwoCyclotomicDFT.agda',
  'DASHI/After.agda',
]
Path(a.output).write_text(''.join(x + '\n' for x in targets))
Path(a.heavy_output).write_text('')
Path(a.json).write_text(json.dumps({'selected': len(targets)}) + '\n')
PY
chmod +x "$fixture/scripts/plan_agda_typecheck_targets.py"
cat > "$fixture/scripts/run_agda29_parallel_check.sh" <<'SH'
#!/usr/bin/env bash
set -euo pipefail
printf '%s|%s|' "${AGDA_JOBS:-}" "${DASHI_AGDA_RSS_LIMIT_MB:-}" >> "$DASHI_TEST_INVOCATIONS"
paste -sd, "$AGDA_TARGETS_FILE" >> "$DASHI_TEST_INVOCATIONS"
SH
chmod +x "$fixture/scripts/run_agda29_parallel_check.sh"
: > "$tmp/invocations"

DASHI_REPO_ROOT="$fixture" \
DASHI_TEST_INVOCATIONS="$tmp/invocations" \
"$ADAPTIVE" \
  --profile "$PROFILE" \
  --report-dir "$tmp/report" \
  --from "$TRIADIC" >"$tmp/adaptive.out" 2>&1 || {
    cat "$tmp/adaptive.out" >&2
    fail "adaptive resume failed"
  }

# Resuming at the reclassified target skips the already-checked prefix.  The
# ordinary suffix runs with jobs=2; the memory-risk target runs alone at 5 GiB.
grep -Fxq '2|15360|DASHI/After.agda' "$tmp/invocations" || {
  cat "$tmp/invocations" >&2
  fail "ordinary resumed suffix did not use jobs=2"
}
grep -Fxq "1|5120|$TRIADIC" "$tmp/invocations" || {
  cat "$tmp/invocations" >&2
  fail "Triadic target did not run memory-risk jobs=1/rss=5120"
}
[ ! -e "$tmp/report/last-success.json" ] || fail "resumed run must not mint full success receipt"

echo "PASS: adaptive Agda resource guard regression"
