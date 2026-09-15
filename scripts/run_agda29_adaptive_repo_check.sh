#!/usr/bin/env bash
set -euo pipefail

REPO_ROOT="${DASHI_REPO_ROOT:-$(cd "$(dirname "$0")/.." && pwd)}"
INCLUDE_HEAVY=0
PLAN_ONLY=0
REPORT_DIR="${DASHI_ADAPTIVE_REPO_CHECK_REPORT_DIR:-$REPO_ROOT/.cache/agda-adaptive-repo-check}"
PROFILE_FILE="${DASHI_AGDA_RESOURCE_PROFILE_FILE:-$REPO_ROOT/scripts/agda_typecheck_resource_profiles.json}"

usage() {
  cat <<'EOF'
Usage: scripts/run_agda29_adaptive_repo_check.sh [options]

Plan repository-wide first-party Agda typechecking with the existing canonical
planner, partition the selected live targets by empirical resource class, and
run each class through the existing Agda 2.9 checker/cache.

Resource classes are operational only:
  ordinary    default scheduling
  long-cpu    observed CPU-heavy; isolated from the ordinary frontier
  memory-risk observed high-memory; reduced Agda parallelism

No class changes liveness or proof status. Every selected target still has to
pass before this wrapper writes a success receipt.

Options:
  --include-heavy       include YM/NS/Balaban and their dependency closure
  --plan-only           write target/resource plans but do not invoke Agda
  --report-dir DIR      write plans and receipt under DIR
  --profile FILE        resource profile registry JSON
  -h, --help            show this help

Environment controls:
  AGDA_JOBS                     ordinary jobs (default 4)
  AGDA_LONG_CPU_JOBS            long-cpu jobs (default 2)
  AGDA_MEMORY_RISK_JOBS         memory-risk jobs (default 1)
  DASHI_AGDA_RSS_LIMIT_MB       ordinary RSS guard (default 15360)
  DASHI_AGDA_LONG_CPU_RSS_MB    long-cpu RSS guard (default ordinary limit)
  DASHI_AGDA_MEMORY_RISK_RSS_MB memory-risk RSS guard (default ordinary limit)
EOF
}

while [ "$#" -gt 0 ]; do
  case "$1" in
    --include-heavy)
      INCLUDE_HEAVY=1
      shift
      ;;
    --plan-only)
      PLAN_ONLY=1
      shift
      ;;
    --report-dir)
      [ "$#" -ge 2 ] || { echo "--report-dir requires a directory" >&2; exit 2; }
      REPORT_DIR="$2"
      shift 2
      ;;
    --profile)
      [ "$#" -ge 2 ] || { echo "--profile requires a file" >&2; exit 2; }
      PROFILE_FILE="$2"
      shift 2
      ;;
    -h|--help)
      usage
      exit 0
      ;;
    *)
      echo "unknown option: $1" >&2
      usage >&2
      exit 2
      ;;
  esac
done

[ -f "$PROFILE_FILE" ] || { echo "resource profile not found: $PROFILE_FILE" >&2; exit 2; }
mkdir -p "$REPORT_DIR"

TARGETS_FILE="$REPORT_DIR/targets.txt"
HEAVY_FILE="$REPORT_DIR/heavy-or-tainted-skipped.txt"
PLANNER_SUMMARY="$REPORT_DIR/planner-summary.json"
ORDINARY_FILE="$REPORT_DIR/ordinary.txt"
LONG_CPU_FILE="$REPORT_DIR/long-cpu.txt"
MEMORY_RISK_FILE="$REPORT_DIR/memory-risk.txt"
RESOURCE_SUMMARY="$REPORT_DIR/resource-summary.json"
SUCCESS_FILE="$REPORT_DIR/last-success.json"
rm -f "$SUCCESS_FILE"

planner=(python3 "$REPO_ROOT/scripts/plan_agda_typecheck_targets.py"
  --root "$REPO_ROOT"
  --output "$TARGETS_FILE"
  --heavy-output "$HEAVY_FILE"
  --json "$PLANNER_SUMMARY")
if [ "$INCLUDE_HEAVY" = "1" ]; then
  planner+=(--include-heavy)
fi
"${planner[@]}"

python3 - \
  "$TARGETS_FILE" "$PROFILE_FILE" \
  "$ORDINARY_FILE" "$LONG_CPU_FILE" "$MEMORY_RISK_FILE" \
  "$RESOURCE_SUMMARY" <<'PY'
import json
import sys
from pathlib import Path

targets_path, profile_path, ordinary_path, long_path, memory_path, summary_path = sys.argv[1:]
targets = [line.strip() for line in Path(targets_path).read_text().splitlines() if line.strip()]
profile = json.loads(Path(profile_path).read_text())
exact = profile.get("exact", {})
prefix_rules = profile.get("prefix", [])
allowed = {"ordinary", "long-cpu", "memory-risk"}

buckets = {name: [] for name in allowed}
matched_exact = 0
matched_prefix = 0

for target in targets:
    resource_class = "ordinary"
    entry = exact.get(target)
    if isinstance(entry, dict):
        candidate = entry.get("class", "ordinary")
        if candidate not in allowed:
            raise SystemExit(f"invalid resource class {candidate!r} for {target}")
        resource_class = candidate
        matched_exact += 1
    else:
        for rule in prefix_rules:
            if not isinstance(rule, dict):
                continue
            prefix = rule.get("path")
            candidate = rule.get("class")
            if isinstance(prefix, str) and target.startswith(prefix):
                if candidate not in allowed:
                    raise SystemExit(f"invalid resource class {candidate!r} for prefix {prefix}")
                resource_class = candidate
                matched_prefix += 1
                break
    buckets[resource_class].append(target)

for path, key in [
    (ordinary_path, "ordinary"),
    (long_path, "long-cpu"),
    (memory_path, "memory-risk"),
]:
    Path(path).write_text("".join(f"{target}\n" for target in buckets[key]))

summary = {
    "schema": "dashi.agda-resource-plan.v1",
    "selected_total": len(targets),
    "ordinary": len(buckets["ordinary"]),
    "long_cpu": len(buckets["long-cpu"]),
    "memory_risk": len(buckets["memory-risk"]),
    "matched_exact_profiles": matched_exact,
    "matched_prefix_profiles": matched_prefix,
    "unprofiled_defaulted_to_ordinary": len(targets) - matched_exact - matched_prefix,
    "profile_file": str(Path(profile_path).resolve()),
}
Path(summary_path).write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n")
PY

ORDINARY_COUNT="$(wc -l < "$ORDINARY_FILE" | tr -d '[:space:]')"
LONG_CPU_COUNT="$(wc -l < "$LONG_CPU_FILE" | tr -d '[:space:]')"
MEMORY_RISK_COUNT="$(wc -l < "$MEMORY_RISK_FILE" | tr -d '[:space:]')"
TOTAL_COUNT=$(( ORDINARY_COUNT + LONG_CPU_COUNT + MEMORY_RISK_COUNT ))

printf 'Adaptive repository Agda plan: total=%d ordinary=%d long-cpu=%d memory-risk=%d\n' \
  "$TOTAL_COUNT" "$ORDINARY_COUNT" "$LONG_CPU_COUNT" "$MEMORY_RISK_COUNT"
printf 'Targets: %s\n' "$TARGETS_FILE"
printf 'Resource summary: %s\n' "$RESOURCE_SUMMARY"
printf 'Resource profile: %s\n' "$PROFILE_FILE"

if [ "$PLAN_ONLY" = "1" ]; then
  exit 0
fi

if [ "$TOTAL_COUNT" -eq 0 ]; then
  echo "no targets selected" >&2
  exit 2
fi

ORDINARY_JOBS="${AGDA_JOBS:-4}"
LONG_CPU_JOBS="${AGDA_LONG_CPU_JOBS:-2}"
MEMORY_RISK_JOBS="${AGDA_MEMORY_RISK_JOBS:-1}"
ORDINARY_RSS_MB="${DASHI_AGDA_RSS_LIMIT_MB:-15360}"
LONG_CPU_RSS_MB="${DASHI_AGDA_LONG_CPU_RSS_MB:-$ORDINARY_RSS_MB}"
MEMORY_RISK_RSS_MB="${DASHI_AGDA_MEMORY_RISK_RSS_MB:-$ORDINARY_RSS_MB}"

run_class() {
  local class_name="$1"
  local targets_file="$2"
  local jobs="$3"
  local rss_mb="$4"
  local count
  count="$(wc -l < "$targets_file" | tr -d '[:space:]')"
  if [ "$count" -eq 0 ]; then
    return 0
  fi

  echo
  printf '=== Agda resource class: %s (%d targets, jobs=%s, rss-limit=%s MiB) ===\n' \
    "$class_name" "$count" "$jobs" "$rss_mb"

  AGDA_TARGETS_FILE="$targets_file" \
  AGDA_JOBS="$jobs" \
  DASHI_AGDA_RSS_LIMIT_MB="$rss_mb" \
    "$REPO_ROOT/scripts/run_agda29_parallel_check.sh"
}

# Ordinary targets go first so the repair frontier advances through cheap
# modules before expensive targets consume workstation time. Long-CPU and
# memory-risk targets stay live and are checked afterwards in isolated Agda
# processes through the existing checker/cache.
run_class "ordinary" "$ORDINARY_FILE" "$ORDINARY_JOBS" "$ORDINARY_RSS_MB"
run_class "long-cpu" "$LONG_CPU_FILE" "$LONG_CPU_JOBS" "$LONG_CPU_RSS_MB"
run_class "memory-risk" "$MEMORY_RISK_FILE" "$MEMORY_RISK_JOBS" "$MEMORY_RISK_RSS_MB"

COMMIT_SHA="$(git -C "$REPO_ROOT" rev-parse HEAD 2>/dev/null || printf unknown)"
TARGETS_SHA256="$(sha256sum "$TARGETS_FILE" | awk '{print $1}')"
PROFILE_SHA256="$(sha256sum "$PROFILE_FILE" | awk '{print $1}')"
CHECKED_AT="$(date -u +%Y-%m-%dT%H:%M:%SZ)"
HEAVY_COUNT="$(wc -l < "$HEAVY_FILE" | tr -d '[:space:]')"

python3 - \
  "$SUCCESS_FILE" "$COMMIT_SHA" "$TARGETS_SHA256" "$PROFILE_SHA256" \
  "$TOTAL_COUNT" "$ORDINARY_COUNT" "$LONG_CPU_COUNT" "$MEMORY_RISK_COUNT" \
  "$HEAVY_COUNT" "$INCLUDE_HEAVY" "$CHECKED_AT" <<'PY'
import json
import sys

(
    path, commit, targets_hash, profile_hash, total_count, ordinary_count,
    long_count, memory_count, heavy_count, include_heavy, checked_at,
) = sys.argv[1:]
receipt = {
    "schema": "dashi.agda-adaptive-repo-typecheck.v1",
    "commit": commit,
    "checked_at_utc": checked_at,
    "targets_sha256": targets_hash,
    "resource_profile_sha256": profile_hash,
    "checked_target_count": int(total_count),
    "resource_counts": {
        "ordinary": int(ordinary_count),
        "long_cpu": int(long_count),
        "memory_risk": int(memory_count),
    },
    "operationally_skipped_heavy_or_tainted": int(heavy_count),
    "include_heavy": include_heavy == "1",
    "claim": (
        "all planned first-party Agda targets typechecked under adaptive resource scheduling"
        if include_heavy != "1"
        else "all first-party Agda targets typechecked including heavy lanes under adaptive resource scheduling"
    ),
}
with open(path, "w") as handle:
    json.dump(receipt, handle, indent=2, sort_keys=True)
    handle.write("\n")
PY

printf '\nSUCCESS receipt: %s\n' "$SUCCESS_FILE"
