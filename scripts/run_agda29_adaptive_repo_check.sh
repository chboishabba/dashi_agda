#!/usr/bin/env bash
set -euo pipefail

REPO_ROOT="${DASHI_REPO_ROOT:-$(cd "$(dirname "$0")/.." && pwd)}"
INCLUDE_HEAVY=0
PLAN_ONLY=0
FROM_TARGET=""
REPORT_DIR="${DASHI_ADAPTIVE_REPO_CHECK_REPORT_DIR:-$REPO_ROOT/.cache/agda-adaptive-repo-check}"
PROFILE_FILE="${DASHI_AGDA_RESOURCE_PROFILE_FILE:-$REPO_ROOT/scripts/agda_typecheck_resource_profiles.json}"

usage() {
  cat <<'EOF'
Usage: scripts/run_agda29_adaptive_repo_check.sh [options]

Plan repository-wide first-party Agda typechecking with the existing canonical
planner, build the first-party import graph, order dependencies before their
consumers, partition by effective resource class, and run each class through
the existing Agda 2.9 checker/cache.

Resource classes are operational only:
  ordinary    default scheduling
  long-cpu    observed CPU-heavy; isolated from the ordinary frontier
  memory-risk observed high-memory; reduced Agda parallelism / RSS ceiling

Resource classes propagate through first-party imports: a target whose import
closure reaches a memory-risk owner is memory-risk too; long-cpu propagates in
the same way unless memory-risk dominates.  Strongly connected components are
scheduled as one dependency unit, with canonical order retained inside a cycle.
This changes scheduling only, not liveness or proof status.

Options:
  --include-heavy       include YM/NS/Balaban and their dependency closure
  --plan-only           write target/resource plans but do not invoke Agda
  --from PATH           resume at PATH in canonical target ordering
  --report-dir DIR      write plans and receipt under DIR
  --profile FILE        resource profile registry JSON
  -h, --help            show this help

Environment controls:
  AGDA_JOBS                         ordinary jobs (default 2)
  AGDA_LONG_CPU_JOBS                long-cpu jobs (default 2)
  AGDA_MEMORY_RISK_JOBS             memory-risk jobs (default 1)
  DASHI_AGDA_RSS_LIMIT_MB           ordinary RSS guard (default 8192)
  DASHI_AGDA_LONG_CPU_RSS_MB        long-cpu RSS guard (default ordinary limit)
  DASHI_AGDA_MEMORY_RISK_RSS_MB     memory-risk RSS guard (default 5120)
  DASHI_AGDA_HOST_HEADROOM_FLOOR_MB minimum MemAvailable+SwapFree before launch
                                      (default 10240)
  DASHI_AGDA_HOST_RESERVE_MB        reserve beyond target RSS ceiling
                                      (default 2048)
  DASHI_MEMINFO_PATH                meminfo source (default /proc/meminfo)
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
    --from)
      [ "$#" -ge 2 ] || { echo "--from requires a path" >&2; exit 2; }
      FROM_TARGET="$2"
      shift 2
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
RUN_TARGETS_FILE="$REPORT_DIR/run-targets.txt"
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

if [ -n "$FROM_TARGET" ]; then
  python3 - "$TARGETS_FILE" "$RUN_TARGETS_FILE" "$FROM_TARGET" <<'PY'
import sys
from pathlib import Path

src, dst, start = sys.argv[1:]
targets = [line.strip() for line in Path(src).read_text().splitlines() if line.strip()]
try:
    index = targets.index(start)
except ValueError:
    raise SystemExit(f"resume target not present in current plan: {start}")
Path(dst).write_text("".join(f"{target}\n" for target in targets[index:]))
PY
else
  cp "$TARGETS_FILE" "$RUN_TARGETS_FILE"
fi

python3 - \
  "$TARGETS_FILE" "$RUN_TARGETS_FILE" "$PROFILE_FILE" "$REPO_ROOT" \
  "$ORDINARY_FILE" "$LONG_CPU_FILE" "$MEMORY_RISK_FILE" \
  "$RESOURCE_SUMMARY" <<'PY'
import heapq
import json
import re
import sys
from pathlib import Path

(
    all_targets_path, run_targets_path, profile_path, root_path,
    ordinary_path, long_path, memory_path, summary_path,
) = sys.argv[1:]
root = Path(root_path)
all_targets = [line.strip() for line in Path(all_targets_path).read_text().splitlines() if line.strip()]
run_targets = [line.strip() for line in Path(run_targets_path).read_text().splitlines() if line.strip()]
run_set = set(run_targets)
canonical_index = {target: index for index, target in enumerate(all_targets)}
profile = json.loads(Path(profile_path).read_text())
exact = profile.get("exact", {})
prefix_rules = profile.get("prefix", [])
allowed = {"ordinary", "long-cpu", "memory-risk"}
severity = {"ordinary": 0, "long-cpu": 1, "memory-risk": 2}
by_severity = {value: key for key, value in severity.items()}
module_re = re.compile(r"^\s*module\s+([A-Za-z0-9_.]+)\s+where\b")
import_re = re.compile(r"^\s*(?:open\s+)?import\s+([A-Za-z0-9_.]+)")

module_to_path = {}
imports_by_path = {}
for rel in all_targets:
    module = None
    imports = []
    try:
        lines = (root / rel).read_text(errors="ignore").splitlines()
    except OSError:
        lines = []
    for raw in lines:
        if raw.lstrip().startswith("--"):
            continue
        if module is None:
            match = module_re.match(raw)
            if match:
                module = match.group(1)
        match = import_re.match(raw)
        if match:
            imports.append(match.group(1))
    if module:
        module_to_path[module] = rel
    imports_by_path[rel] = imports

deps = {
    rel: {module_to_path[name] for name in imports if name in module_to_path}
    for rel, imports in imports_by_path.items()
}

def direct_class(target):
    entry = exact.get(target)
    if isinstance(entry, dict):
        candidate = entry.get("class", "ordinary")
        if candidate not in allowed:
            raise SystemExit(f"invalid resource class {candidate!r} for {target}")
        return candidate, "exact"
    for rule in prefix_rules:
        if not isinstance(rule, dict):
            continue
        prefix = rule.get("path")
        candidate = rule.get("class")
        if isinstance(prefix, str) and target.startswith(prefix):
            if candidate not in allowed:
                raise SystemExit(f"invalid resource class {candidate!r} for prefix {prefix}")
            return candidate, "prefix"
    return "ordinary", "default"

# Tarjan SCC decomposition.  A cycle is one scheduling unit: dependencies can
# be warmed only to the component boundary, so keep the canonical order inside
# that component and propagate the strongest resource class to all its members.
index_counter = 0
stack = []
on_stack = set()
indices = {}
lowlink = {}
components = []
component_of = {}

sys.setrecursionlimit(max(10000, len(all_targets) * 2 + 100))

def strongconnect(node):
    global index_counter
    indices[node] = index_counter
    lowlink[node] = index_counter
    index_counter += 1
    stack.append(node)
    on_stack.add(node)

    for dep in sorted(deps.get(node, ()), key=canonical_index.__getitem__):
        if dep not in indices:
            strongconnect(dep)
            lowlink[node] = min(lowlink[node], lowlink[dep])
        elif dep in on_stack:
            lowlink[node] = min(lowlink[node], indices[dep])

    if lowlink[node] == indices[node]:
        component = []
        while True:
            member = stack.pop()
            on_stack.remove(member)
            component_of[member] = len(components)
            component.append(member)
            if member == node:
                break
        component.sort(key=canonical_index.__getitem__)
        components.append(component)

for target in all_targets:
    if target not in indices:
        strongconnect(target)

component_count = len(components)
component_key = {
    cid: min(canonical_index[target] for target in component)
    for cid, component in enumerate(components)
}
successors = {cid: set() for cid in range(component_count)}
predecessors = {cid: set() for cid in range(component_count)}
dependency_edges = 0
for consumer, consumer_deps in deps.items():
    consumer_cid = component_of[consumer]
    for dep in consumer_deps:
        dependency_edges += 1
        dep_cid = component_of[dep]
        if dep_cid == consumer_cid:
            continue
        successors[dep_cid].add(consumer_cid)
        predecessors[consumer_cid].add(dep_cid)

# Stable Kahn order over the condensation DAG.  The edge direction is
# dependency -> consumer, so this is exactly the cache-warming order.
indegree = {cid: len(predecessors[cid]) for cid in range(component_count)}
ready = [(component_key[cid], cid) for cid, degree in indegree.items() if degree == 0]
heapq.heapify(ready)
component_order = []
while ready:
    _, cid = heapq.heappop(ready)
    component_order.append(cid)
    for nxt in sorted(successors[cid], key=component_key.__getitem__):
        indegree[nxt] -= 1
        if indegree[nxt] == 0:
            heapq.heappush(ready, (component_key[nxt], nxt))

if len(component_order) != component_count:
    raise SystemExit("internal error: SCC condensation graph is not acyclic")

# Resource risk flows in the same direction as scheduling: a consumer inherits
# the strongest class of every first-party dependency.  Cycles already share a
# component, so this is exact on the condensation DAG.
component_direct_severity = {}
for cid, component in enumerate(components):
    component_direct_severity[cid] = max(
        severity[direct_class(target)[0]] for target in component
    )
component_effective_severity = dict(component_direct_severity)
for cid in component_order:
    current = component_effective_severity[cid]
    for nxt in successors[cid]:
        component_effective_severity[nxt] = max(
            component_effective_severity[nxt], current
        )

effective_class = {
    target: by_severity[component_effective_severity[component_of[target]]]
    for target in all_targets
}

ordered_targets = []
for cid in component_order:
    ordered_targets.extend(components[cid])

buckets = {name: [] for name in allowed}
matched_exact = 0
matched_prefix = 0
inherited = 0
for target in ordered_targets:
    if target not in run_set:
        continue
    direct, source = direct_class(target)
    effective = effective_class[target]
    if source == "exact":
        matched_exact += 1
    elif source == "prefix":
        matched_prefix += 1
    if severity[effective] > severity[direct]:
        inherited += 1
    buckets[effective].append(target)

for path, key in [
    (ordinary_path, "ordinary"),
    (long_path, "long-cpu"),
    (memory_path, "memory-risk"),
]:
    Path(path).write_text("".join(f"{target}\n" for target in buckets[key]))

cyclic_scc_count = sum(
    1
    for component in components
    if len(component) > 1 or any(node in deps.get(node, ()) for node in component)
)
summary = {
    "schema": "dashi.agda-resource-plan.v3",
    "selected_total": len(run_targets),
    "ordinary": len(buckets["ordinary"]),
    "long_cpu": len(buckets["long-cpu"]),
    "memory_risk": len(buckets["memory-risk"]),
    "matched_exact_profiles": matched_exact,
    "matched_prefix_profiles": matched_prefix,
    "inherited_resource_profiles": inherited,
    "unprofiled_defaulted_to_ordinary_before_dependency_propagation": (
        len(run_targets) - matched_exact - matched_prefix
    ),
    "dependency_ordered": True,
    "dependency_edges": dependency_edges,
    "strongly_connected_components": component_count,
    "cyclic_strongly_connected_components": cyclic_scc_count,
    "profile_file": str(Path(profile_path).resolve()),
}
Path(summary_path).write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n")
PY

ORDINARY_COUNT="$(wc -l < "$ORDINARY_FILE" | tr -d '[:space:]')"
LONG_CPU_COUNT="$(wc -l < "$LONG_CPU_FILE" | tr -d '[:space:]')"
MEMORY_RISK_COUNT="$(wc -l < "$MEMORY_RISK_FILE" | tr -d '[:space:]')"
TOTAL_COUNT=$(( ORDINARY_COUNT + LONG_CPU_COUNT + MEMORY_RISK_COUNT ))
FULL_PLANNED_COUNT="$(wc -l < "$TARGETS_FILE" | tr -d '[:space:]')"

printf 'Adaptive repository Agda plan: run=%d full=%d ordinary=%d long-cpu=%d memory-risk=%d\n' \
  "$TOTAL_COUNT" "$FULL_PLANNED_COUNT" "$ORDINARY_COUNT" "$LONG_CPU_COUNT" "$MEMORY_RISK_COUNT"
printf 'Targets: %s\n' "$TARGETS_FILE"
printf 'Run targets: %s\n' "$RUN_TARGETS_FILE"
printf 'Resource summary: %s\n' "$RESOURCE_SUMMARY"
printf 'Resource profile: %s\n' "$PROFILE_FILE"
if [ -n "$FROM_TARGET" ]; then
  printf 'Resume frontier: %s\n' "$FROM_TARGET"
fi

if [ "$PLAN_ONLY" = "1" ]; then
  exit 0
fi

if [ "$TOTAL_COUNT" -eq 0 ]; then
  echo "no targets selected" >&2
  exit 2
fi

ORDINARY_JOBS="${AGDA_JOBS:-2}"
LONG_CPU_JOBS="${AGDA_LONG_CPU_JOBS:-2}"
MEMORY_RISK_JOBS="${AGDA_MEMORY_RISK_JOBS:-1}"
ORDINARY_RSS_MB="${DASHI_AGDA_RSS_LIMIT_MB:-8192}"
LONG_CPU_RSS_MB="${DASHI_AGDA_LONG_CPU_RSS_MB:-$ORDINARY_RSS_MB}"
MEMORY_RISK_RSS_MB="${DASHI_AGDA_MEMORY_RISK_RSS_MB:-5120}"
HOST_HEADROOM_FLOOR_MB="${DASHI_AGDA_HOST_HEADROOM_FLOOR_MB:-10240}"
HOST_RESERVE_MB="${DASHI_AGDA_HOST_RESERVE_MB:-2048}"
MEMINFO_PATH="${DASHI_MEMINFO_PATH:-/proc/meminfo}"

for value_name in ORDINARY_JOBS LONG_CPU_JOBS MEMORY_RISK_JOBS ORDINARY_RSS_MB LONG_CPU_RSS_MB MEMORY_RISK_RSS_MB HOST_HEADROOM_FLOOR_MB HOST_RESERVE_MB; do
  value="${!value_name}"
  if ! [[ "$value" =~ ^[0-9]+$ ]] || [ "$value" -eq 0 ]; then
    echo "$value_name must be a positive integer" >&2
    exit 2
  fi
done

host_headroom_mb() {
  python3 - "$MEMINFO_PATH" <<'PY'
import sys
from pathlib import Path

path = Path(sys.argv[1])
try:
    text = path.read_text()
except OSError as exc:
    raise SystemExit(f"cannot read meminfo {path}: {exc}")
values = {}
for line in text.splitlines():
    parts = line.split()
    if len(parts) >= 2 and parts[0] in {"MemAvailable:", "SwapFree:"}:
        values[parts[0][:-1]] = int(parts[1])
missing = {"MemAvailable", "SwapFree"} - values.keys()
if missing:
    raise SystemExit(f"meminfo missing fields: {sorted(missing)}")
print((values["MemAvailable"] + values["SwapFree"]) // 1024)
PY
}

require_host_headroom() {
  local class_name="$1"
  local rss_mb="$2"
  local headroom_mb required_mb
  headroom_mb="$(host_headroom_mb)"
  required_mb=$(( rss_mb + HOST_RESERVE_MB ))
  if [ "$required_mb" -lt "$HOST_HEADROOM_FLOOR_MB" ]; then
    required_mb="$HOST_HEADROOM_FLOOR_MB"
  fi
  printf 'Host headroom before %s: %s MiB available+swap-free; require %s MiB\n' \
    "$class_name" "$headroom_mb" "$required_mb"
  if [ "$headroom_mb" -lt "$required_mb" ]; then
    echo "host memory headroom too low for $class_name: ${headroom_mb} MiB < ${required_mb} MiB; refusing to launch Agda" >&2
    return 75
  fi
}

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

  require_host_headroom "$class_name" "$rss_mb"

  echo
  printf '=== Agda resource class: %s (%d targets, jobs=%s, rss-limit=%s MiB) ===\n' \
    "$class_name" "$count" "$jobs" "$rss_mb"

  AGDA_TARGETS_FILE="$targets_file" \
  AGDA_JOBS="$jobs" \
  DASHI_AGDA_RSS_LIMIT_MB="$rss_mb" \
    "$REPO_ROOT/scripts/run_agda29_parallel_check.sh"
}

run_class "ordinary" "$ORDINARY_FILE" "$ORDINARY_JOBS" "$ORDINARY_RSS_MB"
run_class "long-cpu" "$LONG_CPU_FILE" "$LONG_CPU_JOBS" "$LONG_CPU_RSS_MB"
run_class "memory-risk" "$MEMORY_RISK_FILE" "$MEMORY_RISK_JOBS" "$MEMORY_RISK_RSS_MB"

if [ -n "$FROM_TARGET" ]; then
  echo "Resumed suffix passed; rerun without --from before claiming full coverage."
  exit 0
fi

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
