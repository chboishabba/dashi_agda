#!/usr/bin/env bash
set -u -o pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT_DIR"

TS="$(date +%Y%m%d_%H%M%S)"
AGDA_BIN="${AGDA_BIN:-agda}"
MAX_WORKERS="${MAX_WORKERS:-3}"
VERBOSE="${VERBOSE:-1}"
OUT_DIR=""
FROM_STAGE_ID=""
ONLY_STAGE_IDS_CSV=""
LIST_STAGES=0
DISCOVER_ONLY=0
CLASS_FILTER=""
EXCLUDE_HEAVY=1
CACHE_ENABLED=1
REFRESH_CACHE=0
METADATA_FILE=".cache/closure_hygiene_metadata.tsv"
TIMEOUT_LADDER_CSV=""
declare -a TIMEOUT_LADDER=()
ONLY_FILTER_COUNT=0
declare -A ONLY_STAGE_FILTER=()
declare -A ALIAS_TO_KEY=(
  ["01"]="module:DASHI/Physics/Closure/CanonicalStageCTheoremBundle.agda"
  ["02"]="module:DASHI/Everything.agda"
  ["03"]="audit:canonical_path_audit"
  ["04"]="audit:placeholder_postulate_audit"
  ["05"]="audit:closure_status_pointers"
)
STAGE_ORDER=("01" "02" "03" "04" "05")
HEAVY_AGGREGATORS=(
  "DASHI/Everything.agda"
  "DASHI/Physics/Closure/PhysicsClosureValidationSummary.agda"
  "DASHI/Physics/Closure/ShiftContractObservableTransportPrimeCompatibilityProfileInstance.agda"
  "DASHI/Physics/Closure/ShiftObservableSignaturePressureConsumer.agda"
  "DASHI/Physics/DashiDynamicsShiftInstance.agda"
  "DASHI/Physics/Closure/CanonicalAbstractGaugeMatterInstance.agda"
  "DASHI/Physics/Closure/CanonicalGaugeMatterStrengtheningTheorem.agda"
  "DASHI/Physics/Closure/KnownLimitsFullMatterGaugeTheorem.agda"
  "DASHI/Physics/Closure/AtomicPhotonuclearContactGateTheorem.agda"
  "DASHI/Physics/Closure/CanonicalScheduleIndependentNaturalChargeNextIngredientGap.agda"
)

usage() {
  cat <<'EOF'
Usage: bash scripts/run_closure_hygiene.sh [options] [OUT_DIR]

Options:
  -j, --jobs N        Max parallel workers (default: 3 or $MAX_WORKERS)
  --from ID           Run alias stages with numeric ID >= ID (01..05)
  --only IDS          Run only selected alias IDs, comma-separated (e.g. 01,03,05)
  --list-stages       Print built-in alias stages and exit
  --discover-modules  Print discovered modules with learned classes and exit
  --class CLASS       Run only learned class: fast, medium, heavy, aggregator, audit
  --include-heavy     Include learned heavy and aggregator tasks
  --exclude-heavy     Skip learned heavy and aggregator tasks (default)
  --timeout-ladder S  Timeout sweep in seconds, comma-separated (e.g. 1,2,5,10,30)
  --no-cache          Disable metadata lookup/update
  --refresh-cache     Ignore cached passes for this run, but update metadata
  --metadata-file P   Metadata file path (default: .cache/closure_hygiene_metadata.tsv)
  --cache-file P      Alias for --metadata-file
  -v, --verbose       Stream heavy/aggregator build output to terminal (default)
  -V, --very-verbose  Stream all task output to terminal
  -q, --quiet         Only print queue/progress/final status
  -h, --help          Show this help
EOF
}

normalize_stage_id() {
  local raw="$1"
  if ! [[ "$raw" =~ ^[0-9]+$ ]]; then
    echo "[error] invalid stage ID '$raw' (expected integer like 01 or 3)" >&2
    exit 2
  fi
  if [ "$raw" -lt 1 ] || [ "$raw" -gt 99 ]; then
    echo "[error] stage ID out of range '$raw' (expected 1..99)" >&2
    exit 2
  fi
  printf '%02d' "$((10#$raw))"
}

list_stages() {
  echo "01  module:DASHI/Physics/Closure/CanonicalStageCTheoremBundle.agda"
  echo "02  module:DASHI/Everything.agda"
  echo "03  audit:canonical_path_audit"
  echo "04  audit:placeholder_postulate_audit"
  echo "05  audit:closure_status_pointers"
}

parse_timeout_ladder() {
  local csv="$1"
  local item
  local -a items=()
  IFS=',' read -r -a items <<< "$csv"
  for item in "${items[@]}"; do
    if ! [[ "$item" =~ ^[0-9]+$ ]] || [ "$item" -lt 1 ]; then
      echo "[error] invalid timeout ladder entry '$item' (positive integer seconds required)" >&2
      exit 2
    fi
    TIMEOUT_LADDER+=( "$item" )
  done
}

load_only_filter() {
  local csv="$1"
  local item sid
  local -a items=()
  IFS=',' read -r -a items <<< "$csv"
  for item in "${items[@]}"; do
    sid="$(normalize_stage_id "$item")"
    if [ -z "${ALIAS_TO_KEY[$sid]+x}" ]; then
      echo "[error] unknown stage ID in --only: $sid" >&2
      list_stages >&2
      exit 2
    fi
    ONLY_STAGE_FILTER["$sid"]=1
  done
  ONLY_FILTER_COUNT="${#ONLY_STAGE_FILTER[@]}"
}

while [ "$#" -gt 0 ]; do
  case "$1" in
    -j|--jobs)
      shift
      [ "$#" -gt 0 ] || { echo "[error] missing value for --jobs" >&2; exit 2; }
      MAX_WORKERS="$1"
      ;;
    --from)
      shift
      [ "$#" -gt 0 ] || { echo "[error] missing value for --from" >&2; exit 2; }
      FROM_STAGE_ID="$(normalize_stage_id "$1")"
      ;;
    --only)
      shift
      [ "$#" -gt 0 ] || { echo "[error] missing value for --only" >&2; exit 2; }
      ONLY_STAGE_IDS_CSV="$1"
      ;;
    --list-stages)
      LIST_STAGES=1
      ;;
    --discover-modules)
      DISCOVER_ONLY=1
      ;;
    --class)
      shift
      [ "$#" -gt 0 ] || { echo "[error] missing value for --class" >&2; exit 2; }
      CLASS_FILTER="$1"
      ;;
    --include-heavy)
      EXCLUDE_HEAVY=0
      ;;
    --exclude-heavy)
      EXCLUDE_HEAVY=1
      ;;
    --timeout-ladder)
      shift
      [ "$#" -gt 0 ] || { echo "[error] missing value for --timeout-ladder" >&2; exit 2; }
      TIMEOUT_LADDER_CSV="$1"
      ;;
    --no-cache)
      CACHE_ENABLED=0
      ;;
    --refresh-cache)
      REFRESH_CACHE=1
      ;;
    --metadata-file|--cache-file)
      shift
      [ "$#" -gt 0 ] || { echo "[error] missing value for $1" >&2; exit 2; }
      METADATA_FILE="$1"
      ;;
    -v|--verbose)
      VERBOSE=1
      ;;
    -V|--very-verbose)
      VERBOSE=2
      ;;
    -q|--quiet)
      VERBOSE=0
      ;;
    -h|--help)
      usage
      exit 0
      ;;
    *)
      if [ -z "$OUT_DIR" ]; then
        OUT_DIR="$1"
      else
        echo "[error] unexpected argument: $1" >&2
        exit 2
      fi
      ;;
  esac
  shift
done

if [ "$LIST_STAGES" -eq 1 ]; then
  list_stages
  exit 0
fi

if ! [[ "$MAX_WORKERS" =~ ^[0-9]+$ ]] || [ "$MAX_WORKERS" -lt 1 ]; then
  echo "[error] MAX_WORKERS must be a positive integer, got: $MAX_WORKERS" >&2
  exit 2
fi

if [ -n "$ONLY_STAGE_IDS_CSV" ]; then
  load_only_filter "$ONLY_STAGE_IDS_CSV"
fi

if [ -n "$TIMEOUT_LADDER_CSV" ]; then
  parse_timeout_ladder "$TIMEOUT_LADDER_CSV"
fi

OUT_DIR="${OUT_DIR:-artifacts/closure_hygiene_${TS}}"
mkdir -p "$OUT_DIR"
if [ "$CACHE_ENABLED" -eq 1 ]; then
  metadata_dir="$(dirname -- "$METADATA_FILE")"
  if [ -n "$metadata_dir" ] && [ "$metadata_dir" != "." ]; then
    mkdir -p "$metadata_dir"
  fi
fi

declare -A META_FP=()
declare -A META_RC=()
declare -A META_TS=()
declare -A META_DUR=()
declare -A META_CLASS=()
declare -A META_LABEL=()

declare -A TASK_KIND=()
declare -A TASK_LABEL=()
declare -A TASK_CLASS=()
declare -A TASK_ARTIFACT=()
declare -A TASK_COMMAND=()
declare -A TASK_STREAM=()
declare -A TASK_DEPS=()
declare -a TASK_KEYS=()

declare -a RUN_ORDER=()
declare -A RUN_PID=()
declare -A RUN_START=()
declare -A RUN_STATUS=()
declare -A RUN_DURATION=()
declare -A RUN_SKIPPED=()
INTERRUPTED=0
METADATA_READY=0

STATUS=0
declare -a FAILED_STEPS=()

repo_fingerprint() {
  local agda_version
  agda_version="$("$AGDA_BIN" --version 2>/dev/null | head -n 1 || true)"
  {
    echo "agda_bin=$AGDA_BIN"
    echo "agda_version=$agda_version"
    if git rev-parse --is-inside-work-tree >/dev/null 2>&1; then
      while IFS= read -r f; do
        [ -f "$f" ] || continue
        sha256sum "$f"
      done < <(
        {
          git ls-files -- '*.agda' '*.sh'
          git ls-files --others --exclude-standard -- '*.agda' '*.sh'
        } | sort -u
      )
    else
      find . -type f \( -name '*.agda' -o -name '*.sh' \) -print0 | sort -z | xargs -0 sha256sum
    fi
  } | sha256sum | awk '{print $1}'
}

GLOBAL_FP="$(repo_fingerprint)"
trap handle_interrupt INT TERM

load_metadata() {
  if [ "$CACHE_ENABLED" -ne 1 ] || [ ! -f "$METADATA_FILE" ]; then
    return
  fi
  local key label class fp rc dur ts
  while IFS=$'\t' read -r key label class fp rc dur ts; do
    [ -n "$key" ] || continue
    META_LABEL["$key"]="$label"
    META_CLASS["$key"]="$class"
    META_FP["$key"]="$fp"
    META_RC["$key"]="$rc"
    META_DUR["$key"]="$dur"
    META_TS["$key"]="$ts"
  done < "$METADATA_FILE"
}

save_metadata() {
  if [ "$CACHE_ENABLED" -ne 1 ] || [ "$METADATA_READY" -ne 1 ]; then
    return
  fi
  local tmp="${METADATA_FILE}.tmp"
  : > "$tmp"
  local key
  local row_count=0
  for key in "${TASK_KEYS[@]}"; do
    if [ -z "${TASK_LABEL[$key]+x}" ] || [ -z "${TASK_CLASS[$key]+x}" ]; then
      continue
    fi
    printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
      "$key" \
      "${TASK_LABEL[$key]}" \
      "${TASK_CLASS[$key]}" \
      "${META_FP[$key]:-$GLOBAL_FP}" \
      "${RUN_STATUS[$key]:-${META_RC[$key]:-999}}" \
      "${RUN_DURATION[$key]:-${META_DUR[$key]:-999999}}" \
      "${TS}" >> "$tmp"
    row_count=$(( row_count + 1 ))
  done
  if [ "$row_count" -eq 0 ]; then
    rm -f "$tmp"
    return
  fi
  sort -o "$tmp" "$tmp"
  mv "$tmp" "$METADATA_FILE"
}

flush_task_metadata() {
  local key="$1"
  if [ "$CACHE_ENABLED" -ne 1 ]; then
    return
  fi
  META_LABEL["$key"]="${TASK_LABEL[$key]}"
  META_CLASS["$key"]="${TASK_CLASS[$key]}"
  META_FP["$key"]="$GLOBAL_FP"
  META_RC["$key"]="${RUN_STATUS[$key]:-${META_RC[$key]:-999}}"
  META_DUR["$key"]="${RUN_DURATION[$key]:-${META_DUR[$key]:-999999}}"
  META_TS["$key"]="$TS"
  save_metadata
}

record_task_result() {
  local key="$1"
  local rc="$2"
  local start end dur

  start="${RUN_START[$key]:-0}"
  end="$(date +%s)"
  dur=$(( end - start ))
  [ "$dur" -ge 0 ] || dur=0

  RUN_STATUS["$key"]="$rc"
  RUN_DURATION["$key"]="$dur"
  META_LABEL["$key"]="${TASK_LABEL[$key]}"
  META_CLASS["$key"]="${TASK_CLASS[$key]}"
  META_FP["$key"]="$GLOBAL_FP"
  META_RC["$key"]="$rc"
  META_DUR["$key"]="$dur"
  META_TS["$key"]="$TS"
  flush_task_metadata "$key"
}

drain_finished_children() {
  local key pid rc
  for key in "${RUN_ORDER[@]}"; do
    if [ -n "${RUN_STATUS[$key]+x}" ]; then
      continue
    fi
    pid="${RUN_PID[$key]:-}"
    [ -n "$pid" ] || continue
    if kill -0 "$pid" 2>/dev/null; then
      continue
    fi
    if wait "$pid"; then
      rc=0
    else
      rc=$?
    fi
    record_task_result "$key" "$rc"
  done
}

handle_interrupt() {
  INTERRUPTED=1
  echo "[interrupt] draining completed tasks and flushing metadata"
  drain_finished_children
  save_metadata
  exit 130
}

learned_class_for() {
  local key="$1"
  local kind="${TASK_KIND[$key]}"
  local label="${TASK_LABEL[$key]}"
  local previous="${META_CLASS[$key]:-}"
  local dur="${META_DUR[$key]:-}"
  local agg

  if [ "$kind" = "audit" ]; then
    printf 'audit'
    return
  fi

  for agg in "${HEAVY_AGGREGATORS[@]}"; do
    if [ "$label" = "$agg" ]; then
      printf 'aggregator'
      return
    fi
  done

  if [ -n "$previous" ]; then
    printf '%s' "$previous"
    return
  fi

  if [[ "$dur" =~ ^[0-9]+$ ]]; then
    if [ "$dur" -ge 120 ]; then
      printf 'heavy'
    elif [ "$dur" -ge 20 ]; then
      printf 'medium'
    else
      printf 'fast'
    fi
    return
  fi

  printf 'fast'
}

should_stream_task() {
  local key="$1"
  local class="${TASK_CLASS[$key]}"
  if [ "$VERBOSE" -ge 2 ]; then
    return 0
  fi
  if [ "$VERBOSE" -eq 1 ] && { [ "$class" = "heavy" ] || [ "$class" = "aggregator" ]; }; then
    return 0
  fi
  return 1
}

register_task() {
  local key="$1"
  local kind="$2"
  local label="$3"
  local artifact="$4"
  local deps="$5"
  shift 5
  TASK_KEYS+=( "$key" )
  TASK_KIND["$key"]="$kind"
  TASK_LABEL["$key"]="$label"
  TASK_ARTIFACT["$key"]="$artifact"
  TASK_DEPS["$key"]="$deps"
  TASK_COMMAND["$key"]="$(printf '%q ' "$@")"
  TASK_COMMAND["$key"]="${TASK_COMMAND[$key]% }"
}

module_path_to_key() {
  printf 'module:%s' "$1"
}

audit_key() {
  printf 'audit:%s' "$1"
}

collect_modules() {
  rg --files -g '*.agda' | sort
}

import_to_path() {
  local import_name="$1"
  local path="${import_name//./\/}.agda"
  if [ -f "$path" ]; then
    printf '%s' "$path"
  fi
}

module_deps() {
  local path="$1"
  local dep
  rg -No '^(open import|import) +([A-Za-z0-9_.]+)' "$path" \
    | sed -E 's/^(open import|import) +//' \
    | awk '{print $1}' \
    | while IFS= read -r dep; do
        import_to_path "$dep"
      done \
    | sort -u
}

register_discovered_tasks() {
  local path key deps dep dep_keys artifact
  while IFS= read -r path; do
    key="$(module_path_to_key "$path")"
    deps=""
    while IFS= read -r dep; do
      [ -n "$dep" ] || continue
      dep_keys+=",module:$dep"
    done < <(module_deps "$path")
    deps="${dep_keys#,}"
    dep_keys=""
    artifact="$OUT_DIR/modules/${path//\//__}.log"
    mkdir -p "$(dirname "$artifact")"
    register_task "$key" "module" "$path" "$artifact" "$deps" "$AGDA_BIN" -i . "$path"
  done < <(collect_modules)

  register_task "$(audit_key canonical_path_audit)" "audit" "canonical_path_audit" "$OUT_DIR/03_canonical_path_audit.txt" "" bash -lc '
echo "# Canonical Path Audit"
echo
echo "## Canonical bridge imports (expected)"
rg -n "import DASHI\\.Physics\\.Closure\\.(ContractionForcesQuadraticTheorem|ContractionQuadraticToSignatureBridgeTheorem|QuadraticToCliffordBridgeTheorem|CanonicalContractionToCliffordBridgeTheorem|PhysicsUnification|CanonicalStageCTheoremBundle)" DASHI || true
echo
echo "## Potential alternate-route imports inside closure stack (review)"
rg -n "import DASHI\\.Geometry\\.(QuadraticEmergence|QuadraticFromNorm|QuadraticFromParallelogram|QuadraticFormEmergence)|import DASHI\\.Physics\\.ContractionQuadraticBridge" DASHI/Physics/Closure || true
'
  register_task "$(audit_key placeholder_postulate_audit)" "audit" "placeholder_postulate_audit" "$OUT_DIR/04_placeholder_postulate_audit.txt" "" bash -lc '
echo "# Placeholder/Postulate Audit"
echo
echo "## postulate declarations"
rg -n "^[[:space:]]*postulate\\b" DASHI || true
echo
echo "## placeholder markers"
rg -n "placeholder|to be discharged|TODO" DASHI || true
'
  register_task "$(audit_key closure_status_pointers)" "audit" "closure_status_pointers" "$OUT_DIR/05_closure_status_pointers.txt" "" bash -lc '
echo "# Closure Status Pointers"
rg -n "module DASHI\\.Physics\\.Closure\\.(PhysicsUnification|CanonicalContractionToCliffordBridgeTheorem|CanonicalStageCTheoremBundle|PhysicsClosureFullShift)" DASHI/Physics/Closure -S || true
'
}

seed_aggregator_dependencies() {
  local canonical_bundle="module:DASHI/Physics/Closure/CanonicalStageCTheoremBundle.agda"
  local everything="module:DASHI/Everything.agda"
  local summary="module:DASHI/Physics/Closure/PhysicsClosureValidationSummary.agda"

  if [ -n "${TASK_DEPS[$everything]+x}" ]; then
    TASK_DEPS["$everything"]="${TASK_DEPS[$everything]},$canonical_bundle"
    TASK_DEPS["$everything"]="${TASK_DEPS[$everything]#,}"
  fi

  if [ -n "${TASK_DEPS[$summary]+x}" ]; then
    TASK_DEPS["$summary"]="${TASK_DEPS[$summary]},$canonical_bundle"
    TASK_DEPS["$summary"]="${TASK_DEPS[$summary]#,}"
  fi
}

apply_classes() {
  local key
  for key in "${TASK_KEYS[@]}"; do
    TASK_CLASS["$key"]="$(learned_class_for "$key")"
  done
}

print_discovered_modules() {
  local key
  for key in "${TASK_KEYS[@]}"; do
    if ! should_select_task "$key"; then
      continue
    fi
    printf '%s\t%s\t%s\t%s\t%s\n' \
      "$key" \
      "${TASK_KIND[$key]}" \
      "${TASK_CLASS[$key]}" \
      "${META_DUR[$key]:-unknown}" \
      "${META_RC[$key]:-unknown}"
  done | sort
}

selected_by_alias_filters() {
  local key="$1"
  local sid alias_key

  if [ "$ONLY_FILTER_COUNT" -eq 0 ] && [ -z "$FROM_STAGE_ID" ]; then
    return 0
  fi

  for sid in "${STAGE_ORDER[@]}"; do
    alias_key="${ALIAS_TO_KEY[$sid]}"
    if [ "$alias_key" != "$key" ]; then
      continue
    fi
    if [ "$ONLY_FILTER_COUNT" -gt 0 ] && [ -n "${ONLY_STAGE_FILTER[$sid]+x}" ]; then
      return 0
    fi
    if [ -n "$FROM_STAGE_ID" ] && [ "$((10#$sid))" -ge "$((10#$FROM_STAGE_ID))" ]; then
      return 0
    fi
  done

  return 1
}

should_select_task() {
  local key="$1"
  local class="${TASK_CLASS[$key]}"

  if [ -n "$CLASS_FILTER" ] && [ "$class" != "$CLASS_FILTER" ]; then
    return 1
  fi

  if [ "$EXCLUDE_HEAVY" -eq 1 ] && { [ "$class" = "heavy" ] || [ "$class" = "aggregator" ]; }; then
    return 1
  fi

  if selected_by_alias_filters "$key"; then
    return 0
  fi

  if [ "$ONLY_FILTER_COUNT" -gt 0 ] || [ -n "$FROM_STAGE_ID" ]; then
    return 1
  fi

  return 0
}

run_with_timeout() {
  local timeout_secs="$1"
  shift
  if [ "$timeout_secs" -le 0 ]; then
    "$@"
    return $?
  fi
  "$@" &
  local cmd_pid=$!
  local start now
  start="$(date +%s)"
  while kill -0 "$cmd_pid" 2>/dev/null; do
    now="$(date +%s)"
    if [ $(( now - start )) -ge "$timeout_secs" ]; then
      kill -TERM "$cmd_pid" 2>/dev/null || true
      sleep 1
      kill -KILL "$cmd_pid" 2>/dev/null || true
      wait "$cmd_pid" 2>/dev/null || true
      return 124
    fi
    sleep 0.2
  done
  wait "$cmd_pid"
}

throttle_workers() {
  while [ "$(live_pid_count)" -ge "$MAX_WORKERS" ]; do
    sleep 0.1
  done
}

live_pid_count() {
  local key pid count=0
  for key in "${RUN_ORDER[@]}"; do
    if [ -n "${RUN_STATUS[$key]+x}" ]; then
      continue
    fi
    pid="${RUN_PID[$key]:-}"
    [ -n "$pid" ] || continue
    if kill -0 "$pid" 2>/dev/null; then
      count=$(( count + 1 ))
    fi
  done
  printf '%s' "$count"
}

queue_task() {
  local key="$1"
  local timeout_secs="$2"
  local artifact="${TASK_ARTIFACT[$key]}"
  local cmd="${TASK_COMMAND[$key]}"
  local label_prefix="${TASK_LABEL[$key]}"
  local sed_label
  local stream=0

  if [ -f "$artifact" ]; then
    echo >> "$artifact"
  fi
  echo "[timeout] $( [ "$timeout_secs" -gt 0 ] && printf '%ss' "$timeout_secs" || printf 'none' )" >> "$artifact"
  echo "[cmd] $cmd" >> "$artifact"
  echo "---" >> "$artifact"

  echo "[start] ${TASK_LABEL[$key]}"
  RUN_ORDER+=( "$key" )
  RUN_START["$key"]="$(date +%s)"

  if ! should_stream_task "$key"; then
    stream=1
  fi

  # Escape label for sed replacement context.
  sed_label="${label_prefix//\\/\\\\}"
  sed_label="${sed_label//&/\\&}"
  sed_label="${sed_label//|/\\|}"

  (
    if [ "$stream" -eq 1 ]; then
      run_with_timeout "$timeout_secs" bash -lc "$cmd" >> "$artifact" 2>&1
      exit $?
    else
      run_with_timeout "$timeout_secs" bash -lc "$cmd" 2>&1 | sed "s|^|[${sed_label}] |" | tee -a "$artifact"
      exit "${PIPESTATUS[0]}"
    fi
  ) &
  RUN_PID["$key"]=$!
}

mark_cached_skip() {
  local key="$1"
  local artifact="${TASK_ARTIFACT[$key]}"
  RUN_STATUS["$key"]=0
  RUN_SKIPPED["$key"]=1
  RUN_DURATION["$key"]="${META_DUR[$key]:-0}"
  echo "[skip] ${TASK_LABEL[$key]} (cached pass)"
  {
    echo "[cached] skip ${TASK_LABEL[$key]}"
    echo "[fingerprint] $GLOBAL_FP"
    echo "[source] $METADATA_FILE"
  } > "$artifact"
  flush_task_metadata "$key"
}

can_skip_cached() {
  local key="$1"
  if [ "$CACHE_ENABLED" -ne 1 ] || [ "$REFRESH_CACHE" -eq 1 ]; then
    return 1
  fi
  if [ "${META_FP[$key]:-}" = "$GLOBAL_FP" ] && [ "${META_RC[$key]:-}" = "0" ]; then
    return 0
  fi
  return 1
}

sort_keys_by_duration() {
  local key dur
  local -a rows=()
  for key in "$@"; do
    dur="${META_DUR[$key]:-999999}"
    [[ "$dur" =~ ^[0-9]+$ ]] || dur=999999
    rows+=( "$(printf '%09d\t%s' "$dur" "$key")" )
  done
  printf '%s\n' "${rows[@]}" | sort -n | awk -F'\t' '{print $2}'
}

selected_dep_unresolved() {
  local key="$1"
  local dep
  local deps="${TASK_DEPS[$key]}"
  [ -n "$deps" ] || return 1
  IFS=',' read -r -a arr <<< "$deps"
  for dep in "${arr[@]}"; do
    [ -n "$dep" ] || continue
    if [ -z "${SELECTED[$dep]+x}" ]; then
      continue
    fi
    if [ "${RUN_STATUS[$dep]:-999}" != "0" ]; then
      return 0
    fi
  done
  return 1
}

dep_waits_on_timeout() {
  local key="$1"
  local dep
  local deps="${TASK_DEPS[$key]}"
  [ -n "$deps" ] || return 1
  IFS=',' read -r -a arr <<< "$deps"
  for dep in "${arr[@]}"; do
    [ -n "$dep" ] || continue
    if [ -z "${SELECTED[$dep]+x}" ]; then
      continue
    fi
    if [ "${RUN_STATUS[$dep]:-999}" = "124" ]; then
      return 0
    fi
  done
  return 1
}

dep_failed_hard() {
  local key="$1"
  local dep
  local deps="${TASK_DEPS[$key]}"
  [ -n "$deps" ] || return 1
  IFS=',' read -r -a arr <<< "$deps"
  for dep in "${arr[@]}"; do
    [ -n "$dep" ] || continue
    if [ -z "${SELECTED[$dep]+x}" ]; then
      continue
    fi
    if [ -n "${RUN_STATUS[$dep]+x}" ] && [ "${RUN_STATUS[$dep]}" != "0" ] && [ "${RUN_STATUS[$dep]}" != "124" ]; then
      return 0
    fi
  done
  return 1
}

run_batch() {
  local timeout_secs="$1"
  shift
  local key rc
  RUN_ORDER=()
  for key in "$@"; do
    if [ "$INTERRUPTED" -eq 1 ]; then
      break
    fi
    if can_skip_cached "$key"; then
      mark_cached_skip "$key"
      continue
    fi
    throttle_workers
    queue_task "$key" "$timeout_secs"
  done

  for key in "${RUN_ORDER[@]}"; do
    if wait "${RUN_PID[$key]}"; then
      rc=0
      echo "[ok]  ${TASK_LABEL[$key]}"
    else
      rc=$?
      echo "[fail] ${TASK_LABEL[$key]} (exit $rc)"
    fi
    record_task_result "$key" "$rc"
  done
}

run_rung() {
  local timeout_secs="$1"
  shift
  local -a remaining=( "$@" )
  local key
  while [ "${#remaining[@]}" -gt 0 ]; do
    local -a ready=()
    local -a blocked=()
    for key in "${remaining[@]}"; do
      if dep_failed_hard "$key"; then
        RUN_STATUS["$key"]=125
        continue
      fi
      if selected_dep_unresolved "$key"; then
        blocked+=( "$key" )
      else
        ready+=( "$key" )
      fi
    done

    if [ "${#ready[@]}" -eq 0 ]; then
      break
    fi

    mapfile -t ready < <(sort_keys_by_duration "${ready[@]}")
    run_batch "$timeout_secs" "${ready[@]}"

    local -a next=()
    for key in "${blocked[@]}"; do
      if [ -z "${RUN_STATUS[$key]+x}" ]; then
        next+=( "$key" )
      fi
    done
    remaining=( "${next[@]}" )
  done
}

load_metadata
register_discovered_tasks
seed_aggregator_dependencies
apply_classes
METADATA_READY=1

if [ "$DISCOVER_ONLY" -eq 1 ]; then
  print_discovered_modules
  exit 0
fi

declare -A SELECTED=()
declare -a SELECTED_KEYS=()
key=""
for key in "${TASK_KEYS[@]}"; do
  if should_select_task "$key"; then
    SELECTED["$key"]=1
    SELECTED_KEYS+=( "$key" )
  fi
done

mapfile -t SELECTED_KEYS < <(sort_keys_by_duration "${SELECTED_KEYS[@]}")

if [ "${#TIMEOUT_LADDER[@]}" -gt 0 ]; then
  declare -a remaining=( "${SELECTED_KEYS[@]}" )
  local_round=0
  for rung in "${TIMEOUT_LADDER[@]}"; do
    [ "${#remaining[@]}" -gt 0 ] || break
    local_round=$(( local_round + 1 ))
    echo "[ladder] round $local_round timeout=${rung}s remaining=${#remaining[@]}"
    run_rung "$rung" "${remaining[@]}"
    declare -a next=()
    for key in "${remaining[@]}"; do
      if [ "${RUN_STATUS[$key]:-999}" = "124" ]; then
        next+=( "$key" )
      elif [ -z "${RUN_STATUS[$key]+x}" ] && dep_waits_on_timeout "$key"; then
        next+=( "$key" )
      elif [ -z "${RUN_STATUS[$key]+x}" ]; then
        RUN_STATUS["$key"]=125
      fi
    done
    remaining=( "${next[@]}" )
  done
  for key in "${remaining[@]}"; do
    if [ -z "${RUN_STATUS[$key]+x}" ]; then
      if dep_waits_on_timeout "$key"; then
        RUN_STATUS["$key"]=125
      else
        RUN_STATUS["$key"]=124
      fi
    fi
  done
else
  run_rung 0 "${SELECTED_KEYS[@]}"
fi

STATUS=0
FAILED_STEPS=()
for key in "${SELECTED_KEYS[@]}"; do
  if [ "${RUN_STATUS[$key]:-999}" != "0" ]; then
    STATUS=1
    FAILED_STEPS+=( "${TASK_LABEL[$key]}:${RUN_STATUS[$key]:-999}" )
  fi
done

save_metadata

count_class_selected() {
  local wanted="$1"
  local count=0
  local key
  for key in "${SELECTED_KEYS[@]}"; do
    if [ "${TASK_CLASS[$key]}" = "$wanted" ]; then
      count=$(( count + 1 ))
    fi
  done
  printf '%s' "$count"
}

cat > "$OUT_DIR/SUMMARY.txt" <<EOF_SUM
Closure hygiene run: $TS
Root: $ROOT_DIR
Agda binary: $AGDA_BIN
Max workers: $MAX_WORKERS
Verbose: $VERBOSE
Stage filter from: ${FROM_STAGE_ID:-none}
Stage filter only: ${ONLY_STAGE_IDS_CSV:-none}
Class filter: ${CLASS_FILTER:-none}
Include heavy: $((1 - EXCLUDE_HEAVY))
Cache enabled: $CACHE_ENABLED
Cache refresh: $REFRESH_CACHE
Metadata file: $METADATA_FILE
Cache ordering: shortest-known task first
Timeout ladder: ${TIMEOUT_LADDER_CSV:-none}

Selected tasks:
  - total: ${#SELECTED_KEYS[@]}
  - fast: $(count_class_selected fast)
  - medium: $(count_class_selected medium)
  - heavy: $(count_class_selected heavy)
  - aggregator: $(count_class_selected aggregator)
  - audit: $(count_class_selected audit)

Alias checks:
  - 01 CanonicalStageCTheoremBundle: ${RUN_STATUS[module:DASHI/Physics/Closure/CanonicalStageCTheoremBundle.agda]:-N/A}
  - 02 Everything.agda: ${RUN_STATUS[module:DASHI/Everything.agda]:-N/A}
  - 03 canonical_path_audit: ${RUN_STATUS[audit:canonical_path_audit]:-N/A}
  - 04 placeholder_postulate_audit: ${RUN_STATUS[audit:placeholder_postulate_audit]:-N/A}
  - 05 closure_status_pointers: ${RUN_STATUS[audit:closure_status_pointers]:-N/A}

Overall status: $(if [ "$STATUS" -eq 0 ]; then echo "PASS"; else echo "FAIL"; fi)
EOF_SUM

if [ "${#FAILED_STEPS[@]}" -gt 0 ]; then
  {
    echo
    echo "Failed steps:"
    for key in "${FAILED_STEPS[@]}"; do
      echo "  - $key"
    done
  } | tee -a "$OUT_DIR/SUMMARY.txt"
fi

if [ "$STATUS" -eq 0 ]; then
  echo "[done] PASS. Artifacts in $OUT_DIR"
else
  echo "[done] FAIL. Artifacts in $OUT_DIR"
fi

exit "$STATUS"
