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
CACHE_ENABLED=1
REFRESH_CACHE=0
CACHE_FILE=".cache/closure_hygiene_stage_cache.tsv"
TIMEOUT_LADDER_CSV=""
declare -a TIMEOUT_LADDER=()
ONLY_FILTER_COUNT=0
declare -A ONLY_STAGE_FILTER
ALL_STAGES=(
  "01_canonical_stagec_build"
  "02_everything_build"
  "03_canonical_path_audit"
  "04_placeholder_postulate_audit"
  "05_closure_status_pointers"
)
declare -A STAGE_DEPENDS=(
  ["02_everything_build"]="01_canonical_stagec_build"
)

usage() {
  cat <<'EOF'
Usage: bash scripts/run_closure_hygiene.sh [options] [OUT_DIR]

Options:
  -j, --jobs N      Max parallel workers (default: 3 or $MAX_WORKERS)
  --from ID         Run stages with numeric ID >= ID (e.g. 03)
  --only IDS        Run only selected IDs, comma-separated (e.g. 01,03,05)
  --list-stages     Print available stage IDs and names, then exit
  --timeout-ladder S
                  Timeout sweep in seconds, comma-separated (e.g. 1,2,5,10,30)
  --no-cache        Disable stage pass-cache lookup/update
  --refresh-cache   Ignore cached passes for this run, but update cache
  --cache-file P    Cache file path (default: .cache/closure_hygiene_stage_cache.tsv)
  -v, --verbose     Stream build-step output to terminal (default)
  -V, --very-verbose
                  Stream all step output to terminal
  -q, --quiet       Only print step headers and final status
  -h, --help        Show this help
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
  local name id
  for name in "${ALL_STAGES[@]}"; do
    id="${name%%_*}"
    echo "$id  $name"
  done
}

stage_exists() {
  local sid="$1"
  local name
  for name in "${ALL_STAGES[@]}"; do
    if [ "${name%%_*}" = "$sid" ]; then
      return 0
    fi
  done
  return 1
}

load_only_filter() {
  local csv="$1"
  local item sid
  IFS=',' read -r -a items <<< "$csv"
  for item in "${items[@]}"; do
    sid="$(normalize_stage_id "$item")"
    if ! stage_exists "$sid"; then
      echo "[error] unknown stage ID in --only: $sid" >&2
      echo "Available stages:" >&2
      list_stages >&2
      exit 2
    fi
    ONLY_STAGE_FILTER["$sid"]=1
  done
  ONLY_FILTER_COUNT="${#ONLY_STAGE_FILTER[@]}"
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

should_run_stage() {
  local name="$1"
  local sid="${name%%_*}"

  if [ "$ONLY_FILTER_COUNT" -gt 0 ] && [ -z "${ONLY_STAGE_FILTER[$sid]+x}" ]; then
    return 1
  fi

  if [ -n "$FROM_STAGE_ID" ] && [ "$((10#$sid))" -lt "$((10#$FROM_STAGE_ID))" ]; then
    return 1
  fi

  return 0
}

while [ "$#" -gt 0 ]; do
  case "$1" in
    -j|--jobs)
      shift
      if [ "$#" -eq 0 ]; then
        echo "[error] missing value for --jobs" >&2
        exit 2
      fi
      MAX_WORKERS="$1"
      ;;
    --from)
      shift
      if [ "$#" -eq 0 ]; then
        echo "[error] missing value for --from" >&2
        exit 2
      fi
      FROM_STAGE_ID="$(normalize_stage_id "$1")"
      ;;
    --only)
      shift
      if [ "$#" -eq 0 ]; then
        echo "[error] missing value for --only" >&2
        exit 2
      fi
      ONLY_STAGE_IDS_CSV="$1"
      ;;
    --list-stages)
      LIST_STAGES=1
      ;;
    --timeout-ladder)
      shift
      if [ "$#" -eq 0 ]; then
        echo "[error] missing value for --timeout-ladder" >&2
        exit 2
      fi
      TIMEOUT_LADDER_CSV="$1"
      ;;
    --no-cache)
      CACHE_ENABLED=0
      ;;
    --refresh-cache)
      REFRESH_CACHE=1
      ;;
    --cache-file)
      shift
      if [ "$#" -eq 0 ]; then
        echo "[error] missing value for --cache-file" >&2
        exit 2
      fi
      CACHE_FILE="$1"
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

if [ -n "$FROM_STAGE_ID" ] && ! stage_exists "$FROM_STAGE_ID"; then
  echo "[error] unknown --from stage ID: $FROM_STAGE_ID" >&2
  echo "Available stages:" >&2
  list_stages >&2
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
  mkdir -p "$(dirname "$CACHE_FILE")"
fi

STATUS=0
declare -a STEP_ORDER=()
declare -a FAILED_STEPS=()
declare -A STEP_PID
declare -A STEP_ARTIFACT
declare -A STEP_STATUS
declare -A STEP_COMMAND
declare -A STEP_SKIPPED
declare -A STEP_FINGERPRINT
declare -A STEP_STARTED_AT=()
declare -A STEP_DURATION_SECS=()
declare -A FINAL_STATUS=()
declare -A FINAL_SKIPPED=()
declare -A SELECTED_STAGE=()
declare -A CACHE_FP=()
declare -A CACHE_RC=()
declare -A CACHE_TS=()
declare -A CACHE_DUR=()

cmd_string() {
  local out=""
  local arg
  for arg in "$@"; do
    out+=$(printf '%q ' "$arg")
  done
  printf '%s' "${out% }"
}

throttle_workers() {
  while [ "$(jobs -rp | wc -l | tr -d ' ')" -ge "$MAX_WORKERS" ]; do
    sleep 0.1
  done
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
  return $?
}

load_cache() {
  if [ "$CACHE_ENABLED" -ne 1 ] || [ ! -f "$CACHE_FILE" ]; then
    return
  fi
  local stage fp rc ts dur
  while IFS=$'\t' read -r stage fp rc ts dur; do
    [ -n "$stage" ] || continue
    CACHE_FP["$stage"]="$fp"
    CACHE_RC["$stage"]="$rc"
    CACHE_TS["$stage"]="$ts"
    CACHE_DUR["$stage"]="${dur:-999999}"
  done < "$CACHE_FILE"
}

save_cache() {
  if [ "$CACHE_ENABLED" -ne 1 ]; then
    return
  fi
  local tmp="${CACHE_FILE}.tmp"
  : > "$tmp"
  local stage
  for stage in "${!CACHE_FP[@]}"; do
    printf '%s\t%s\t%s\t%s\t%s\n' \
      "$stage" "${CACHE_FP[$stage]}" "${CACHE_RC[$stage]:-1}" "${CACHE_TS[$stage]:-}" "${CACHE_DUR[$stage]:-999999}" >> "$tmp"
  done
  sort -o "$tmp" "$tmp"
  mv "$tmp" "$CACHE_FILE"
}

stage_fingerprint() {
  local name="$1"
  local cmd_string_value="$2"
  local agda_version
  agda_version="$("$AGDA_BIN" --version 2>/dev/null | head -n 1 || true)"

  {
    echo "stage=$name"
    echo "cmd=$cmd_string_value"
    echo "agda_bin=$AGDA_BIN"
    echo "agda_version=$agda_version"
    if git rev-parse --is-inside-work-tree >/dev/null 2>&1; then
      local f
      while IFS= read -r f; do
        [ -f "$f" ] || continue
        sha256sum "$f"
      done < <(
        {
          git ls-files -- DASHI scripts/run_closure_hygiene.sh
          git ls-files --others --exclude-standard -- DASHI scripts/run_closure_hygiene.sh
        } | sort -u
      )
    else
      find DASHI scripts -type f \( -name '*.agda' -o -name '*.md' -o -name '*.sh' \) -print0 \
        | sort -z \
        | xargs -0 sha256sum
    fi
  } | sha256sum | awk '{print $1}'
}

queue_step() {
  local name="$1"
  shift
  local artifact="$1"
  shift
  local timeout_secs="$1"
  shift
  local cmd=( "$@" )
  local stream_now=0

  if [ "$VERBOSE" -ge 2 ]; then
    stream_now=1
  elif [ "$VERBOSE" -eq 1 ] && [[ "$name" =~ ^0[12]_ ]]; then
    stream_now=1
  fi

  throttle_workers
  STEP_ARTIFACT["$name"]="$artifact"
  STEP_COMMAND["$name"]="$(cmd_string "${cmd[@]}")"

  echo "[queue] $name"
  if [ -f "$artifact" ]; then
    echo >> "$artifact"
  fi
  if [ "$timeout_secs" -gt 0 ]; then
    echo "[timeout] ${timeout_secs}s" >> "$artifact"
  else
    echo "[timeout] none" >> "$artifact"
  fi
  echo "[cmd] ${STEP_COMMAND[$name]}" >> "$artifact"
  echo "---" >> "$artifact"
  STEP_STARTED_AT["$name"]="$(date +%s)"

  (
    if [ "$stream_now" -eq 1 ]; then
      run_with_timeout "$timeout_secs" "${cmd[@]}" 2>&1 | sed "s/^/[$name] /" | tee -a "$artifact"
      exit "${PIPESTATUS[0]}"
    else
      run_with_timeout "$timeout_secs" "${cmd[@]}" >> "$artifact" 2>&1
      exit $?
    fi
  ) &
  STEP_PID["$name"]=$!
}

schedule_step() {
  local name="$1"
  shift
  local artifact="$1"
  shift
  local timeout_secs="$1"
  shift
  local cmd=( "$@" )
  local fp cached_rc cached_fp

  STEP_ORDER+=( "$name" )
  STEP_ARTIFACT["$name"]="$artifact"
  STEP_COMMAND["$name"]="$(cmd_string "${cmd[@]}")"
  fp="$(stage_fingerprint "$name" "${STEP_COMMAND[$name]}")"
  STEP_FINGERPRINT["$name"]="$fp"

  if [ "$CACHE_ENABLED" -eq 1 ] && [ "$REFRESH_CACHE" -eq 0 ]; then
    cached_fp="${CACHE_FP[$name]:-}"
    cached_rc="${CACHE_RC[$name]:-}"
    if [ -n "$cached_fp" ] && [ "$cached_fp" = "$fp" ] && [ "$cached_rc" = "0" ]; then
      STEP_STATUS["$name"]=0
      STEP_SKIPPED["$name"]=1
      echo "[skip] $name (cached pass)"
      {
        echo "[cached] skip $name"
        echo "[fingerprint] $fp"
        echo "[source] $CACHE_FILE"
      } > "$artifact"
      return
    fi
  fi

  queue_step "$name" "$artifact" "$timeout_secs" "${cmd[@]}"
}

step_03_canonical_path_audit() {
  echo "# Canonical Path Audit"
  echo
  echo "## Canonical bridge imports (expected)"
  rg -n "import DASHI\\.Physics\\.Closure\\.(ContractionForcesQuadraticTheorem|ContractionQuadraticToSignatureBridgeTheorem|QuadraticToCliffordBridgeTheorem|CanonicalContractionToCliffordBridgeTheorem|PhysicsUnification|CanonicalStageCTheoremBundle)" DASHI || true
  echo
  echo "## Potential alternate-route imports inside closure stack (review)"
  rg -n "import DASHI\\.Geometry\\.(QuadraticEmergence|QuadraticFromNorm|QuadraticFromParallelogram|QuadraticFormEmergence)|import DASHI\\.Physics\\.ContractionQuadraticBridge" DASHI/Physics/Closure || true
}

step_04_placeholder_postulate_audit() {
  echo "# Placeholder/Postulate Audit"
  echo
  echo "## postulate declarations"
  rg -n "^[[:space:]]*postulate\\b" DASHI || true
  echo
  echo "## placeholder markers"
  rg -n "placeholder|to be discharged|TODO" DASHI || true
}

step_05_closure_status_pointers() {
  echo "# Closure Status Pointers"
  rg -n "module DASHI\\.Physics\\.Closure\\.(PhysicsUnification|CanonicalContractionToCliffordBridgeTheorem|CanonicalStageCTheoremBundle|PhysicsClosureFullShift)" DASHI/Physics/Closure -S || true
}

collect_results() {
  local name pid rc started finished dur
  for name in "${STEP_ORDER[@]}"; do
    if [ -n "${STEP_SKIPPED[$name]+x}" ]; then
      FINAL_STATUS["$name"]=0
      FINAL_SKIPPED["$name"]=1
      continue
    fi
    pid="${STEP_PID[$name]}"
    if wait "$pid"; then
      rc=0
      echo "[ok]  $name"
    else
      rc=$?
      echo "[fail] $name (exit $rc)"
      FAILED_STEPS+=( "$name:$rc" )
    fi
    STEP_STATUS["$name"]="$rc"
    FINAL_STATUS["$name"]="$rc"
    FINAL_SKIPPED["$name"]=0
    started="${STEP_STARTED_AT[$name]:-0}"
    finished="$(date +%s)"
    dur=$(( finished - started ))
    if [ "$dur" -lt 0 ]; then dur=0; fi
    STEP_DURATION_SECS["$name"]="$dur"
    if [ "$CACHE_ENABLED" -eq 1 ]; then
      CACHE_FP["$name"]="${STEP_FINGERPRINT[$name]:-}"
      CACHE_RC["$name"]="$rc"
      CACHE_TS["$name"]="$TS"
      CACHE_DUR["$name"]="$dur"
    fi
  done
}

step_status_text() {
  local name="$1"
  if [ -n "${FINAL_SKIPPED[$name]+x}" ] && [ "${FINAL_SKIPPED[$name]}" -eq 1 ]; then
    printf 'SKIP (cached PASS)'
    return
  fi
  if [ -z "${FINAL_STATUS[$name]+x}" ]; then
    printf 'N/A'
    return
  fi
  local rc="${FINAL_STATUS[$name]}"
  if [ "$rc" -eq 0 ]; then
    printf 'PASS'
  elif [ "$rc" -eq 124 ]; then
    printf 'TIMEOUT (exit 124)'
  elif [ "$rc" -eq 125 ]; then
    printf 'BLOCKED (dependency unmet)'
  else
    printf 'FAIL (exit %s)' "$rc"
  fi
}

is_stage_blocked_by_dependency() {
  local stage_name="$1"
  local dep="${STAGE_DEPENDS[$stage_name]:-}"
  if [ -z "$dep" ]; then
    return 1
  fi
  if [ -z "${SELECTED_STAGE[$dep]+x}" ]; then
    return 1
  fi
  if [ "${FINAL_STATUS[$dep]:-999}" -ne 0 ]; then
    return 0
  fi
  return 1
}

sorted_selected_stages() {
  local name sid est
  local -a selected=()
  local -a lines=()
  for name in "${ALL_STAGES[@]}"; do
    if should_run_stage "$name"; then
      selected+=( "$name" )
    fi
  done
  if [ "${#selected[@]}" -eq 0 ]; then
    return 0
  fi
  for name in "${selected[@]}"; do
    est="${CACHE_DUR[$name]:-999999}"
    if ! [[ "$est" =~ ^[0-9]+$ ]]; then
      est=999999
    fi
    lines+=( "$(printf '%09d %s' "$est" "$name")" )
  done
  IFS=$'\n' read -r -d '' -a lines < <(printf '%s\n' "${lines[@]}" | sort -n && printf '\0')
  for name in "${lines[@]}"; do
    echo "${name#* }"
  done
}

queue_stage_by_name() {
  local name="$1"
  local timeout_secs="${2:-0}"
  case "$name" in
    01_canonical_stagec_build)
      schedule_step "$name" "$OUT_DIR/01_canonical_stagec_build.log" "$timeout_secs" \
        "$AGDA_BIN" -i . DASHI/Physics/Closure/CanonicalStageCTheoremBundle.agda
      ;;
    02_everything_build)
      schedule_step "$name" "$OUT_DIR/02_everything_build.log" "$timeout_secs" \
        "$AGDA_BIN" -i . DASHI/Everything.agda
      ;;
    03_canonical_path_audit)
      schedule_step "$name" "$OUT_DIR/03_canonical_path_audit.txt" "$timeout_secs" \
        step_03_canonical_path_audit
      ;;
    04_placeholder_postulate_audit)
      schedule_step "$name" "$OUT_DIR/04_placeholder_postulate_audit.txt" "$timeout_secs" \
        step_04_placeholder_postulate_audit
      ;;
    05_closure_status_pointers)
      schedule_step "$name" "$OUT_DIR/05_closure_status_pointers.txt" "$timeout_secs" \
        step_05_closure_status_pointers
      ;;
    *)
      echo "[error] unknown stage name: $name" >&2
      STATUS=1
      ;;
  esac
}

run_stage_set() {
  local timeout_secs="$1"
  shift
  local stage_name
  STEP_ORDER=()
  FAILED_STEPS=()
  STEP_PID=()
  STEP_STATUS=()
  STEP_SKIPPED=()
  STEP_FINGERPRINT=()
  STEP_STARTED_AT=()
  STEP_DURATION_SECS=()

  for stage_name in "$@"; do
    queue_stage_by_name "$stage_name" "$timeout_secs"
  done
  collect_results
}

# Queue selected tasks in runtime-aware order (shortest-known first).
load_cache
declare -a SELECTED_STAGES=()
while IFS= read -r stage_name; do
  [ -n "$stage_name" ] || continue
  SELECTED_STAGES+=( "$stage_name" )
  SELECTED_STAGE["$stage_name"]=1
done < <(sorted_selected_stages)

if [ "${#TIMEOUT_LADDER[@]}" -gt 0 ]; then
  declare -a REMAINING_STAGES=("${SELECTED_STAGES[@]}")
  local_round=0
  for rung in "${TIMEOUT_LADDER[@]}"; do
    if [ "${#REMAINING_STAGES[@]}" -eq 0 ]; then
      break
    fi
    declare -a RUN_THIS_ROUND=()
    declare -a BLOCKED_THIS_ROUND=()
    for stage_name in "${REMAINING_STAGES[@]}"; do
      if is_stage_blocked_by_dependency "$stage_name"; then
        BLOCKED_THIS_ROUND+=( "$stage_name" )
      else
        RUN_THIS_ROUND+=( "$stage_name" )
      fi
    done

    if [ "${#RUN_THIS_ROUND[@]}" -eq 0 ]; then
      local_round=$((local_round + 1))
      echo "[ladder] round $local_round timeout=${rung}s runnable=0 blocked=${#BLOCKED_THIS_ROUND[@]}"
      break
    fi

    local_round=$((local_round + 1))
    echo "[ladder] round $local_round timeout=${rung}s runnable=${#RUN_THIS_ROUND[@]} blocked=${#BLOCKED_THIS_ROUND[@]}"
    run_stage_set "$rung" "${RUN_THIS_ROUND[@]}"
    declare -a NEXT_REMAINING=()
    for stage_name in "${RUN_THIS_ROUND[@]}"; do
      if [ "${FINAL_STATUS[$stage_name]:-999}" -eq 124 ]; then
        NEXT_REMAINING+=( "$stage_name" )
      fi
    done
    NEXT_REMAINING+=( "${BLOCKED_THIS_ROUND[@]}" )
    REMAINING_STAGES=("${NEXT_REMAINING[@]}")
  done

  if [ "${#REMAINING_STAGES[@]}" -gt 0 ]; then
    for stage_name in "${REMAINING_STAGES[@]}"; do
      if [ -z "${FINAL_STATUS[$stage_name]+x}" ]; then
        FINAL_STATUS["$stage_name"]=125
      fi
    done
  fi
else
  run_stage_set 0 "${SELECTED_STAGES[@]}"
fi

save_cache

STATUS=0
FAILED_STEPS=()
for stage_name in "${SELECTED_STAGES[@]}"; do
  rc="${FINAL_STATUS[$stage_name]:-999}"
  if [ "$rc" -ne 0 ]; then
    STATUS=1
    FAILED_STEPS+=( "$stage_name:$rc" )
  fi
done

cat > "$OUT_DIR/SUMMARY.txt" <<EOF_SUM
Closure hygiene run: $TS
Root: $ROOT_DIR
Agda binary: $AGDA_BIN
Max workers: $MAX_WORKERS
Verbose: $VERBOSE
Stage filter from: ${FROM_STAGE_ID:-none}
Stage filter only: ${ONLY_STAGE_IDS_CSV:-none}
Cache enabled: $CACHE_ENABLED
Cache refresh: $REFRESH_CACHE
Cache file: $CACHE_FILE
Cache ordering: shortest-known stage first
Timeout ladder: ${TIMEOUT_LADDER_CSV:-none}

Build checks:
  - CanonicalStageCTheoremBundle: $(step_status_text 01_canonical_stagec_build)
  - Everything.agda: $(step_status_text 02_everything_build)

Audit checks:
  - canonical_path_audit: $(step_status_text 03_canonical_path_audit)
  - placeholder_postulate_audit: $(step_status_text 04_placeholder_postulate_audit)
  - closure_status_pointers: $(step_status_text 05_closure_status_pointers)

Artifacts:
  - $OUT_DIR/01_canonical_stagec_build.log
  - $OUT_DIR/02_everything_build.log
  - $OUT_DIR/03_canonical_path_audit.txt
  - $OUT_DIR/04_placeholder_postulate_audit.txt
  - $OUT_DIR/05_closure_status_pointers.txt

Overall status: $(if [ "$STATUS" -eq 0 ]; then echo "PASS"; else echo "FAIL"; fi)
EOF_SUM

if [ "${#FAILED_STEPS[@]}" -gt 0 ]; then
  {
    echo
    echo "Failed steps:"
    for entry in "${FAILED_STEPS[@]}"; do
      echo "  - $entry"
    done
  } | tee -a "$OUT_DIR/SUMMARY.txt"
fi

if [ "$STATUS" -eq 0 ]; then
  echo "[done] PASS. Artifacts in $OUT_DIR"
else
  echo "[done] FAIL. Artifacts in $OUT_DIR"
fi

exit "$STATUS"
