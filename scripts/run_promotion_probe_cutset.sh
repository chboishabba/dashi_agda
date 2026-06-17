#!/usr/bin/env bash

set -u

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
DEFAULT_TIMEOUT=120
LOG_ROOT="$REPO_ROOT/logs/agda-promotion-probe-cutset"
resolve_agda_bin() {
  if [ -n "${AGDA_BIN:-}" ]; then
    printf '%s\n' "${AGDA_BIN}"
    return 0
  fi

  local candidate_store candidate_bin
  candidate_store="$(nix build --no-link --print-out-paths /home/c/Documents/code/agda#debug.bin 2>/dev/null)"
  candidate_bin="${candidate_store}/bin/agda"
  if [ -n "$candidate_store" ] && [ -x "$candidate_bin" ]; then
    printf '%s\n' "$candidate_bin"
    return 0
  fi

  if command -v agda >/dev/null 2>&1; then
    command -v agda
    return 0
  fi

  echo agda
}

AGDA_BIN="$(resolve_agda_bin)"

EVERYTHING_TARGET="DASHI/Everything.agda"
PROBE_TARGETS=(
  "DASHI/Physics/Probes/NSPromotionProbe.agda"
  "DASHI/Physics/Probes/YMPromotionProbe.agda"
  "DASHI/Physics/Probes/UnificationPromotionProbe.agda"
  "DASHI/Physics/Probes/CurrentProofProfilePromotionProbe.agda"
)

usage() {
  cat <<'EOF'
Usage: scripts/run_promotion_probe_cutset.sh [options]

Runs the aggregate repo check plus the promotion probe cutset:
  DASHI/Everything.agda
  DASHI/Physics/Probes/NSPromotionProbe.agda
  DASHI/Physics/Probes/YMPromotionProbe.agda
  DASHI/Physics/Probes/UnificationPromotionProbe.agda
  DASHI/Physics/Probes/CurrentProofProfilePromotionProbe.agda

Options:
  --timeout SECONDS   Per-file timeout in seconds. Default: 120
  --log-dir PATH      Root directory for per-run logs.
  --list              Print targets and exit.
  --help              Show this help.

Exit codes:
  0  All targets passed.
  1  One or more targets failed.
  2  Bad arguments.
  3  One or more targets timed out, but none failed.
EOF
}

die() {
  echo "error: $*" >&2
  exit 2
}

require_cmd() {
  command -v "$1" >/dev/null 2>&1 || die "missing required command: $1"
}

sanitize_path() {
  printf '%s' "$1" | tr '/ ' '__'
}

all_targets() {
  printf '%s\n' "$EVERYTHING_TARGET"
  printf '%s\n' "${PROBE_TARGETS[@]}"
}

run_target() {
  local target="$1"
  local timeout_s="$2"
  local log_dir="$3"

  local safe_name log_file status
  safe_name="$(sanitize_path "$target")"
  log_file="$log_dir/${safe_name}.log"

  mkdir -p "$log_dir"

  {
    echo "== $target =="
    echo "command: timeout ${timeout_s}s ${AGDA_BIN} -i . -i DCHoTT-Agda -i cubical -l standard-library $target"
    echo "started: $(date -Iseconds)"
    echo
  } >"$log_file"

  (
    cd "$REPO_ROOT" || exit 99
    timeout "${timeout_s}s" "$AGDA_BIN" -i . -i DCHoTT-Agda -i cubical -l standard-library "$target"
  ) >>"$log_file" 2>&1
  status=$?

  {
    echo
    echo "exit_code: $status"
    echo "finished: $(date -Iseconds)"
  } >>"$log_file"

  if [[ $status -eq 0 ]]; then
    printf 'PASS\t%s\t%s\n' "$target" "$log_file"
  elif [[ $status -eq 124 ]]; then
    printf 'TIMEOUT\t%s\t%s\n' "$target" "$log_file"
  else
    printf 'FAIL\t%s\t%s\n' "$target" "$log_file"
  fi
}

TIMEOUT_S="$DEFAULT_TIMEOUT"
LIST_ONLY=0

while [[ $# -gt 0 ]]; do
  case "$1" in
    --timeout)
      [[ $# -ge 2 ]] || die "--timeout requires a value"
      TIMEOUT_S="$2"
      shift 2
      ;;
    --log-dir)
      [[ $# -ge 2 ]] || die "--log-dir requires a value"
      LOG_ROOT="$2"
      shift 2
      ;;
    --list)
      LIST_ONLY=1
      shift
      ;;
    --help|-h)
      usage
      exit 0
      ;;
    *)
      die "unknown argument: $1"
      ;;
  esac
done

require_cmd "$AGDA_BIN"
require_cmd timeout

[[ "$TIMEOUT_S" =~ ^[0-9]+$ ]] || die "--timeout must be an integer"
(( TIMEOUT_S > 0 )) || die "--timeout must be positive"

mapfile -t TARGETS < <(all_targets)
(( ${#TARGETS[@]} > 0 )) || die "no targets configured"

if (( LIST_ONLY )); then
  printf '%s\n' "${TARGETS[@]}"
  exit 0
fi

if [[ -z "$LOG_ROOT" ]]; then
  die "log root is empty"
fi

RUN_STAMP="$(date +%Y%m%dT%H%M%S)"
LOG_DIR="$LOG_ROOT/$RUN_STAMP"
SUMMARY_FILE="$LOG_DIR/summary.tsv"
mkdir -p "$LOG_DIR"

echo "repo_root: $REPO_ROOT"
echo "targets: ${#TARGETS[@]}"
echo "timeout_seconds: $TIMEOUT_S"
echo "log_dir: $LOG_DIR"
echo

pass_count=0
timeout_count=0
fail_count=0

for target in "${TARGETS[@]}"; do
  result="$(run_target "$target" "$TIMEOUT_S" "$LOG_DIR")"
  printf '%s\n' "$result"
  printf '%s\n' "$result" >>"$SUMMARY_FILE"
  case "${result%%$'\t'*}" in
    PASS) ((pass_count += 1)) ;;
    TIMEOUT) ((timeout_count += 1)) ;;
    FAIL) ((fail_count += 1)) ;;
  esac
done

echo
echo "summary:"
echo "  pass: $pass_count"
echo "  timeout: $timeout_count"
echo "  fail: $fail_count"

if (( fail_count > 0 )); then
  exit 1
fi

if (( timeout_count > 0 )); then
  exit 3
fi

exit 0
