#!/usr/bin/env bash

set -u

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
MANIFEST="$REPO_ROOT/Docs/support/reference/AgdaValidationTargets.md"
SECTION_HEADER="## Current YM H3a/H3b Propagation Targets"
DEFAULT_TIMEOUT=120
DEFAULT_JOBS=1
LOG_ROOT="$REPO_ROOT/logs/agda-ym-h3a"
EVERYTHING_TARGET="DASHI/Everything.agda"

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

usage() {
  cat <<'EOF'
Usage: scripts/run_ym_h3a_validation.sh [options]

Runs the current YM H3a/H3b Agda validation targets listed in:
  Docs/support/reference/AgdaValidationTargets.md

Options:
  --timeout SECONDS   Per-file timeout in seconds. Default: 120
  --jobs N            Parallel jobs. Default: 1
  --log-dir PATH      Root directory for per-run logs.
  --everything        Run only DASHI/Everything.agda.
  --with-everything   Append DASHI/Everything.agda after the manifest targets.
  --list              Print targets and exit.
  --fail-fast         Stop on the first hard Agda failure.
  --help              Show this help.

Exit codes:
  0  All targets passed.
  1  One or more targets failed.
  2  Bad arguments or manifest parse failure.
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

extract_targets() {
  awk -v section="$SECTION_HEADER" '
    $0 == section { in_section = 1; next }
    in_section && /^## / { exit }
    in_section {
      if (match($0, /`DASHI\/[^`]+\.agda`/)) {
        path = substr($0, RSTART + 1, RLENGTH - 2)
        print path
      }
    }
  ' "$MANIFEST"
}

sanitize_path() {
  printf '%s' "$1" | tr '/ ' '__'
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

run_with_xargs() {
  local jobs="$1"
  local timeout_s="$2"
  local log_dir="$3"
  shift 3
  local -a targets=("$@")

  printf '%s\n' "${targets[@]}" \
    | xargs -I{} -P "$jobs" bash -lc '
        target="$1"
        timeout_s="$2"
        log_dir="$3"
        script="$4"
        "$script" --internal-run "$target" "$timeout_s" "$log_dir"
      ' _ "{}" "$timeout_s" "$log_dir" "$0"
}

TIMEOUT_S="$DEFAULT_TIMEOUT"
JOBS="$DEFAULT_JOBS"
LOG_DIR=""
LIST_ONLY=0
FAIL_FAST=0
EVERYTHING_ONLY=0
WITH_EVERYTHING=0

while [[ $# -gt 0 ]]; do
  case "$1" in
    --timeout)
      [[ $# -ge 2 ]] || die "--timeout requires a value"
      TIMEOUT_S="$2"
      shift 2
      ;;
    --jobs)
      [[ $# -ge 2 ]] || die "--jobs requires a value"
      JOBS="$2"
      shift 2
      ;;
    --log-dir)
      [[ $# -ge 2 ]] || die "--log-dir requires a value"
      LOG_ROOT="$2"
      shift 2
      ;;
    --everything)
      EVERYTHING_ONLY=1
      shift
      ;;
    --with-everything)
      WITH_EVERYTHING=1
      shift
      ;;
    --list)
      LIST_ONLY=1
      shift
      ;;
    --fail-fast)
      FAIL_FAST=1
      shift
      ;;
    --internal-run)
      [[ $# -eq 4 ]] || die "--internal-run expects TARGET TIMEOUT LOG_DIR"
      run_target "$2" "$3" "$4"
      exit 0
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
require_cmd awk
require_cmd xargs

[[ -f "$MANIFEST" ]] || die "manifest not found: $MANIFEST"
[[ "$TIMEOUT_S" =~ ^[0-9]+$ ]] || die "--timeout must be an integer"
[[ "$JOBS" =~ ^[0-9]+$ ]] || die "--jobs must be an integer"
(( TIMEOUT_S > 0 )) || die "--timeout must be positive"
(( JOBS > 0 )) || die "--jobs must be positive"

mapfile -t TARGETS < <(extract_targets)
(( ${#TARGETS[@]} > 0 )) || die "no targets found under section: $SECTION_HEADER"

if (( EVERYTHING_ONLY == 1 && WITH_EVERYTHING == 1 )); then
  die "--everything and --with-everything are mutually exclusive"
fi

if (( EVERYTHING_ONLY )); then
  TARGETS=("$EVERYTHING_TARGET")
elif (( WITH_EVERYTHING )); then
  TARGETS+=("$EVERYTHING_TARGET")
fi

if (( LIST_ONLY )); then
  printf '%s\n' "${TARGETS[@]}"
  exit 0
fi

if [[ -z "$LOG_DIR" ]]; then
  RUN_STAMP="$(date +%Y%m%dT%H%M%S)"
  LOG_DIR="$LOG_ROOT/$RUN_STAMP"
fi

mkdir -p "$LOG_DIR"

echo "repo_root: $REPO_ROOT"
echo "manifest: $MANIFEST"
echo "targets: ${#TARGETS[@]}"
echo "timeout_seconds: $TIMEOUT_S"
echo "jobs: $JOBS"
echo "log_dir: $LOG_DIR"
echo

pass_count=0
timeout_count=0
fail_count=0

if (( JOBS == 1 || FAIL_FAST == 1 )); then
  for target in "${TARGETS[@]}"; do
    result="$(run_target "$target" "$TIMEOUT_S" "$LOG_DIR")"
    printf '%s\n' "$result"
    case "${result%%$'\t'*}" in
      PASS) ((pass_count += 1)) ;;
      TIMEOUT) ((timeout_count += 1)) ;;
      FAIL)
        ((fail_count += 1))
        if (( FAIL_FAST )); then
          break
        fi
        ;;
    esac
  done
else
  while IFS=$'\t' read -r status _target _log; do
    [[ -n "$status" ]] || continue
    case "$status" in
      PASS) ((pass_count += 1)) ;;
      TIMEOUT) ((timeout_count += 1)) ;;
      FAIL) ((fail_count += 1)) ;;
    esac
    printf '%s\t%s\t%s\n' "$status" "$_target" "$_log"
  done < <(run_with_xargs "$JOBS" "$TIMEOUT_S" "$LOG_DIR" "${TARGETS[@]}")
fi

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
