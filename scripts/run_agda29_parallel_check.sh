#!/usr/bin/env bash
set -euo pipefail
JOBS="${AGDA_JOBS:-4}"
AGDA_FLAKE="${AGDA_FLAKE:-/home/c/Documents/code/agda#debug.bin}"

SESSION_NAME="${DASHI_TMUX_SESSION:-dashi_agda_check_$$}"
WAIT_CHANNEL="dashi_wait_$$"
STATUS_DIR="${DASHI_STATUS_DIR:-${XDG_CACHE_HOME:-/home/c/.cache}/dashi-agda29/status}"
mkdir -p "$STATUS_DIR"
STATUS_FILE="$(mktemp "$STATUS_DIR/status_XXXXXX.txt")"

if [ -z "${TMUX:-}" ] && [ "${DASHI_NO_TMUX:-0}" != "1" ] && command -v tmux >/dev/null 2>&1; then
  rm -f "$STATUS_FILE"
  tmux kill-session -t "${SESSION_NAME}" 2>/dev/null || true

  echo "Launching execution inside detached tmux session '${SESSION_NAME}' (waiting on channel ${WAIT_CHANNEL})..."

  if ! tmux new-session -d -s "${SESSION_NAME}" \
    "bash -lc '
      set +e
            export DASHI_AGDA29_CACHE_ROOT=\"${DASHI_AGDA29_CACHE_ROOT:-}\"
            DASHI_NO_TMUX=1 AGDA_JOBS=\"${JOBS}\" \
              AGDA_PROFILE=\"${AGDA_PROFILE:-}\" \
              AGDA_PROFILE_VERBOSITY=\"${AGDA_PROFILE_VERBOSITY:-}\" \
              AGDA_RTS_HEAP=\"${AGDA_RTS_HEAP:-}\" \
              AGDA_RTS_STATS=\"${AGDA_RTS_STATS:-0}\" \
              AGDA_TARGETS_FILE=\"${AGDA_TARGETS_FILE:-}\" \
              DASHI_AGDA_RSS_LIMIT_MB=\"${DASHI_AGDA_RSS_LIMIT_MB:-}\" \
              \"$0\" ${@+\"$@\"}
      rc=\$?
      printf \"%s\\n\" \"\$rc\" > \"$STATUS_FILE\"
      tmux wait-for -S \"${WAIT_CHANNEL}\"
      if [ \"\$rc\" -ne 0 ] && [ \"\${DASHI_TMUX_KEEP_FAILED:-0}\" = \"1\" ]; then
        echo
        echo \"Agda check failed with status \$rc. Session retained for inspection: tmux attach -t ${SESSION_NAME}\"
        exec bash
      fi
      exit \"\$rc\"
    '"; then
    printf '%s\n' "125" > "$STATUS_FILE"
    rm -f "$STATUS_FILE"
    echo "failed to launch tmux worker session '${SESSION_NAME}'" >&2
    exit 125
  fi

  # Background sentinel: if the tmux session disappears (OOM kill, crash)
  # before the worker signals, unblock the wait channel so we don't hang.
  (
    while tmux has-session -t "${SESSION_NAME}" 2>/dev/null; do
      sleep 2
    done
    # Session is gone — give the worker a brief chance to publish its real
    # status before recording the crash/disappearance sentinel.
    for _ in 1 2 3 4 5; do
      [ -s "$STATUS_FILE" ] && break
      sleep 0.2
    done
    if [ ! -s "$STATUS_FILE" ]; then
      STATUS_TMP="${STATUS_FILE}.tmp"
      printf '%s\n' "137" > "$STATUS_TMP"
      mv -f "$STATUS_TMP" "$STATUS_FILE"
      tmux wait-for -S "${WAIT_CHANNEL}" 2>/dev/null || true
    fi
  ) &
  SENTINEL_PID=$!

  tmux wait-for "${WAIT_CHANNEL}" 2>/dev/null || true

  # Clean up sentinel
  kill "$SENTINEL_PID" 2>/dev/null || true
  wait "$SENTINEL_PID" 2>/dev/null || true

  rc="$(cat "$STATUS_FILE" 2>/dev/null || printf '137')"
  rm -f "$STATUS_FILE"
  exit "$rc"
fi
REPO_ROOT="${DASHI_REPO_ROOT:-/home/c/Documents/code/dashi_agda}"
STDLIB_SRC="${AGDA_STDLIB_SRC_29:-${AGDA_STDLIB_SRC:-}}"
STDLIB_REPO="${AGDA_STDLIB_REPO:-https://github.com/agda/agda-stdlib.git}"
STDLIB_REF="${AGDA_STDLIB_REF:-experimental}"
DASHI_CACHE_HOME="${DASHI_AGDA29_CACHE_ROOT:-${XDG_CACHE_HOME:-$HOME/.cache}/dashi-agda29}"
DASHI_EPHEMERAL="${DASHI_AGDA29_EPHEMERAL:-0}"
DASHI_CLEAN="${DASHI_AGDA29_CLEAN:-0}"
STDLIB_UPDATE="${AGDA_STDLIB_UPDATE:-0}"
AGDA_LOG_PATH="${AGDA_LOG_PATH:-/home/c/.gemini/antigravity/scratch/dashi-agda29-parallel-check.log}"
AGDA_LOG_KEEP_COUNT="${AGDA_LOG_KEEP_COUNT:-10}"
AGDA_LOG_BASE_PATH="$AGDA_LOG_PATH"

if [ -z "${XDG_CACHE_HOME:-}" ]; then
  export XDG_CACHE_HOME="$REPO_ROOT/.cache"
  mkdir -p "$XDG_CACHE_HOME"
fi

if [ -n "${AGDA_TARGETS_FILE:-}" ] && [ -f "$AGDA_TARGETS_FILE" ]; then
  mapfile -t TARGETS < "$AGDA_TARGETS_FILE"
elif [ "$#" -eq 0 ]; then
  TARGETS=("DASHI/Everything.agda")
else
  TARGETS=("$@")
fi

log_target_slug() {
  local slug="$1"
  slug="${slug//\//__}"
  slug="${slug// /_}"
  slug="${slug//[^A-Za-z0-9._-]/_}"
  printf '%s\n' "$slug"
}

build_log_path() {
  local base_path="$1"
  local target_slug="$2"
  local timestamp="$3"
  local log_dir log_file log_stem log_ext

  log_dir="$(dirname "$base_path")"
  log_file="$(basename "$base_path")"

  if [[ "$log_file" == *.* ]]; then
    log_stem="${log_file%.*}"
    log_ext=".${log_file##*.}"
  else
    log_stem="$log_file"
    log_ext=""
  fi

  printf '%s/%s-%s-%s%s\n' \
    "$log_dir" \
    "$log_stem" \
    "$timestamp" \
    "$target_slug" \
    "$log_ext"
}

prune_old_logs() {
  local base_path="$1"
  local keep_count="$2"
  local log_dir log_file log_stem log_ext pattern

  log_dir="$(dirname "$base_path")"
  log_file="$(basename "$base_path")"

  if [[ "$log_file" == *.* ]]; then
    log_stem="${log_file%.*}"
    log_ext=".${log_file##*.}"
  else
    log_stem="$log_file"
    log_ext=""
  fi

  pattern="$log_dir/$log_stem-*${log_ext}"

  mapfile -t existing_logs < <(find "$log_dir" -maxdepth 1 -type f -name "$(basename "$pattern")" -printf '%T@ %p\n' | sort -n | awk '{ $1=""; sub(/^ /, ""); print }')

  while [ "${#existing_logs[@]}" -gt "$keep_count" ]; do
    rm -f "${existing_logs[0]}"
    existing_logs=("${existing_logs[@]:1}")
  done
}

AGDA_BIN="${AGDA_BIN:-$(nix build --no-link --print-out-paths "$AGDA_FLAKE")/bin/agda}"
if [ "$DASHI_EPHEMERAL" = "1" ]; then
  DASHI_WORK="$(mktemp -d /tmp/dashi-agda29-shadow.XXXXXX)"
  STDLIB_WORK="$(mktemp -d /tmp/agda-stdlib-experimental.XXXXXX)"
else
  if [ "$DASHI_CLEAN" = "1" ]; then
    rm -rf "$DASHI_CACHE_HOME"
  fi

  mkdir -p "$DASHI_CACHE_HOME"
  LOCK_FILE="$DASHI_CACHE_HOME/check.lock"
  exec 9>"$LOCK_FILE"
  if command -v flock >/dev/null 2>&1; then
    flock 9
  fi

  DASHI_WORK="$DASHI_CACHE_HOME/dashi-shadow"
  STDLIB_WORK="$DASHI_CACHE_HOME/agda-stdlib-${STDLIB_REF}"
  mkdir -p "$DASHI_WORK" "$STDLIB_WORK"
fi
STDLIB_INCLUDE="$STDLIB_WORK/src"
STD_LIB_RESOLVED_SRC=""

resolve_stdlib_src() {
  local path="$1"
  if [ -z "$path" ]; then
    return 1
  fi

  if [ -d "$path/src" ]; then
    echo "$path/src"
  elif [ -d "$path" ]; then
    echo "$path"
  else
    return 1
  fi
}

if [ -n "$STDLIB_SRC" ]; then
  if ! STD_LIB_RESOLVED_SRC="$(resolve_stdlib_src "$STDLIB_SRC")"; then
    echo "AGDA_STDLIB_SRC_29/AGDA_STDLIB_SRC must be a readable Agda stdlib directory (or its src subdir)." >&2
    exit 2
  fi
fi

if [ "$DASHI_EPHEMERAL" = "1" ]; then
  cleanup() {
    rm -rf "$DASHI_WORK" "$STDLIB_WORK"
  }
  trap cleanup EXIT
fi

# Keep the shadow tree path stable so Agda can reuse .agdai interfaces across
# runs. Excluded receiver files, including .agdai caches, are protected because
# we intentionally do not use --delete-excluded.
rsync -a --delete --prune-empty-dirs \
  --include='*/' \
  --include='*.agda' \
  --include='*.lagda' \
  --include='*.lagda.md' \
  --include='*.lagda.rst' \
  --include='*.lagda.tex' \
  --exclude='*' \
  "$REPO_ROOT/" "$DASHI_WORK/"

if [ -n "$STD_LIB_RESOLVED_SRC" ]; then
  rsync -a --delete --exclude='*.agdai' "$STD_LIB_RESOLVED_SRC/" "$STDLIB_WORK/"
  STDLIB_INCLUDE="$STDLIB_WORK"
else
  if [ ! -d "$STDLIB_WORK/.git" ]; then
    rm -rf "$STDLIB_WORK"
    git clone --depth=1 --branch "$STDLIB_REF" "$STDLIB_REPO" "$STDLIB_WORK"
  elif [ "$STDLIB_UPDATE" = "1" ]; then
    git -C "$STDLIB_WORK" fetch --depth=1 origin "$STDLIB_REF"
    git -C "$STDLIB_WORK" checkout -q "$STDLIB_REF"
    git -C "$STDLIB_WORK" reset --hard -q "origin/$STDLIB_REF"
  fi
  STDLIB_INCLUDE="$STDLIB_WORK/src"
fi
chmod -R u+w "$STDLIB_WORK"

cd "$DASHI_WORK"
mkdir -p "$(dirname "$AGDA_LOG_PATH")"
if [ "${#TARGETS[@]}" -eq 1 ]; then
  LOG_TARGET_SLUG="$(log_target_slug "${TARGETS[0]}")"
else
  LOG_TARGET_SLUG="$(log_target_slug "${TARGETS[0]}")-plus-$(( ${#TARGETS[@]} - 1 ))"
fi
LOG_TIMESTAMP="$(date +%Y%m%d-%H%M%S)"
AGDA_LOG_PATH="$(build_log_path "$AGDA_LOG_BASE_PATH" "$LOG_TARGET_SLUG" "$LOG_TIMESTAMP")"
: >"$AGDA_LOG_PATH"
prune_old_logs "$AGDA_LOG_BASE_PATH" "$AGDA_LOG_KEEP_COUNT"
echo "Logging Agda output to: $AGDA_LOG_PATH"

AGDA_PROFILE_ARGS=()
# Optional diagnostic controls for expensive focused checks.  They are opt-in
# so ordinary wrapper invocations retain the existing Agda command line.
# Example:
#   AGDA_PROFILE=definitions AGDA_PROFILE_VERBOSITY=10 \
#   AGDA_RTS_HEAP=10G AGDA_RTS_STATS=1 DASHI_AGDA_RSS_LIMIT_MB=14000 \
#   scripts/run_agda29_parallel_check.sh DASHI/Path/To/Target.agda
if [ -n "${AGDA_PROFILE:-}" ]; then
  AGDA_PROFILE_ARGS+=("--profile=${AGDA_PROFILE}")
  if [ -n "${AGDA_PROFILE_VERBOSITY:-}" ]; then
    AGDA_PROFILE_ARGS+=("-v" "profile.${AGDA_PROFILE}:${AGDA_PROFILE_VERBOSITY}")
  fi
fi

AGDA_RTS_ARGS=()
if [ -n "${AGDA_RTS_HEAP:-}" ] || [ "${AGDA_RTS_STATS:-0}" = "1" ]; then
  AGDA_RTS_ARGS=(+RTS)
  if [ -n "${AGDA_RTS_HEAP:-}" ]; then
    AGDA_RTS_ARGS+=("-M${AGDA_RTS_HEAP}")
  fi
  if [ "${AGDA_RTS_STATS:-0}" = "1" ]; then
    AGDA_RTS_ARGS+=(-s)
  fi
  AGDA_RTS_ARGS+=(-RTS)
fi

AGDA_RUN=("$AGDA_BIN" "${AGDA_RTS_ARGS[@]}" \
  --no-libraries --no-default-libraries \
  "-j$JOBS" \
  -i . -i DCHoTT-Agda -i vendor/bishop -i cubical -i "$STDLIB_INCLUDE" \
  -WnoUnsupportedIndexedMatch \
  "${AGDA_PROFILE_ARGS[@]}")

if command -v stdbuf >/dev/null 2>&1; then
  AGDA_RUN=(stdbuf -oL -eL "${AGDA_RUN[@]}")
fi

run_agda_target() {
  local target="$1"
  local status watchdog_pid rss_kb watchdog_marker

  if [ -z "${DASHI_AGDA_RSS_LIMIT_MB:-}" ]; then
    "${AGDA_RUN[@]}" "$target"
    return
  fi

  if ! [[ "$DASHI_AGDA_RSS_LIMIT_MB" =~ ^[1-9][0-9]*$ ]]; then
    echo "DASHI_AGDA_RSS_LIMIT_MB must be a positive integer" >&2
    return 2
  fi

  watchdog_marker="$(mktemp "${TMPDIR:-/tmp}/dashi-agda-rss-watchdog.XXXXXX")"
  rm -f "$watchdog_marker"

  "${AGDA_RUN[@]}" "$target" &
  local agda_pid=$!
  (
    local limit_kb=$(( DASHI_AGDA_RSS_LIMIT_MB * 1024 ))
    while kill -0 "$agda_pid" 2>/dev/null; do
      rss_kb="$(ps -o rss= -p "$agda_pid" 2>/dev/null | tr -d '[:space:]')"
      if [[ "$rss_kb" =~ ^[0-9]+$ ]] && [ "$rss_kb" -gt "$limit_kb" ]; then
        echo "Agda RSS watchdog: ${rss_kb} KiB exceeds ${limit_kb} KiB; terminating $target" >&2
        : >"$watchdog_marker"
        kill -TERM "$agda_pid" 2>/dev/null || true
        sleep 5
        kill -KILL "$agda_pid" 2>/dev/null || true
        break
      fi
      sleep 1
    done
  ) &
  watchdog_pid=$!

  wait "$agda_pid"
  status=$?
  kill "$watchdog_pid" 2>/dev/null || true
  wait "$watchdog_pid" 2>/dev/null || true
  if [ -e "$watchdog_marker" ]; then
    rm -f "$watchdog_marker"
    # Match the tmux crash sentinel: this is a memory-resource stop, not an
    # Agda proof error.
    return 137
  fi
  rm -f "$watchdog_marker"
  return "$status"
}

for target in "${TARGETS[@]}"; do
  echo "Checking: $target"
  set +e
  run_agda_target "$target" 2>&1 | tee -a "$AGDA_LOG_PATH"
  status="${PIPESTATUS[0]}"
  set -e
  if [ "$status" -ne 0 ]; then
    echo "Agda failed for: $target" >&2
    exit "$status"
  fi
done
