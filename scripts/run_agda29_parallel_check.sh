#!/usr/bin/env bash
set -euo pipefail

JOBS="${AGDA_JOBS:-8}"
AGDA_FLAKE="${AGDA_FLAKE:-/home/c/Documents/code/agda#debug.bin}"
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

if [ "$#" -eq 0 ]; then
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

AGDA_RUN=("$AGDA_BIN" \
  --no-libraries --no-default-libraries \
  "-j$JOBS" \
  -i . -i DCHoTT-Agda -i cubical -i "$STDLIB_INCLUDE" \
  -WnoUnsupportedIndexedMatch)

if command -v stdbuf >/dev/null 2>&1; then
  AGDA_RUN=(stdbuf -oL -eL "${AGDA_RUN[@]}")
fi

for target in "${TARGETS[@]}"; do
  echo "Checking: $target"
  set +e
  "${AGDA_RUN[@]}" "$target" 2>&1 | tee -a "$AGDA_LOG_PATH"
  status="${PIPESTATUS[0]}"
  set -e
  if [ "$status" -ne 0 ]; then
    echo "Agda failed for: $target" >&2
    exit "$status"
  fi
done
