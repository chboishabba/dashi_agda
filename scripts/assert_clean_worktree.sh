#!/usr/bin/env bash
set -euo pipefail

usage() {
  printf 'usage: %s --freeze-hash HASH [--repo-root PATH]\n' "$0" >&2
}

repo_root="."
freeze_hash=""

while [ "$#" -gt 0 ]; do
  case "$1" in
    --freeze-hash)
      [ "$#" -ge 2 ] || { usage; exit 64; }
      freeze_hash="$2"
      shift 2
      ;;
    --repo-root)
      [ "$#" -ge 2 ] || { usage; exit 64; }
      repo_root="$2"
      shift 2
      ;;
    --help|-h)
      usage
      exit 0
      ;;
    *)
      usage
      exit 64
      ;;
  esac
done

if [ -z "$freeze_hash" ]; then
  usage
  exit 64
fi

if ! git -C "$repo_root" rev-parse --is-inside-work-tree >/dev/null 2>&1; then
  printf 'FAIL: not inside a git worktree: %s\n' "$repo_root" >&2
  exit 70
fi

actual_head="$(git -C "$repo_root" rev-parse HEAD)"
if [ "$actual_head" != "$freeze_hash" ]; then
  printf 'FAIL: freeze hash does not match HEAD\n' >&2
  printf 'expected: %s\nactual:   %s\n' "$freeze_hash" "$actual_head" >&2
  exit 65
fi

if ! git -C "$repo_root" diff --quiet --ignore-submodules --; then
  printf 'FAIL: worktree has modified tracked files\n' >&2
  exit 66
fi

if ! git -C "$repo_root" diff --cached --quiet --ignore-submodules --; then
  printf 'FAIL: index has staged changes\n' >&2
  exit 67
fi

untracked="$(git -C "$repo_root" ls-files --others --exclude-standard)"
if [ -n "$untracked" ]; then
  printf 'FAIL: worktree has untracked files\n' >&2
  printf '%s\n' "$untracked" >&2
  exit 68
fi

printf 'OK: clean worktree certificate for %s\n' "$actual_head"
