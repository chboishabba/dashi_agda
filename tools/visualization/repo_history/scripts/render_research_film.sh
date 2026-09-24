#!/usr/bin/env bash
set -euo pipefail

if ! command -v dashi-repo-history >/dev/null 2>&1; then
  script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
  if [ -x "$script_dir/../.venv/bin/dashi-repo-history" ]; then
    export PATH="$(cd "$script_dir/../.venv/bin" && pwd):$PATH"
  fi
fi

repo="${1:-.}"
commits="${DASHI_FILM_COMMITS:-500}"
quality="${DASHI_FILM_QUALITY:--qm}"
pace="${DASHI_FILM_PACE:-1.0}"
font="${DASHI_FILM_FONT:-DejaVu Sans}"
log="${DASHI_FILM_LOG:-$repo/media/logs/dashi-research-film.log}"
history="${DASHI_FILM_HISTORY:-${TMPDIR:-/tmp}/dashi-research-film-history.json}"
profile="${DASHI_FILM_PROFILE:-${TMPDIR:-/tmp}/dashi-research-film-profile.json}"
github_repo="${DASHI_FILM_GITHUB_REPO:-}"

mkdir -p "$(dirname "$log")"
exec > >(tee -a "$log") 2>&1
printf '\n===== DASHI research-film run: %s =====\n' "$(date -Is)"
printf 'log: %s\n' "$log"

args=(
  extract "$repo"
  --ref HEAD
  --max-commits "$commits"
  --episode-context
  --compact
  --checkpoint-interval 50
  --parity-every 25
  --profile-output "$profile"
  -o "$history"
)

if [[ -n "$github_repo" ]]; then
  args+=(--github-prs "$github_repo")
fi

echo "== extract semantic history =="
dashi-repo-history "${args[@]}"

echo
echo "== inspect directed film plan =="
dashi-repo-history film "$history" --beats

echo
echo "== backend profile =="
dashi-repo-history profile "$profile"

echo
echo "== render with Manim =="
dashi-repo-history render "$history" \
  --scene research-film \
  --film-pace "$pace" \
  --film-font "$font" \
  --quality "$quality"

echo
echo "Rendered MP4(s):"
find media tools/visualization/repo_history/media \
  -type f -name '*.mp4' -print 2>/dev/null || true
