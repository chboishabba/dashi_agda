#!/usr/bin/env bash
set -euo pipefail

repo="${1:-.}"
commits="${DASHI_FILM_COMMITS:-500}"
quality="${DASHI_FILM_QUALITY:--qm}"
history="${DASHI_FILM_HISTORY:-/tmp/dashi-research-film-history.json}"
profile="${DASHI_FILM_PROFILE:-/tmp/dashi-research-film-profile.json}"
github_repo="${DASHI_FILM_GITHUB_REPO:-}"

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
  --quality "$quality"

echo
echo "Rendered MP4(s):"
find tools/visualization/repo_history/media \
  -type f -name '*.mp4' -print 2>/dev/null || true
