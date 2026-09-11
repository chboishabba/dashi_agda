#!/usr/bin/env bash
set -euo pipefail

HERE="$(cd "$(dirname "$0")" && pwd)"
REPO_ROOT="$(cd "$HERE/../.." && pwd)"
HANDOFF_ROOT="${1:-/tmp/slr-validation-20260911}"
OUT_DIR="${2:-$HANDOFF_ROOT/gwb-world}"
ARCHIVE="${3:-$HANDOFF_ROOT/gwb-world-handoff.tar.xz}"
STAGE="$(mktemp -d)"
trap 'rm -rf "$STAGE"' EXIT
ROOT="$STAGE/gwb-world-handoff"
mkdir -p "$ROOT/gwb-world" "$ROOT/gwb-projection" "$ROOT/fixtures"

copy_if_present() {
  local src="$1" dst="$2"
  if [[ -e "$src" ]]; then
    mkdir -p "$(dirname "$dst")"
    cp -a "$src" "$dst"
  fi
}

# Certification/source metadata only: no raw books or projected corpus text.
copy_if_present "$HANDOFF_ROOT/gwb-full-certification.json" "$ROOT/gwb-full-certification.json"
copy_if_present "$HANDOFF_ROOT/gwb-certify.log" "$ROOT/gwb-certify.log"
copy_if_present "$HANDOFF_ROOT/gwb-source-inventory.json" "$ROOT/gwb-source-inventory.json"
copy_if_present "$HANDOFF_ROOT/README.md" "$ROOT/README.source-handoff.md"
copy_if_present "$HANDOFF_ROOT/gwb-projection/source_projection.json" "$ROOT/gwb-projection/source_projection.json"
copy_if_present "$REPO_ROOT/fixtures/slr/gwb-reviewed-wikimedia-identities-v1.jsonl" "$ROOT/fixtures/gwb-reviewed-wikimedia-identities-v1.jsonl"
copy_if_present "$REPO_ROOT/fixtures/slr/gwb-claim-relative-source-roles-v1.jsonl" "$ROOT/fixtures/gwb-claim-relative-source-roles-v1.jsonl"

# Copy all generated GWB-world receipts, models, logs, graph sidecars and HTTP
# caches (including optional multilingual diagnostics), but never recursively
# include an archive produced by this packager.
if [[ -d "$OUT_DIR" ]]; then
  while IFS= read -r -d '' src; do
    rel="${src#$OUT_DIR/}"
    case "$rel" in
      *.tar|*.tar.gz|*.tgz|*.tar.xz|*.zip) continue ;;
    esac
    if [[ -d "$src" ]]; then
      mkdir -p "$ROOT/gwb-world/$rel"
    else
      mkdir -p "$(dirname "$ROOT/gwb-world/$rel")"
      cp -a "$src" "$ROOT/gwb-world/$rel"
    fi
  done < <(find "$OUT_DIR" -mindepth 1 -print0)
fi

GIT_HEAD="unknown"
if git -C "$REPO_ROOT" rev-parse HEAD >/dev/null 2>&1; then
  GIT_HEAD="$(git -C "$REPO_ROOT" rev-parse HEAD)"
fi

python3 - "$ROOT/HANDOFF.json" "$GIT_HEAD" <<'PY'
import json, sys
from pathlib import Path
out = Path(sys.argv[1])
head = sys.argv[2]
payload = {
    "schema": "slr-gwb-world-handoff-v1",
    "git_head": head,
    "scope": "GWB SLR CandidateWorldModel, SensibLaw parity, reviewed Wikimedia graph, identity/source-role contraction, optional multilingual parser diagnostics, formal logs, and replay caches",
    "raw_books_embedded": False,
    "projected_corpus_text_embedded": False,
    "candidate_only": True,
    "semantic_promotion": False,
}
out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
PY

(
  cd "$ROOT"
  find . -type f ! -name MANIFEST.sha256 -print0 \
    | sort -z \
    | xargs -0 sha256sum > MANIFEST.sha256
)

mkdir -p "$(dirname "$ARCHIVE")"
tar --sort=name --mtime='@0' --owner=0 --group=0 --numeric-owner \
  -C "$STAGE" -cJf "$ARCHIVE" gwb-world-handoff
SHA="$(sha256sum "$ARCHIVE" | awk '{print $1}')"
printf '%s  %s\n' "$SHA" "$(basename "$ARCHIVE")" > "$ARCHIVE.sha256"
FILE_COUNT="$(find "$ROOT" -type f | wc -l | tr -d ' ')"
CACHE_COUNT="0"
if [[ -d "$ROOT/gwb-world/wikimedia-http-cache" ]]; then
  CACHE_COUNT="$(find "$ROOT/gwb-world/wikimedia-http-cache" -type f | wc -l | tr -d ' ')"
fi
MULTILINGUAL_CACHE_COUNT="0"
if [[ -d "$ROOT/gwb-world/multilingual-wikimedia-http-cache" ]]; then
  MULTILINGUAL_CACHE_COUNT="$(find "$ROOT/gwb-world/multilingual-wikimedia-http-cache" -type f | wc -l | tr -d ' ')"
fi

printf 'SLR_GWB_WORLD_HANDOFF_RECEIPT schema=slr-gwb-world-handoff-v1 archive=%s sha256=%s files=%s cache_files=%s multilingual_cache_files=%s raw_books_embedded=false projected_corpus_text_embedded=false candidate_only=true semantic_promotion=false\n' \
  "$ARCHIVE" "$SHA" "$FILE_COUNT" "$CACHE_COUNT" "$MULTILINGUAL_CACHE_COUNT" >&2
printf 'archive=%s\nsha256=%s\nsha256_file=%s\n' "$ARCHIVE" "$SHA" "$ARCHIVE.sha256"
