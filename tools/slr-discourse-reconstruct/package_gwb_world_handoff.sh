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
mkdir -p "$ROOT/gwb-projection" "$ROOT/fixtures"

copy_if_present() {
  local src="$1" dst="$2"
  if [[ -e "$src" ]]; then
    mkdir -p "$(dirname "$dst")"
    cp -a "$src" "$dst"
  fi
}

# Certification/source metadata only: no raw books or projected corpus text.
# The large generated gwb-world tree is intentionally NOT copied into STAGE;
# it is streamed directly from OUT_DIR into the final archive below.
copy_if_present "$HANDOFF_ROOT/gwb-full-certification.json" "$ROOT/gwb-full-certification.json"
copy_if_present "$HANDOFF_ROOT/gwb-certify.log" "$ROOT/gwb-certify.log"
copy_if_present "$HANDOFF_ROOT/gwb-source-inventory.json" "$ROOT/gwb-source-inventory.json"
copy_if_present "$HANDOFF_ROOT/README.md" "$ROOT/README.source-handoff.md"
copy_if_present "$HANDOFF_ROOT/gwb-projection/source_projection.json" "$ROOT/gwb-projection/source_projection.json"
copy_if_present "$REPO_ROOT/fixtures/slr/gwb-reviewed-wikimedia-identities-v1.jsonl" "$ROOT/fixtures/gwb-reviewed-wikimedia-identities-v1.jsonl"
copy_if_present "$REPO_ROOT/fixtures/slr/gwb-claim-relative-source-roles-v1.jsonl" "$ROOT/fixtures/gwb-claim-relative-source-roles-v1.jsonl"
copy_if_present "$REPO_ROOT/fixtures/slr/slr-world-research-tranches-v1.jsonl" "$ROOT/fixtures/slr-world-research-tranches-v1.jsonl"

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
    "schema": "slr-gwb-world-handoff-v2",
    "git_head": head,
    "scope": "GWB SLR CandidateWorldModel, SensibLaw parity, reviewed Wikimedia graph, identity/source-role contraction, multilingual parser/PNF/semantic-closure diagnostics, joined world-research tranche state, formal logs, and replay caches",
    "packaging_mode": "stream-live-world-no-full-staging-copy",
    "raw_books_embedded": False,
    "projected_corpus_text_embedded": False,
    "candidate_only": True,
    "semantic_promotion": False,
}
out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
PY

python3 - "$ROOT" "$OUT_DIR" "$ROOT/MANIFEST.sha256" <<'PY'
import hashlib
import sys
from pathlib import Path
root = Path(sys.argv[1]); out_dir = Path(sys.argv[2]); manifest = Path(sys.argv[3])
archive_suffixes = (".tar", ".tar.gz", ".tgz", ".tar.xz", ".zip")
entries = []
def digest(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for block in iter(lambda: f.read(1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()
for path in root.rglob("*"):
    if path.is_file() and path != manifest:
        entries.append((path.relative_to(root.parent).as_posix(), path))
if out_dir.is_dir():
    for path in out_dir.rglob("*"):
        if not path.is_file():
            continue
        rel_world = path.relative_to(out_dir).as_posix()
        if rel_world.endswith(archive_suffixes):
            continue
        entries.append((f"gwb-world-handoff/gwb-world/{rel_world}", path))
entries.sort(key=lambda x: x[0])
with manifest.open("w", encoding="utf-8") as f:
    for rel, path in entries:
        f.write(f"{digest(path)}  {rel}\n")
PY

mkdir -p "$(dirname "$ARCHIVE")"
rm -f "$ARCHIVE" "$ARCHIVE.sha256"
WORLD_LIST="$STAGE/world-files.list0"
if [[ -d "$OUT_DIR" ]]; then
  (
    cd "$OUT_DIR"
    find . -mindepth 1 -type f \
      ! -name '*.tar' ! -name '*.tar.gz' ! -name '*.tgz' \
      ! -name '*.tar.xz' ! -name '*.zip' -print0 | sort -z
  ) > "$WORLD_LIST"
else
  : > "$WORLD_LIST"
fi

tar --sort=name --mtime='@0' --owner=0 --group=0 --numeric-owner \
  --transform='s,^\./,gwb-world-handoff/gwb-world/,' \
  -C "$STAGE" -cJf "$ARCHIVE" gwb-world-handoff \
  -C "$OUT_DIR" --null -T "$WORLD_LIST"

SHA="$(sha256sum "$ARCHIVE" | awk '{print $1}')"
printf '%s  %s\n' "$SHA" "$(basename "$ARCHIVE")" > "$ARCHIVE.sha256"
STAGED_FILE_COUNT="$(find "$ROOT" -type f | wc -l | tr -d ' ')"
WORLD_FILE_COUNT="0"
if [[ -d "$OUT_DIR" ]]; then
  WORLD_FILE_COUNT="$(find "$OUT_DIR" -type f ! -name '*.tar' ! -name '*.tar.gz' ! -name '*.tgz' ! -name '*.tar.xz' ! -name '*.zip' | wc -l | tr -d ' ')"
fi
FILE_COUNT="$((STAGED_FILE_COUNT + WORLD_FILE_COUNT))"
CACHE_COUNT="0"; MULTILINGUAL_CACHE_COUNT="0"; SEMANTIC_CACHE_COUNT="0"
if [[ -d "$OUT_DIR/wikimedia-http-cache" ]]; then CACHE_COUNT="$(find "$OUT_DIR/wikimedia-http-cache" -type f | wc -l | tr -d ' ')"; fi
if [[ -d "$OUT_DIR/multilingual-wikimedia-http-cache" ]]; then MULTILINGUAL_CACHE_COUNT="$(find "$OUT_DIR/multilingual-wikimedia-http-cache" -type f | wc -l | tr -d ' ')"; fi
if [[ -d "$OUT_DIR/semantic-world-http-cache" ]]; then SEMANTIC_CACHE_COUNT="$(find "$OUT_DIR/semantic-world-http-cache" -type f | wc -l | tr -d ' ')"; fi

printf 'SLR_GWB_WORLD_HANDOFF_RECEIPT schema=slr-gwb-world-handoff-v2 archive=%s sha256=%s files=%s cache_files=%s multilingual_cache_files=%s semantic_cache_files=%s packaging_mode=stream-live-world-no-full-staging-copy raw_books_embedded=false projected_corpus_text_embedded=false candidate_only=true semantic_promotion=false\n' \
  "$ARCHIVE" "$SHA" "$FILE_COUNT" "$CACHE_COUNT" "$MULTILINGUAL_CACHE_COUNT" "$SEMANTIC_CACHE_COUNT" >&2
printf 'archive=%s\nsha256=%s\nsha256_file=%s\n' "$ARCHIVE" "$SHA" "$ARCHIVE.sha256"
