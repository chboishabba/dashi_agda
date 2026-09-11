#!/usr/bin/env bash
set -euo pipefail

HERE="$(cd "$(dirname "$0")" && pwd)"
HANDOFF_ROOT="${1:-/tmp/slr-validation-20260911}"
OUT_DIR="${2:-$HANDOFF_ROOT/gwb-world}"
LANGUAGES="${3:-en,es,fr,de}"
GRAPH="$OUT_DIR/gwb-wikimedia-world-graph.json"
CACHE_DIR="$OUT_DIR/multilingual-wikimedia-http-cache"
OUTPUT="$OUT_DIR/gwb-multilingual-wikimedia-parser-compat.json"
ERR="$OUT_DIR/gwb-multilingual-wikimedia-parser-compat.stderr"

[[ -s "$GRAPH" ]] || { echo "ERROR: missing graph $GRAPH" >&2; exit 1; }
mkdir -p "$CACHE_DIR"

python3 "$HERE/slr_multilingual_wikimedia_parser_compat.py" \
  --graph "$GRAPH" \
  --output "$OUTPUT" \
  --cache-dir "$CACHE_DIR" \
  --languages "$LANGUAGES" \
  --max-qids "${MULTILINGUAL_MAX_QIDS:-4}" \
  --retries "${MULTILINGUAL_MAX_RETRIES:-5}" \
  2> "$ERR"

grep -q 'schema=slr-multilingual-wikimedia-parser-compat-v1' "$ERR" || {
  echo 'ERROR: multilingual compatibility receipt missing/stale' >&2
  cat "$ERR" >&2
  exit 1
}
grep -q 'same_qid_identity=true' "$ERR" || { echo 'ERROR: shared-QID language identity not retained' >&2; exit 1; }
grep -q 'translation_equivalence=false' "$ERR" || { echo 'ERROR: same-QID surface promoted to translation equivalence' >&2; exit 1; }
grep -q 'semantic_equivalence=false' "$ERR" || { echo 'ERROR: parser compatibility promoted semantic equivalence' >&2; exit 1; }

python3 - "$OUTPUT" <<'PY'
import json, sys
m = json.load(open(sys.argv[1], encoding='utf-8'))
assert m['same_qid_pays_cross_language_identity'] is True
assert m['same_qid_pays_translation_equivalence'] is False
assert m['parser_schema_compatibility_pays_semantic_equivalence'] is False
assert m['candidate_only'] is True
assert m['semantic_promotion'] is False
assert m['summary']['language_surfaces'] > 0
print(
    'SLR_MULTILINGUAL_WIKIMEDIA_PARSER_COMPAT_VALIDATION '
    f"qids={m['summary']['qids']} language_surfaces={m['summary']['language_surfaces']} "
    f"shared_qid_identity_pairs={m['summary']['shared_qid_identity_pairs']} "
    f"trained_parser_surfaces={m['summary']['trained_parser_surfaces']} "
    f"fallback_parser_surfaces={m['summary']['fallback_parser_surfaces']} "
    'translation_equivalence=false semantic_equivalence=false candidate_only=true semantic_promotion=false'
)
PY

cat "$ERR"
printf 'multilingual_compat=%s\nmultilingual_cache=%s\n' "$OUTPUT" "$CACHE_DIR"
