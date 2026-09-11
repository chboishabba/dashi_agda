#!/usr/bin/env bash
set -euo pipefail

HERE="$(cd "$(dirname "$0")" && pwd)"
OUT_DIR="${1:-/tmp/slr-validation-20260911/gwb-world}"
ITIR_VENV="${2:-/home/c/Documents/code/ITIR-suite/.venv}"
MULTI="$OUT_DIR/gwb-multilingual-wikimedia-parser-compat.json"
CACHE="$OUT_DIR/multilingual-wikimedia-http-cache"
OUT="$OUT_DIR/gwb-multilingual-pnf-role-compat.json"
ERR="$OUT_DIR/gwb-multilingual-pnf-role-compat.stderr"

[[ -s "$MULTI" ]] || { echo "ERROR: missing multilingual compatibility artifact: $MULTI" >&2; exit 1; }
[[ -d "$CACHE" ]] || { echo "ERROR: missing multilingual cache: $CACHE" >&2; exit 1; }
PY="$ITIR_VENV/bin/python"
[[ -x "$PY" ]] || PY="python3"

"$PY" "$HERE/slr_multilingual_pnf_role_compat.py" \
  --multilingual-compat "$MULTI" \
  --cache-dir "$CACHE" \
  --output "$OUT" \
  2> "$ERR"

grep -q 'schema=slr-multilingual-pnf-role-compat-v1' "$ERR" || {
  echo 'ERROR: multilingual PNF role receipt missing/stale' >&2
  cat "$ERR" >&2
  exit 1
}
grep -q 'translation_equivalence=false' "$ERR" || {
  echo 'ERROR: structural overlap was promoted to translation equivalence' >&2
  exit 1
}
grep -q 'claim_semantic_equivalence=false' "$ERR" || {
  echo 'ERROR: structural overlap was promoted to claim semantic equivalence' >&2
  exit 1
}
grep -q 'semantic_promotion=false' "$ERR" || {
  echo 'ERROR: multilingual PNF role diagnostic attempted semantic promotion' >&2
  exit 1
}

cat "$ERR"
printf 'multilingual_pnf_role_compat=%s\n' "$OUT"
