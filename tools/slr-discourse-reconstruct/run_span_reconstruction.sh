#!/usr/bin/env bash
set -euo pipefail

SPECIMEN="${1:-/tmp/slr-specimens/9-sept-8-03pm}"
GRAPH="${SPECIMEN}/discourse-graph-transcript-wide.tsv"
PARSER="${SPECIMEN}/parser.tsv"
SOURCE="${SPECIMEN}/source.txt"
ROLES="${SPECIMEN}/role-transitions-transcript-wide.tsv"
ROLE_STDERR="${SPECIMEN}/role-transitions-transcript-wide.stderr"
LEDGER="${SPECIMEN}/discourse-spans-transcript-wide.tsv"
RECON="${SPECIMEN}/source-reconstructed.txt"
STDERR="${SPECIMEN}/discourse-spans-transcript-wide.stderr"

rm -f "$ROLES" "$ROLE_STDERR" "$LEDGER" "$RECON" "$STDERR"

head -n 1 "$GRAPH" | grep -q $'^schema\tnode_id.*pnf_subject_crossings.*pnf_clause_crossings' || {
  echo 'ERROR: discourse graph is stale/non-v2; rerun run_manifold_graph.sh first' >&2
  exit 1
}

cargo run --release --bin slr-role-transition -- \
  --parser "$PARSER" \
  --graph "$GRAPH" \
  > "$ROLES" \
  2> "$ROLE_STDERR"

grep -q 'schema=slr-role-transition-v1' "$ROLE_STDERR" || {
  echo 'ERROR: role-transition receipt missing/stale' >&2
  cat "$ROLE_STDERR" >&2
  exit 1
}

cargo run --release --bin slr-discourse-spans -- \
  --graph "$GRAPH" \
  --roles "$ROLES" \
  --parser "$PARSER" \
  --source "$SOURCE" \
  --ledger "$LEDGER" \
  --reconstructed "$RECON" \
  2> "$STDERR"

grep -q 'schema=slr-discourse-spans-v4' "$STDERR" || {
  echo 'ERROR: stale/non-v4 slr-discourse-spans receipt' >&2
  cat "$STDERR" >&2
  exit 1
}

grep -q 'role_blocked_rank1_singletons=' "$STDERR" || {
  echo 'ERROR: typed role compatibility gate receipt missing' >&2
  cat "$STDERR" >&2
  exit 1
}

python3 - "$SOURCE" "$RECON" <<'PY'
from pathlib import Path
import sys

src_path = Path(sys.argv[1])
rec_path = Path(sys.argv[2])
src = src_path.read_bytes()
rec = rec_path.read_bytes()

src_par = src.count(b'\n\n')
rec_par = rec.count(b'\n\n')
if len(rec) < len(src):
    raise SystemExit(f'ERROR: reconstructed bytes shrank: source={len(src)} reconstructed={len(rec)}')
if rec_par < src_par:
    raise SystemExit(f'ERROR: paragraph separators lost: source={src_par} reconstructed={rec_par}')

i = j = 0
inserted = 0
while i < len(src) and j < len(rec):
    if src[i] == rec[j]:
        i += 1
        j += 1
    elif rec[j] == 0x0A:
        inserted += 1
        j += 1
    else:
        raise SystemExit(f'ERROR: non-newline reconstruction mutation at source_byte={i} reconstructed_byte={j}')
while j < len(rec) and rec[j] == 0x0A:
    inserted += 1
    j += 1
if i != len(src) or j != len(rec):
    raise SystemExit(f'ERROR: source is not recoverable by deleting inserted newlines: matched={i}/{len(src)} reconstructed_consumed={j}/{len(rec)}')

print(f'SLR_DISCOURSE_SPAN_INTEGRITY source_bytes={len(src)} reconstructed_bytes={len(rec)} inserted_newlines={inserted} source_double_newlines={src_par} reconstructed_double_newlines={rec_par} source_recoverable=true')
PY

printf 'roles=%s\nledger=%s\nreconstructed=%s\n' "$ROLES" "$LEDGER" "$RECON"
printf '\nNext: rerun the existing spaCy -> SLR/PNF pipeline on %s into a separate reconstructed specimen directory.\n' "$RECON"
