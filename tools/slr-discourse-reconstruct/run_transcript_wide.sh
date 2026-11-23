#!/usr/bin/env bash
set -euo pipefail

if [[ $# -lt 1 ]]; then
  echo "usage: $0 SPECIMEN_DIR [PROFILES_TSV]" >&2
  exit 2
fi

specimen_dir=$1
profiles=${2:-}
parser="$specimen_dir/parser.tsv"
pnf="$specimen_dir/pnf.stdout"
source="$specimen_dir/source.txt"
source_sha="$specimen_dir/source.sha256"
out="$specimen_dir/discourse-cuts-transcript-wide.tsv"
err="$specimen_dir/discourse-cuts-transcript-wide.stderr"
short="$specimen_dir/discourse-cuts-transcript-wide-top3.tsv"

args=(
  --parser "$parser"
  --pnf "$pnf"
  --source "$source"
  --source-sha "$source_sha"
  --top 1000000
)
if [[ -n "$profiles" ]]; then
  args+=(--profiles "$profiles")
fi

cargo run --release -- "${args[@]}" >"$out" 2>"$err"

# Keep the header plus the three highest-ranked cut candidates in each sentence.
awk -F '\t' 'NR==1 || ($3+0)<=3' "$out" >"$short"

printf 'full=%s\nshort=%s\nstderr=%s\n' "$out" "$short" "$err"
