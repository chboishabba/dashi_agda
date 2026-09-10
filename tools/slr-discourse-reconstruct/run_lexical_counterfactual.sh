#!/usr/bin/env bash
set -euo pipefail

if [[ $# -lt 4 ]]; then
  echo "usage: $0 SPECIMEN_DIR SENTENCE TOKEN SLR_ROOT [PROFILES_TSV]" >&2
  exit 2
fi
SPECIMEN=$1
SENTENCE=$2
TOKEN=$3
SLR_ROOT=$4
PROFILES=${5:-}
OUT="${SPECIMEN}/lexical-counterfactual-s${SENTENCE}-t${TOKEN}"

cargo run --release --bin slr-lexical-counterfactual -- \
  --parser "${SPECIMEN}/parser.tsv" \
  --source "${SPECIMEN}/source.txt" \
  --sentence "$SENTENCE" --token "$TOKEN" --out-dir "$OUT" \
  2> "${OUT}.stderr"

while IFS=$'\t' read -r schema variant replacement original lemma pos dep head sid tok next src candidate; do
  [[ "$variant" == "variant" ]] && continue
  dir="$OUT/$variant"
  sha256sum "$dir/source.txt" > "$dir/source.sha256"
  "$SLR_ROOT/.venv/bin/python" "$SLR_ROOT/python/spacy_stream.py" --model en_core_web_sm "$dir/source.txt" > "$dir/parser.tsv" 2> "$dir/spacy.stderr"
  "$SLR_ROOT/target/release/sensiblaw-stream" < "$dir/parser.tsv" > "$dir/pnf.stdout" 2> "$dir/pnf.stderr"
  args=("$dir")
  [[ -n "$PROFILES" ]] && args+=("$PROFILES")
  bash "$(dirname "$0")/run_transcript_wide.sh" "${args[@]}" >/dev/null
  bash "$(dirname "$0")/run_manifold_graph.sh" "$dir" >/dev/null
done < "$OUT/manifest.tsv"

python3 - "$OUT" <<'PY'
from pathlib import Path
import csv, sys
out=Path(sys.argv[1])
manifest=list(csv.DictReader((out/'manifest.tsv').open(), delimiter='\t'))
rows=[]
front_sets=[]
for m in manifest:
    v=m['variant']; d=out/v
    target_anchor=f"{m['replacement']}|{m['next_surface']}"
    graph=list(csv.DictReader((d/'discourse-graph-transcript-wide.tsv').open(), delimiter='\t'))
    hits=[r for r in graph if r['anchor']==target_anchor]
    # Replacement can alter sentence numbering. Prefer nearest original sentence id.
    if hits:
        sid=int(m['sentence']); hits.sort(key=lambda r:(abs(int(r['sentence'])-sid),int(r['within_sentence_rank'])))
        r=hits[0]
        fs=set(filter(None,r['pareto_fibres'].split(','))); front_sets.append(fs)
        rows.append({**m,'resolved_sentence':r['sentence'],'rank':r['within_sentence_rank'],'anchor':r['anchor'],'projection':r['projection'],'pareto_fibres':r['pareto_fibres'],'subject_crossings':r['pnf_subject_crossings'],'object_crossings':r['pnf_object_crossings'],'clause_crossings':r['pnf_clause_crossings'],'coordination_crossings':r['pnf_coordination_crossings']})
    else:
        front_sets.append(set())
        rows.append({**m,'resolved_sentence':'','rank':'','anchor':target_anchor,'projection':'not-located','pareto_fibres':'','subject_crossings':'','object_crossings':'','clause_crossings':'','coordination_crossings':''})
fields=['schema','variant','replacement','original_surface','original_lemma','original_pos','original_dep','sentence','token','next_surface','resolved_sentence','rank','anchor','projection','pareto_fibres','subject_crossings','object_crossings','clause_crossings','coordination_crossings','candidate_only']
with (out/'counterfactual-manifold.tsv').open('w',newline='') as f:
    w=csv.DictWriter(f,fieldnames=fields,delimiter='\t',extrasaction='ignore');w.writeheader();w.writerows(rows)
all_names={'speaker','quote','nesting','asr','rhetorical'}
must=set.intersection(*front_sets) if front_sets else set()
may=set.union(*front_sets) if front_sets else set()
with (out/'counterfactual-envelope.tsv').open('w') as f:
    f.write('schema\tmust_fibres\tmay_fibres\tstable\trealizations\tcandidate_only\n')
    f.write('slr-lexical-counterfactual-envelope-v1\t{}\t{}\t{}\t{}\ttrue\n'.format(','.join(sorted(must)),','.join(sorted(may)),str(must==may).lower(),len(front_sets)))
print(f"SLR_LEXICAL_COUNTERFACTUAL_ENVELOPE realizations={len(front_sets)} must={','.join(sorted(must)) or '-'} may={','.join(sorted(may)) or '-'} stable={str(must==may).lower()} candidate_only=true")
PY

printf 'manifest=%s\nmanifold=%s\nenvelope=%s\n' "$OUT/manifest.tsv" "$OUT/counterfactual-manifold.tsv" "$OUT/counterfactual-envelope.tsv"
