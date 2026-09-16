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

while IFS=$'\t' read -r schema variant perturbation_class replacement original lemma pos dep head sid tok next src candidate; do
  [[ "$variant" == "variant" ]] && continue
  dir="$OUT/$variant"
  sha256sum "$dir/source.txt" > "$dir/source.sha256"
  "$SLR_ROOT/.venv/bin/python" "$SLR_ROOT/python/spacy_stream.py" --model en_core_web_sm "$dir/source.txt" > "$dir/parser.tsv" 2> "$dir/spacy.stderr"
  "$SLR_ROOT/target/release/sensiblaw-stream" < "$dir/parser.tsv" > "$dir/pnf.stdout" 2> "$dir/pnf.stderr"
  args=("$dir")
  [[ -n "$PROFILES" ]] && args+=("$PROFILES")
  bash "$(dirname "$0")/run_transcript_wide.sh" "${args[@]}" >/dev/null
  bash "$(dirname "$0")/run_manifold_graph.sh" "$dir" >/dev/null
  cargo run --release --bin slr-subject-transition -- \
    --parser "$dir/parser.tsv" \
    --graph "$dir/discourse-graph-transcript-wide.tsv" \
    > "$dir/subject-transitions.tsv" \
    2> "$dir/subject-transitions.stderr"
done < "$OUT/manifest.tsv"

python3 - "$OUT" <<'PY'
from pathlib import Path
import csv, sys
out=Path(sys.argv[1])
manifest=list(csv.DictReader((out/'manifest.tsv').open(), delimiter='\t'))
rows=[]

def hard_cut_admissible(r):
    proj=r['projection']; subj=int(r['pnf_subject_crossings'] or 0); obj=int(r['pnf_object_crossings'] or 0); clause=int(r['pnf_clause_crossings'] or 0)
    if proj=='speaker': return subj==0 and obj==0 and clause==0
    if proj=='quote': return subj==0 and obj==0
    return False

for m in manifest:
    v=m['variant']; d=out/v; target_anchor=f"{m['replacement']}|{m['next_surface']}"
    graph=list(csv.DictReader((d/'discourse-graph-transcript-wide.tsv').open(), delimiter='\t'))
    hits=[r for r in graph if r['anchor']==target_anchor]
    if hits:
        sid=int(m['sentence']); hits.sort(key=lambda r:(abs(int(r['sentence'])-sid),int(r['within_sentence_rank'])))
        r=hits[0]
        tr=list(csv.DictReader((d/'subject-transitions.tsv').open(), delimiter='\t'))
        th=[x for x in tr if x['sentence']==r['sentence'] and x['split']==r['split']]
        st=th[0]['subject_transition'] if th else 'not-located'
        admitted=hard_cut_admissible(r)
        rows.append({**m,'resolved_sentence':r['sentence'],'rank':r['within_sentence_rank'],'anchor':r['anchor'],'projection':r['projection'],'pareto_fibres':r['pareto_fibres'],'subject_transition':st,'subject_crossings':r['pnf_subject_crossings'],'object_crossings':r['pnf_object_crossings'],'clause_crossings':r['pnf_clause_crossings'],'coordination_crossings':r['pnf_coordination_crossings'],'hard_cut_admissible':str(admitted).lower()})
    else:
        rows.append({**m,'resolved_sentence':'','rank':'','anchor':target_anchor,'projection':'not-located','pareto_fibres':'','subject_transition':'not-located','subject_crossings':'','object_crossings':'','clause_crossings':'','coordination_crossings':'','hard_cut_admissible':'false'})

fields=['schema','variant','perturbation_class','replacement','original_surface','original_lemma','original_pos','original_dep','sentence','token','next_surface','resolved_sentence','rank','anchor','projection','pareto_fibres','subject_transition','subject_crossings','object_crossings','clause_crossings','coordination_crossings','hard_cut_admissible','candidate_only']
with (out/'counterfactual-manifold.tsv').open('w',newline='') as f:
    w=csv.DictWriter(f,fieldnames=fields,delimiter='\t',extrasaction='ignore'); w.writeheader(); w.writerows(rows)

def envelope(rs):
    fronts=[set(filter(None,r['pareto_fibres'].split(','))) for r in rs]
    must=set.intersection(*fronts) if fronts else set(); may=set.union(*fronts) if fronts else set()
    states=sorted({r['subject_transition'] for r in rs})
    adm=[r['hard_cut_admissible']=='true' for r in rs]
    return dict(n=len(rs),must=must,may=may,projection_stable=must==may,states=states,subject_stable=len(states)==1,hard_cut_must=all(adm) if adm else False,hard_cut_may=any(adm) if adm else False,consumer_stable=(len(states)==1 and bool(adm) and all(x==adm[0] for x in adm)))

lex=[r for r in rows if r['perturbation_class']=='lexical']
all_env=envelope(rows); lex_env=envelope(lex)
with (out/'counterfactual-envelope.tsv').open('w') as f:
    f.write('schema\tscope\tmust_fibres\tmay_fibres\tprojection_stable\tsubject_transition_values\tsubject_transition_stable\thard_cut_must\thard_cut_may\tconsumer_stable\trealizations\tcandidate_only\n')
    for scope,e in [('lexical',lex_env),('all-including-structural',all_env)]:
        f.write('slr-lexical-counterfactual-envelope-v3\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\ttrue\n'.format(scope,','.join(sorted(e['must'])),','.join(sorted(e['may'])),str(e['projection_stable']).lower(),','.join(e['states']),str(e['subject_stable']).lower(),str(e['hard_cut_must']).lower(),str(e['hard_cut_may']).lower(),str(e['consumer_stable']).lower(),e['n']))
for scope,e in [('lexical',lex_env),('all',all_env)]:
    print(f"SLR_LEXICAL_COUNTERFACTUAL_ENVELOPE scope={scope} realizations={e['n']} must={','.join(sorted(e['must'])) or '-'} may={','.join(sorted(e['may'])) or '-'} projection_stable={str(e['projection_stable']).lower()} subject_states={','.join(e['states'])} subject_stable={str(e['subject_stable']).lower()} hard_cut_must={str(e['hard_cut_must']).lower()} hard_cut_may={str(e['hard_cut_may']).lower()} consumer_stable={str(e['consumer_stable']).lower()} candidate_only=true")
PY

printf 'manifest=%s\nmanifold=%s\nenvelope=%s\n' "$OUT/manifest.tsv" "$OUT/counterfactual-manifold.tsv" "$OUT/counterfactual-envelope.tsv"
