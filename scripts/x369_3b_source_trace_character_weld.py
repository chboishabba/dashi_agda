"""Join actual characteristic-zero normalized factor to existing source characters.

Source class triples are mandatory independent inputs, never inferred
from traces. Recompute original 6.Suz selected join, Fourier-resolve the
fused 1458 base and Monster V2 trace, then recover the Weyl scalar
without complex approximation. A passing comparison is source-relative
until the literal cover-word/class correspondence is authenticated.
"""
import argparse
import json
import sys
from pathlib import Path
from scripts.x369_3b_cyclotomic_rank import Q
from scripts.monster_3b_mmgroup_checkpointed_weyl import read_pinned
from scripts.x369_3b_cyclotomic_projector import digest
from scripts.x369_actual_weyl_frame_bidi import require
# Original source consumers import sibling scripts by bare name.
sys.path.insert(0,str(Path(__file__).resolve().parent))
from monster_3b_suzuki_all_conductors_character_audit import Cyc,audit
from monster_3b_suzuki_selected_character_join import check
from render_monster_3b_suzuki_main_quotient_match import validate


def qcyc(q):return Cyc.from_coeffs(3,[q.a,q.b,0])


def phase_trace(values,phase):
    require(len(values)==3 and phase in (1,2),'literal central-shift triple')
    w=Cyc.from_coeffs(3,[0,1,0])
    powers=[Cyc.scalar(1),w,w*w]
    out=Cyc.scalar(0)
    for i,v in enumerate(values):out=out+v*powers[(-phase*i)%3]
    return out/3


def compare(witness,rows,source,selected,join,binding):
    require(witness['status']=='actual_source_nonzero_Weyl_trace_witness' and
            witness['offset_trivial_in_Suzuki_quotient_from_E_word'] is True,
            'actual source trace witness')
    require(rows['main_table']==selected['main_table'] and rows['mn3b_table']==selected['mn3b_table']
            and rows['base_1458_main_position']==selected['base_1458_main_position']
            and all(rows[k]==selected[k] for k in ('gap_runtime_version','ctbllib_runtime_version')),
            'same original main table source')
    n=len(rows['main_class_orders'])
    require(all(len(rows[k])==n for k in ('main_class_sizes','main_to_outer','main_to_mn3b','base1458','restricted_V2')),
            'full original source rows')
    require(Cyc.wire(rows['base1458'][0])==1458 and Cyc.wire(rows['restricted_V2'][0])==196884,
            'source character degrees')
    center=selected['base_1458_extraspecial_central_class_position']-1
    require(Cyc.wire(rows['base1458'][center])==-729 and Cyc.wire(rows['restricted_V2'][center])==54,
            'source central traces')
    triple=binding['main_class_triple_1_based'];k=binding['six_suz_class_1_based']
    require(len(triple)==3 and all(type(i) is int and 1<=i<=n for i in triple) and
            type(k) is int and 1<=k<=210,'source class address')
    require(len(rows['six_to_outer'])==210 and
            all(rows['main_to_outer'][i-1]==rows['six_to_outer'][k-1] for i in triple),
            'source outer quotient alignment')
    require(binding['central_shift_words']==witness['central_shift_words'] and
            isinstance(binding['class_identification_source_ref'],str) and bool(binding['class_identification_source_ref']),
            'literal source class binding required')
    phase=witness['phase']
    b=phase_trace([Cyc.wire(rows['base1458'][i-1]) for i in triple],phase)
    t=phase_trace([Cyc.wire(rows['restricted_V2'][i-1]) for i in triple],phase)
    r=Q.wire(witness['offset_normalized_Weyl_trace'])
    m=Q.wire(witness['normalized_multiplicity_trace'])
    require(bool(r),'nonzero Weyl trace witness')
    # Both zero or both nonzero is necessary for same actual base action.
    require(b!=0,'source class binding has zero canonical trace on nonzero reference')
    require(qcyc(r*m)==t,'actual phase trace differs from source restriction')
    scalar=b*qcyc(r.inv())
    require(scalar!=0,'canonical reference scalar')
    table12={x['label']:x for x in source['degree12']}
    table78={x['label']:x for x in source['degree78']}
    possibilities=[]
    for a in join['selected_atlas_12']:
        for d in join['selected_atlas_78']:
            expected=Cyc.wire(table12[a]['values'][k-1])+Cyc.wire(table78[d]['values'][k-1])
            if b*expected==t:
                possibilities.append([a,d])
    return dict(status='source_relative_3B_trace_weld' if possibilities else 'source_relative_character_mismatch',
        source_phase_trace=t.short(),canonical_729_phase_trace=b.short(),reference_to_source_scalar=scalar.short(),
        possible_selected_12_78_pairs=possibilities,six_suz_class_1_based=k,
        main_class_triple_1_based=triple,all_character_rows_recomputed=True,
        class_identification_source_ref=binding['class_identification_source_ref'],
        literal_cover_class_map_independently_authenticated=False,
        coherent_scalar_cochain_all_relations_certified=False,
        characteristic_zero_12_plus_78_certified=False)


def main():
    p=argparse.ArgumentParser()
    for n in ('witness','trace-source','all-rows','selected','binding'):
        p.add_argument('--'+n,type=Path,required=True);p.add_argument('--'+n+'-sha256',required=True)
    p.add_argument('--output',type=Path,required=True);a=p.parse_args()
    data={n:read_pinned(getattr(a,n),getattr(a,n+'_sha256')) for n in ('witness','trace_source','all_rows','selected','binding')}
    if data['witness'].get('status')=='actual_cyclotomic_word_factor':
        data['witness']=data['witness']['trace_witness']
        require(data['witness'] is not None,'phase-closed actual word required')
    j=check(data['all_rows'],data['selected'],audit_fn=audit,selected_validate_fn=validate)
    r=compare(data['witness'],data['trace_source'],data['all_rows'],data['selected'],j,data['binding'])
    r['input_sha256']={n:getattr(a,n+'_sha256') for n in data}
    a.output.parent.mkdir(parents=True,exist_ok=True)
    with a.output.open('x') as f:json.dump(r,f,indent=2,sort_keys=True);f.write('\n')
    print(r['status'],digest(a.output.read_bytes()))
    if not r['possible_selected_12_78_pairs']:raise SystemExit(2)

if __name__=='__main__':main()
