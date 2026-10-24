#!/usr/bin/env python3
"""Backend-free selected-3B D4 character test from ordinary Monster traces.

For each of 8 actual, independently identified D4 elements g in C_N(3B)(z),
take SOURCE-IDENTIFIED ordinary χ_196883 values at g, zg, z²g.
Then χ_(Wζ)(g) = (χ(g)+ζ²χ(zg)+ζχ(z²g))/3.
In Z[ζ], ζ²=-1-ζ, the answer is the integer pair
  ((χ(g)-χ(zg))/3,(χ(z²g)-χ(zg))/3).

Provenance is declared by a manifest, NOT authenticated by this pure
arithmetic checker. This cannot create the missing actual class map/embedding.
"""
import argparse,json
from pathlib import Path

EXPECTED={'identity':65610,'half':810,'quarter':90,'axis':2430,'diagonal':2430}
COUNTS={'identity':1,'half':1,'quarter':2,'axis':2,'diagonal':2}

def phase_trace(chig,chizg,chiz2g):
    if any(type(v) is not int for v in (chig,chizg,chiz2g)):
        raise ValueError('ordinary Monster character triple must be integers')
    a,b=chig-chizg,chiz2g-chizg
    if a%3 or b%3:raise ValueError('source class triple gives nonintegral Z[zeta] trace')
    return a//3,b//3

def verify(obj):
    if not isinstance(obj,dict) or not isinstance(obj.get('source_url'),str) or not obj['source_url']:
        raise ValueError('independently sourced character/class provenance URL required')
    if not isinstance(obj.get('embedding_witness_url'),str) or not obj['embedding_witness_url']:
        raise ValueError('distinct actual D4->C_N3B(z) embedding evidence URL required')
    rows=obj.get('classes')
    if not isinstance(rows,list) or len(rows)!=8:
        raise ValueError('all eight actual D4 elements must be supplied')
    seen=set();counts={k:0 for k in COUNTS};evaluations={}
    for row in rows:
        if not isinstance(row,dict):raise ValueError('each class row must be an object')
        name,cl=row.get('word_id'),row.get('d4_class')
        if not isinstance(name,str) or not name or name in seen:
            raise ValueError('unique actual D4 element identifiers required')
        seen.add(name)
        if cl not in EXPECTED:raise ValueError('invalid D4 class')
        counts[cl]+=1
        pos=row.get('monster_class_positions')
        if not (isinstance(pos,list) and len(pos)==3 and
                all(type(v) is int and v>0 for v in pos)):
            raise ValueError('three exact source class positions required')
        vals=row.get('monster_character_triple')
        if not (isinstance(vals,list) and len(vals)==3):
            raise ValueError('three Monster χ-values required')
        a,b=phase_trace(*vals)
        evaluations[name]=dict(d4_class=cl,monster_class_positions=pos,
            zeta_character=[a,b],model_character=[EXPECTED[cl],0],
            matches_model=(a,b)==(EXPECTED[cl],0))
    if counts!=COUNTS:raise ValueError('bad D4 class distribution')
    ident=next(row for row in evaluations.values() if row['d4_class']=='identity')
    if ident['zeta_character']!=[65610,0]:
        raise ValueError('selected ζ dimension is not 65610')
    matches=all(v['matches_model'] for v in evaluations.values())
    return dict(status='source-declared arithmetic verification ONLY',
        source_url=obj['source_url'],embedding_witness_url=obj['embedding_witness_url'],
        actual_class_map_verified_by_this_script=False,
        eight_source_element_character_triples=evaluations,
        matches_geometric_D4_character=matches,
        conditional_D4_intertwiner_exists=matches,
        full_N3B_intertwiner_proved=False,mmgroup_required=False)

def selftest():
    assert phase_trace(196883,53,53)==(65610,0)
    assert phase_trace(53,196883,53)==(-65610,-65610)
    try:phase_trace(196883,54,53)
    except ValueError:pass
    else:raise AssertionError('nonintegral ζ character accepted')
    try:verify({'source_url':'fixture','embedding_witness_url':'fixture','classes':[]})
    except ValueError:pass
    else:raise AssertionError('missing actual subgroup classes accepted')
    return dict(status='finite arithmetic and negative tests passed',
        only_actual_triple_available='identity 196883,53,53',
        derived_zeta_dimension=65610,actual_D4_eight_class_witness=False)

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('manifest',nargs='?',type=Path)
    p.add_argument('--selftest',action='store_true')
    p.add_argument('--receipt',type=Path)
    a=p.parse_args()
    if a.selftest:result=selftest()
    elif a.manifest and a.manifest.is_file():
        result=verify(json.loads(a.manifest.read_text()))
    else:p.error('required: actual source-backed D4 class manifest (or --selftest)')
    text=json.dumps(result,indent=2)+"\n"
    if a.receipt:a.receipt.write_text(text)
    print(text,end='')
if __name__=='__main__':main()
