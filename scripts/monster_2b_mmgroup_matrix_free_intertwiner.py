"""Actual 2B negative sector, direct twisted-coordinate seed construction.

Seysen mmgroup documentation: A/B/C/T/X are the 2B-positive sector
(300 + 98280), Y/Z the negative sector (2*2048*24).
Start with 24 multiplicity coordinates, not 20,000 positive X vectors.
The declared source is checked rather than assumed. The shared Weyl
frame implements exact characteristic-7 forward and inverse transport.
"""
import argparse
import json
from pathlib import Path
from time import monotonic
from scripts.check_x369_mixed_central_monster_source import actual_binary,require
from scripts.x369_actual_weyl_frame_bidi import WeylFrame,RowBasis,source_sha


def candidates():
    # Multiplicity first, then orbit coordinate; X is positive, never
    # search it for a negative central weight.
    for i in range(2048):
        for tag in ('Y','Z'):
            for j in range(24):yield tag,i,j


def run(limit,seconds):
    from mmgroup import MM,MMV
    require(0<seconds<=90 and limit>0,'bounded source scope')
    deadline=monotonic()+seconds
    source=actual_binary()
    z=MM(source['center_word'])
    A=tuple(MM(s) for s in source['translation_words'])
    B=tuple(MM(s) for s in source['modulation_words'])
    V=MMV(7)
    frame=WeylFrame(2,6,z,A,B,[],[],RowBasis())
    signs={}
    for tag,i,j in [('A',0,0),('B',1,0),('C',1,0),('T',0,0),('X',0,0),('Y',0,0),('Z',0,0)]:
        v=V(tag,i,j);expected=6 if tag in ('Y','Z') else 1
        require(v*z==expected*v,'documented 2B sector orientation mismatch')
        signs[tag]=expected
    inspected=0
    for label in candidates():
        if inspected>=limit or monotonic()>=deadline:break
        inspected+=1
        v=V(*label)
        require(v*z==6*v,'actual twisted source basis not negative')
        frame.admit(v,label)
        if len(frame.seeds)==24:break
    checked=0;verified=0;complete=len(frame.seeds)==24
    if complete:
        for j in range(24):
            n,ok=frame.verify_seed(j,deadline);checked+=n
            if not ok:complete=False;break
            verified+=1
    bidi=False
    if complete and monotonic()<deadline:bidi=frame.check_bidi()
    else:complete=False
    return dict(status='actual_MMV7_binary_weyl_basis' if complete else 'bounded_incomplete',
        source=source,inspected=inspected,sector_tag_probes=signs,
        candidate_order='Y/Z multiplicity-first, no positive X',
        independent_zero_weight_seeds=len(frame.seeds),seed_labels=frame.labels,
        seed_sha256=[source_sha(s) for s in frame.seeds],pivot_indices=frame.rank.pivots,
        actual_weight_checks=checked,verified_seed_count=verified,
        actual_projector_dimension_from_integral_2B_character=98304,
        implicit_columns=4096*len(frame.seeds),all_declared_seed_checks_complete=complete,
        all_word_basis_transport_by_weyl_relations=complete,
        explicit_weight_projection_inverse_available=True,actual_two_weight_bidi=bidi,
        full_explicit_rank_checked=False,character_zero_FLm_griess_product_certified=False,
        original_JMD_uv_action_certified=False)


def main():
    p=argparse.ArgumentParser();p.add_argument('--max-candidates',type=int,default=20000)
    p.add_argument('--seconds',type=float,default=90);p.add_argument('--output',type=Path)
    a=p.parse_args();r=run(a.max_candidates,a.seconds)
    s=json.dumps(r,sort_keys=True,indent=2)+'\n'
    if a.output:
        a.output.parent.mkdir(parents=True,exist_ok=True)
        with a.output.open('x') as f:f.write(s)
    print(s,end='')
    if not r['all_declared_seed_checks_complete']:raise SystemExit(2)


if __name__=='__main__':main()
