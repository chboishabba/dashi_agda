"""Checkpointed actual 3B rank90 Weyl source, using the admitted local receipt.

Uses the original Dietrich/Lee/Pisani/Popiel words and source checker.
No synthetic sector or inferred normalizer multiplicity action.
Immutable receipt chain; replay only previously selected seed labels,
not the thousands of rejected candidates.
"""
import argparse
import hashlib
import json
from pathlib import Path
from time import monotonic
from itertools import islice
from scripts.x369_actual_weyl_frame_bidi import WeylFrame,RowBasis,source_sha,require
from scripts.monster_3b_mmgroup_matrix_free_intertwiner import candidates
from scripts.monster_3b_mmgroup_weyl_word_alignment import check_words

ROOT=Path(__file__).resolve().parent
OWNERS=('x369_actual_weyl_frame_bidi.py','monster_3b_mmgroup_checkpointed_weyl.py',
        'monster_3b_mmgroup_matrix_free_intertwiner.py','monster_3b_mmgroup_weyl_word_alignment.py',
        'monster_3b_mmgroup_source_symplectic_basis.py')


def sha(raw):return hashlib.sha256(raw).hexdigest()


def read_pinned(path,expected):
    raw=path.read_bytes()
    require(sha(raw)==expected,'pinned source/checkpoint receipt SHA mismatch')
    return json.loads(raw)


def run(a):
    from mmgroup import MM,MMV
    from importlib.metadata import version
    require(0<a.seconds<=90 and a.candidates>0 and bool(a.resume)==bool(a.resume_sha256),
            'bounded checkpoint scope')
    deadline=monotonic()+a.seconds
    local=read_pinned(a.local_receipt,a.local_sha256)
    manifest=local['actual_local_sources']['ternary_manifest']
    checked=check_words(manifest)
    z=MM(manifest['center_word'])
    A=tuple(MM(w) for w in manifest['translation_words'])
    B=tuple(MM(w) for w in manifest['modulation_words'])
    contract=dict(local_receipt_sha256=a.local_sha256,manifest_sha256=checked['manifest_sha256'],
        mmgroup_version=version('mmgroup'),modulus=7,zeta=2,expected_multiplicity=90,
        source_owners={p:sha((ROOT/p).read_bytes()) for p in OWNERS})
    V=MMV(7);frame=WeylFrame(3,2,z,A,B,[],[],RowBasis())
    cursor=0;verified=0;checks=0
    if a.resume:
        prior=read_pinned(a.resume,a.resume_sha256)
        require(prior['contract']==contract,'source/frame contract changed')
        require(prior['status']=='bounded_incomplete','already completed frame')
        cursor=prior['candidate_cursor'];verified=prior['verified_seed_count'];checks=prior['actual_weight_checks']
        require(0<=verified<=len(prior['seed_labels'])<=90,'checkpoint seed scope')
        require(checks==verified*36,'checkpoint generator check coverage')
        for label,expected in zip(prior['seed_labels'],prior['seed_sha256'],strict=True):
            require(frame.admit(V(*label),label) and source_sha(frame.seeds[-1])==expected,
                    'original projected seed did not reopen')
        require(frame.rank.pivots==prior['pivot_indices'],'seed rank changed')
    start=cursor
    if len(frame.seeds)<90:
        for label in islice(candidates(),cursor,None):
            if monotonic()>=deadline or cursor-start>=a.candidates:break
            cursor+=1
            frame.admit(V(*label),label)
            if len(frame.seeds)==90:break
    if len(frame.seeds)==90:
        for j in range(verified,90):
            if monotonic()>=deadline:break
            n,ok=frame.verify_seed(j,deadline)
            if not ok:break  # no partially paid seed carried to the next run
            checks+=n;verified+=1
    bidi=False
    if verified==90 and monotonic()<deadline:bidi=frame.check_bidi()
    complete=verified==90 and bidi
    return dict(status='actual_MMV7_ternary_weyl_basis' if complete else 'bounded_incomplete',
        contract=contract,source_word_check=checked,parent_checkpoint_sha256=a.resume_sha256,
        candidate_cursor=cursor,new_candidates_inspected=cursor-start,
        seed_labels=frame.labels,seed_sha256=[source_sha(v) for v in frame.seeds],
        pivot_indices=frame.rank.pivots,independent_zero_weight_seeds=len(frame.seeds),
        verified_seed_count=verified,actual_weight_checks=checks,
        implicit_columns=729*len(frame.seeds),selected_source_degree=65610,
        actual_two_weight_bidi=bidi,all_declared_seed_checks_complete=complete,
        explicit_weight_projection_inverse_available=True,
        normalizer_12_plus_78_source_identification=False,
        original_character_zero_flm_action_certified=False)


def main():
    p=argparse.ArgumentParser()
    p.add_argument('--local-receipt',type=Path,required=True);p.add_argument('--local-sha256',required=True)
    p.add_argument('--resume',type=Path);p.add_argument('--resume-sha256')
    p.add_argument('--seconds',type=float,default=80);p.add_argument('--candidates',type=int,default=1000)
    p.add_argument('--output',type=Path,required=True)
    a=p.parse_args()
    if a.output.exists():raise FileExistsError(a.output)
    r=run(a);a.output.parent.mkdir(parents=True,exist_ok=True)
    with a.output.open('x') as f:json.dump(r,f,sort_keys=True,indent=2);f.write('\n')
    print(json.dumps({k:v for k,v in r.items() if k not in ('seed_labels','seed_sha256','pivot_indices','source_word_check','contract')},indent=2))
    print('receipt_sha256',sha(a.output.read_bytes()))
    if not r['all_declared_seed_checks_complete']:raise SystemExit(2)


if __name__=='__main__':main()
