"""Actual 2B weight-two negative sector -> 4096 x 24 Weyl basis.

Uses the concrete binary central group source adapter and existing 3B
matrix-free construction, with actual Seysen MMV(7). The rank proof
uses the genuine source character dimension and distinct weights;
not a character-zero FLM Griess algebra identification.
"""
import argparse
import json
from pathlib import Path
from time import monotonic
from scripts.check_x369_mixed_central_monster_source import actual_binary,require


def candidates():
    # Actual basis tags, prioritize the twisted part of Conway's module.
    for tag in ('X','Y','Z'):
        for i in range(2048):
            for j in range(24):yield tag,i,j
    for i in range(24):yield 'A',i,i
    for tag in ('A','B','C'):
        for i in range(24):
            for j in range(i):yield tag,i,j
    for i in range(759):
        for j in range(64):yield 'T',i,j


def run(limit,seconds):
    from mmgroup import MM,MMV
    import numpy as np
    require(0<seconds<=90 and limit>0,'bounded source scope')
    deadline=monotonic()+seconds
    source=actual_binary()
    z=MM(source['center_word'])
    A=[MM(s) for s in source['translation_words']]
    B=[MM(s) for s in source['modulation_words']]
    V=MMV(7)
    # On W_- the central sign acts by -1; all B_i commute and square 1.
    def project(v):
        w=4*(v-v*z)
        for b in B:w=4*(w+w*b)
        return w
    labels=[];seeds=[];basis=[];pivots=[];inspected=0
    for label in candidates():
        if inspected>=limit or monotonic()>=deadline:break
        inspected+=1
        w=project(V(*label))
        if w==0*w:continue
        require(w*z==6*w and all(w*b==w for b in B),'actual 2B joint weight projector')
        arr=np.asarray(w['E'],dtype=np.int16).copy()%7
        require(arr.size==196884,'actual weight-two coordinates')
        arr=arr.reshape(-1)
        for k,row in zip(pivots,basis):
            factor=int(arr[k])
            if factor:arr=(arr-factor*row)%7
        nz=np.flatnonzero(arr)
        if not len(nz):continue
        k=int(nz[0]);arr=arr*pow(int(arr[k]),-1,7)%7
        labels.append(list(label));seeds.append(w);basis.append(arr);pivots.append(k)
        if len(labels)==24:break
    checked=0;complete=len(labels)==24
    if complete:
        for w in seeds:
            for i,a in enumerate(A):
                if monotonic()>=deadline:complete=False;break
                v=w*a
                require(v*a==w and v*z==6*v,'actual 2B translation inverse')
                for j,b in enumerate(B):
                    require(v*b==(6 if i==j else 1)*v,'actual 2B weight separation')
                    checked+=1
            if not complete:break
    # The 2B character on V2 is 275+1=276. Over F7 the
    # involution is semisimple, and the integral representation has
    # the same eigenspace ranks away from characteristic two.
    # Once 24 independent zero-weight seeds exist, Weyl relations
    # give 4096 distinct weights and 24 independent vectors each.
    # This establishes basis rank using the published integral lift
    # dimension, not an explicit 98304-column numerical rank computation.
    return dict(status='actual_MMV7_binary_weyl_basis' if complete else 'bounded_incomplete',
        source=source,inspected=inspected,independent_zero_weight_seeds=len(labels),
        seed_labels=labels,pivot_indices=pivots,actual_weight_checks=checked,
        actual_projector_dimension_from_integral_2B_character=98304,
        implicit_columns=4096*len(labels),all_declared_seed_checks_complete=complete,
        all_word_basis_transport_by_weyl_relations=complete,
        full_explicit_rank_checked=False,character_zero_FLm_griess_product_certified=False,
        original_JMD_uv_action_certified=False)


def main():
    p=argparse.ArgumentParser();p.add_argument('--max-candidates',type=int,default=20000)
    p.add_argument('--seconds',type=float,default=90);p.add_argument('--output',type=Path)
    a=p.parse_args();r=run(a.max_candidates,a.seconds)
    s=json.dumps(r,sort_keys=True,indent=2)+'\n'
    if a.output:
        with a.output.open('x') as f:f.write(s)
    print(s,end='')
    if not r['all_declared_seed_checks_complete']:raise SystemExit(2)


if __name__=='__main__':main()
