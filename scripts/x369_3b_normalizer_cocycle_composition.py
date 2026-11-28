"""Compose actual 3B normalizer tensor factors and retain scalar cocycle.

Requires complete four phase/lift receipts from the source extractor.
Build each 729 operator from its normalized zero line and conjugated
translations. Exact F7 composition: normalized Weyl factor and opposite
scalar on multiplicity are retained; no modular-to-complex character
promotion. Group orders are evaluated in actual mmgroup.
"""
import argparse
import hashlib
import json
from dataclasses import dataclass
from pathlib import Path
from time import monotonic
import numpy as np
from scripts.x369_actual_3b_normalizer_tensor import monomial,WEIGHTS,require
from scripts.monster_3b_mmgroup_checkpointed_weyl import read_pinned


def mm(a,b):
    # Each integer dot product has <=729 summands <=36; binary64 BLAS
    # is exact at this bound, not a floating approximation to F7.
    require(a.ndim==b.ndim==2 and a.shape[1]==b.shape[0]<=729 and
            np.all((0<=a)&(a<7)) and np.all((0<=b)&(b<7)),'finite-field matrix scope')
    c=a.astype(np.float64)@b.astype(np.float64)
    require(np.all(c==np.floor(c)),'noninteger modular product')
    return c.astype(np.int64)%7


def invert_coord(c):
    a,b,t=c
    return tuple(-x%3 for x in a),tuple(-x%3 for x in b),(-t+sum(x*y for x,y in zip(a,b)))%3


@dataclass
class Factor:
    source: int
    target: int
    W: object
    M: object


def normalize(source,target,W,M):
    k=int(np.flatnonzero(W[:,0])[0]);s=int(W[k,0])
    return Factor(source,target,W*pow(s,-1,7)%7,M*s%7),s


def compose(first,second):
    require(first.target==second.source,'phase-indexed composition')
    return normalize(first.source,second.target,mm(second.W,first.W),mm(second.M,first.M))


def unit(z):
    return Factor(z,z,np.eye(729,dtype=np.int64),np.eye(90,dtype=np.int64))


def exact_equal(a,b):
    return a.source==b.source and a.target==b.target and np.array_equal(a.W,b.W) and np.array_equal(a.M,b.M)


def from_receipt(r):
    c=r['contract'];z=c['target_zeta']
    require(r['status']=='actual_MMV7_normalizer_tensor_factor' and r['full_multiplicity_rank']==90
            and r['actual_normalizer_factorization_from_weyl_covariance'] is True
            and [v['j'] for v in r['columns']]==list(range(90)),'actual factor receipt complete')
    phi=np.asarray(r['reference_phi'],dtype=np.int64)
    require(phi.shape==(729,) and np.all((0<=phi)&(phi<7)),'source reference line')
    aa=r['transformed_translation_coordinates'];bb=r['transformed_modulation_coordinates']
    require(len(aa)==len(bb)==6,'actual conjugated Weyl words')
    for b in bb:require(np.array_equal(monomial(phi,b,z),phi),'reference line not fixed')
    inv=[invert_coord(a) for a in aa]
    columns=[]
    for u in WEIGHTS:
        v=phi
        for a,k in zip(inv,u):
            for _ in range(k):v=monomial(v,a,z)
        columns.append(v)
    W=np.stack(columns,axis=1)
    M=np.asarray(r['multiplicity_matrix'],dtype=np.int64)
    Mi=np.asarray(r['multiplicity_inverse'],dtype=np.int64)
    require(M.shape==Mi.shape==(90,90) and np.array_equal(mm(M,Mi),np.eye(90,dtype=np.int64)),
            'actual multiplicity inverse')
    require(np.array_equal(M,np.array([v['coefficients'] for v in r['columns']],dtype=np.int64).T),
            'actual source columns changed')
    f,s=normalize(c['source_zeta'],z,W,M)
    require(s==1,'source scalar normalization mismatch')
    return f


def word(factors,start,names,deadline):
    out=unit(start);scalars=[]
    for name in names:
        if monotonic()>=deadline:raise TimeoutError('normalizer relation budget')
        out,s=compose(out,factors[(name,out.target)])
        scalars.append(s)
    return out,scalars


def power(f,n,deadline):
    require(f.source==f.target and n>=0,'closed phase power')
    x=unit(f.source);scalars=[]
    while n:
        if monotonic()>=deadline:raise TimeoutError('normalizer power budget')
        if n&1:
            x,s=compose(x,f);scalars.append(s)
        n//=2
        if n:
            f,s=compose(f,f);scalars.append(s)
    return x,scalars


def run(a):
    from mmgroup import MM
    deadline=monotonic()+a.seconds
    local=read_pinned(a.local,a.local_sha256)
    manifest=local['actual_local_sources']['ternary_manifest']
    words={r['name']:MM(r['word']) for r in manifest['normalizer_lifts']}
    factors={};frame={}
    for path,digest in zip(a.factor,a.factor_sha256,strict=True):
        r=read_pinned(path,digest);c=r['contract'];name=c['lift'];z=c['source_zeta']
        require(c['local_sha256']==a.local_sha256 and MM(c['word'])==words[name],'actual local word scope')
        require((name,z) not in factors,'duplicate phase factor')
        for p,h in ((z,c['frame_sha256']),(c['target_zeta'],c['target_sha256'])):
            require(p not in frame or frame[p]==h,'inconsistent phase frame identity');frame[p]=h
        factors[name,z]=from_receipt(r)
    require(set(factors)=={(name,z) for name in words for z in (2,4)},'all actual phase factors required')
    rows=[]
    # First generator orders, then mixed product orders. Use exact
    # group words for the order; never infer order from matrix degree.
    names=list(words)
    scopes=[(name,) for name in names]+[tuple(names),tuple(reversed(names))]
    for s in scopes:
        for z in (2,4):
            try:
                f,sc=word(factors,z,s,deadline)
                g=MM(1)
                for name in s:g=g*words[name]
                order=g.order();require(order>0,'actual group order')
                repeats=1
                if f.target!=z:
                    f,t=compose(f,word(factors,f.target,s,deadline)[0]);sc.append(t);repeats=2
                require(order%repeats==0,'actual phase-order compatibility')
                out,pc=power(f,order//repeats,deadline)
                require(exact_equal(out,unit(z)),'actual tensor factors do not obey source order')
                rows.append(dict(word=s,zeta=z,actual_group_order=order,
                    normalized_W_and_M_relation=True,composition_scalars=sc,power_scalars=pc))
            except TimeoutError:
                return dict(status='bounded_incomplete',rows=rows,all_normalizer_relations_certified=False)
    return dict(status='actual_3b_tensor_order_relations',rows=rows,
        phase_frame_hashes=frame,all_normalizer_relations_certified=False,
        actual_source_word_orders_verified=True,characteristic_zero_12_plus_78_certified=False)


def main():
    p=argparse.ArgumentParser()
    p.add_argument('--local',type=Path,required=True);p.add_argument('--local-sha256',required=True)
    p.add_argument('--factor',type=Path,action='append',required=True);p.add_argument('--factor-sha256',action='append',required=True)
    p.add_argument('--seconds',type=float,default=90);p.add_argument('--output',type=Path,required=True)
    a=p.parse_args();require(0<a.seconds<=90 and len(a.factor)==len(a.factor_sha256)==4,'bounded four-factor scope')
    r=run(a);a.output.parent.mkdir(parents=True,exist_ok=True)
    with a.output.open('x') as f:json.dump(r,f,sort_keys=True,indent=2);f.write('\n')
    print(r['status'],len(r['rows']))
    if r['status']=='bounded_incomplete':raise SystemExit(2)

if __name__=='__main__':main()
