"""Exact Q(omega) rank/normalizer coordinate extraction from actual seed lifts.

A nonzero mod7 minor lifts to a nonzero characteristic-zero minor;
the actual source dimension 65610 and Weyl translations give rank90.
This establishes the multiplicity coordinates, not the 12+78 identification.
"""
from fractions import Fraction as F
from dataclasses import dataclass
from pathlib import Path
import argparse
import json
import hashlib
from time import monotonic
from scripts.x369_3b_cyclotomic_projector import CV,NORM,digest
from scripts.monster_3b_mmgroup_checkpointed_weyl import read_pinned
from scripts.x369_actual_weyl_frame_bidi import require,inverse7
import numpy as np


@dataclass(frozen=True)
class Q:
    a:F=F(0)
    b:F=F(0)
    @classmethod
    def wire(cls,v):return cls(F(v[0]),F(v[1]))
    def __add__(x,y):return Q(x.a+y.a,x.b+y.b)
    def __neg__(x):return Q(-x.a,-x.b)
    def __sub__(x,y):return x+-y
    def __mul__(x,y):return Q(x.a*y.a-x.b*y.b,x.a*y.b+x.b*y.a-x.b*y.b)
    def inv(x):
        n=x.a*x.a-x.a*x.b+x.b*x.b
        require(n!=0,'singular cyclotomic pivot')
        return Q((x.a-x.b)/n,-x.b/n)
    def __truediv__(x,y):return x*y.inv()
    def __bool__(x):return bool(x.a or x.b)
    def mod7(x):
        def r(v):
            require(v.denominator%7!=0,'nonintegral reduction at 7')
            return v.numerator*pow(v.denominator,-1,7)%7
        return (r(x.a)+2*r(x.b))%7
    def pack(x):return [str(x.a),str(x.b)]


ONE=Q(F(1));ZERO=Q();OMEGA=Q(F(0),F(1));PHASE=(ONE,OMEGA,OMEGA*OMEGA)


def solve_matrix(M, rhs):
    n=len(M);k=len(rhs[0])
    require(n>0 and len(rhs)==n and all(len(x)==n for x in M) and all(len(x)==k for x in rhs),'exact solve dimensions')
    a=[list(x)+list(y) for x,y in zip(M,rhs)]
    for i in range(n):
        j=next((j for j in range(i,n) if a[j][i]),None)
        require(j is not None,'singular characteristic-zero pivot')
        a[i],a[j]=a[j],a[i]
        v=a[i][i].inv();a[i]=[v*x for x in a[i]]
        for j in range(n):
            if i==j or not a[j][i]:continue
            v=a[j][i];a[j]=[x-v*y for x,y in zip(a[j],a[i])]
    return [x[n:] for x in a]


def rank_receipt(frame,frame_sha,entries):
    require(frame['status']=='actual_MMV7_ternary_weyl_basis' and frame['verified_seed_count']==90
            and frame['actual_weight_checks']==3240 and frame['actual_two_weight_bidi'] is True,
            'complete actual modular frame')
    require(len(entries)==90,'all actual seed lifts required')
    rows=[];hashes=[];owners=None
    for j,(r,sha) in enumerate(entries):
        c=r['contract']
        require(r['status']=='actual_cyclotomic_seed_lift' and r['completed_projectors']==7
            and r['unnormalized_projector_reduces_to_actual_modular_seed'] is True
            and c['frame_sha256']==frame_sha and c['seed']==j and c['label']==frame['seed_labels'][j]
            and c['zeta']==frame['contract']['zeta'] and c['normalization']==NORM
            and c['local_sha256']==frame['contract']['local_receipt_sha256']
            and c['manifest_sha256']==frame['contract']['manifest_sha256'],'actual seed receipt mismatch')
        if owners is None:owners=c['source_owners']
        require(owners==c['source_owners'],'seed owner mismatch')
        v=CV.reopen(r['vector'])
        normalized=(v.residue()*pow(NORM,-1,7)%7).astype(np.uint8).tobytes()
        require(hashlib.sha256(normalized).hexdigest()==frame['seed_sha256'][j],'actual seed reduction digest')
        require(v.pivots(frame['pivot_indices'])==r['pivot_values'],'actual pivot payload changed')
        rows.append([Q.wire(x) for x in r['pivot_values']]);hashes.append(sha)
    M=[list(x) for x in zip(*rows)]
    mod=np.array([[x.mod7() for x in row] for row in M],dtype=np.int64)
    inv=inverse7(mod)
    require(np.array_equal(inv@mod%7,np.eye(90,dtype=np.int64)),'mod7 nonzero minor')
    return dict(status='actual_cyclotomic_rank90_minor',frame_sha256=frame_sha,
        local_sha256=frame['contract']['local_receipt_sha256'],manifest_sha256=frame['contract']['manifest_sha256'],
        zeta=frame['contract']['zeta'],normalization=NORM,seed_receipt_sha256=hashes,
        source_owners=owners,pivot_indices=frame['pivot_indices'],
        pivot_matrix=[[v.pack() for v in row] for row in M],
        inverse_mod7=inv.tolist(),rank_at_least_90=True,
        rank_exactly_90_from_source_dimension_and_Weyl=True,
        characteristic_zero_12_plus_78_certified=False)


def main():
    p=argparse.ArgumentParser()
    p.add_argument('--frame',type=Path,required=True);p.add_argument('--frame-sha256',required=True)
    p.add_argument('--seed-manifest',type=Path,required=True);p.add_argument('--seed-manifest-sha256',required=True)
    p.add_argument('--output',type=Path,required=True);a=p.parse_args()
    f=read_pinned(a.frame,a.frame_sha256)
    m=read_pinned(a.seed_manifest,a.seed_manifest_sha256)
    # Manifest paths relative to its directory; list in actual seed order.
    require(type(m) is list and len(m)==90,'complete seed manifest')
    def entries():
        for row in m:yield read_pinned(a.seed_manifest.parent/row['path'],row['sha256']),row['sha256']
    # Stream full source payloads, retain only the 90x90 exact minor.
    r=rank_receipt(f,a.frame_sha256,SeedEntries(entries(),len(m)))
    a.output.parent.mkdir(parents=True,exist_ok=True)
    with a.output.open('x') as out:json.dump(r,out,sort_keys=True,indent=2);out.write('\n')
    print(r['status'],digest(a.output.read_bytes()))


class SeedEntries:
    def __init__(self,it,n):self.it=it;self.n=n
    def __len__(self):return self.n
    def __iter__(self):return self.it

if __name__=='__main__':main()
