"""Characteristic-zero 3B projector bridge on the SAME actual MMV basis.

Use unnormalized character projectors so vector arithmetic remains in
Z[1/2, omega], omega^2+omega+1=0. The missing 3^7 normalization is
explicit, never discarded. Modulo 7, omega maps to 2, so both actual
phase frames (2,4) can be lifted using the same cyclotomic convention.
Source group/action owners are the existing verified actual Weyl words
and bounded dyadic atom evaluator. No claim about full FLM VOA identity.
"""
import argparse
from dataclasses import dataclass
from fractions import Fraction as F
from pathlib import Path
from time import monotonic
import hashlib
import json
import numpy as np
from scripts.x369_monster_dyadic_source_action import DIM,Dyadic,action,require,unit
from scripts.monster_3b_mmgroup_checkpointed_weyl import read_pinned
from scripts.monster_3b_mmgroup_weyl_word_alignment import check_words
from scripts.x369_actual_weyl_frame_bidi import WeylFrame,RowBasis,source_sha,inverse7

OMEGA=((1,0),(0,1),(-1,-1))
NORM=3**7
ROOT=Path(__file__).resolve().parent
OWNERS=('x369_3b_cyclotomic_projector.py','x369_monster_dyadic_source_action.py',
        'x369_actual_weyl_frame_bidi.py','monster_3b_mmgroup_weyl_word_alignment.py')


def digest(raw):return hashlib.sha256(raw).hexdigest()


def add(a,b):
    p=max(a.power,b.power)
    return Dyadic(a.numerator*(1<<(p-a.power))+b.numerator*(1<<(p-b.power)),p)


def neg(a):return Dyadic(-a.numerator,a.power)


def zero():return Dyadic(np.zeros(DIM,dtype=object))


@dataclass
class CV:
    a: Dyadic
    b: Dyadic

    def __add__(self,o):return CV(add(self.a,o.a),add(self.b,o.b))

    def phase(self,k):
        k%=3
        if k==0:return self
        if k==1:return CV(neg(self.b),add(self.a,neg(self.b)))
        return CV(add(self.b,neg(self.a)),neg(self.a))

    def acted(self,g,deadline):
        # Preserve an exact zero component without unnecessary source atoms.
        def f(v):return action(v,g,deadline) if np.any(v.numerator) else v
        return CV(f(self.a),f(self.b))

    def same(self,o):return self.a.same(o.a) and self.b.same(o.b)

    def residue(self,p=7,omega=2):
        require((omega*omega+omega+1)%p==0,'cyclotomic reduction')
        return (self.a.residue(p).astype(np.int64)+omega*self.b.residue(p))%p

    def pivots(self,indices):
        return [[str(F(self.a.numerator[i],1<<self.a.power)),
                 str(F(self.b.numerator[i],1<<self.b.power))] for i in indices]

    def wire(self):
        def pack(v):
            return dict(power=v.power,entries=[[int(i),str(v.numerator[i])] for i in np.flatnonzero(v.numerator)])
        return [pack(self.a),pack(self.b)]

    @classmethod
    def reopen(cls,data):
        def unpack(d):
            a=np.zeros(DIM,dtype=object);last=-1
            for i,v in d['entries']:
                require(type(i) is int and last<i<DIM and int(v)!=0,'canonical sparse source')
                a[i]=int(v);last=i
            return Dyadic(a,d['power'])
        require(len(data)==2,'cyclotomic pair')
        v=cls(*(unpack(x) for x in data))
        require(v.wire()==data,'noncanonical source vector')
        return v


def eig_sum(v,g,k,deadline):
    # Right eigenvalue omega^k. Exactly 3 times the projector.
    w=v.acted(g,deadline);t=w.acted(g,deadline)
    return v+w.phase(-k)+t.phase(-2*k)


def stage_plan(manifest,phase):
    return [(manifest['center_word'],phase)]+[(w,0) for w in manifest['modulation_words']]


def run(a):
    from mmgroup import MM,MMV,MMSpace
    from importlib.metadata import version
    require(0<a.seconds<=90 and bool(a.resume)==bool(a.resume_sha256),'bounded source')
    deadline=monotonic()+a.seconds
    local=read_pinned(a.local,a.local_sha256)
    m=local['actual_local_sources']['ternary_manifest'];checked=check_words(m)
    f=read_pinned(a.frame,a.frame_sha256);fc=f['contract']
    phase=1 if a.zeta==2 else 2
    require(f['status']=='actual_MMV7_ternary_weyl_basis' and f['verified_seed_count']==90
            and f['actual_weight_checks']==3240 and f['actual_two_weight_bidi'] is True
            and fc['local_receipt_sha256']==a.local_sha256 and fc['manifest_sha256']==checked['manifest_sha256']
            and fc['zeta']==a.zeta and fc['mmgroup_version']==version('mmgroup'),'complete actual phase source')
    j=a.seed
    require(0<=j<90 and len(f['seed_labels'])==len(f['pivot_indices'])==90,'actual seed scope')
    label=f['seed_labels'][j];index=MMSpace.index_to_linear(*label)
    V=MMV(7);z=MM(m['center_word']);A=tuple(MM(w) for w in m['translation_words']);B=tuple(MM(w) for w in m['modulation_words'])
    mf=WeylFrame(3,a.zeta,z,A,B,[],[],RowBasis())
    mod=mf.project(V(*label))
    require(source_sha(mod)==f['seed_sha256'][j],'actual modular seed identity')
    plan=stage_plan(m,phase)
    contract=dict(local_sha256=a.local_sha256,frame_sha256=a.frame_sha256,
        manifest_sha256=checked['manifest_sha256'],phase=phase,zeta=a.zeta,
        seed=j,label=label,index=index,normalization=NORM,mmgroup_version=version('mmgroup'),
        source_owners={p:digest((ROOT/p).read_bytes()) for p in OWNERS})
    v=CV(unit(index),zero());cursor=0
    if a.resume:
        old=read_pinned(a.resume,a.resume_sha256)
        require(old['contract']==contract and old['status']=='bounded_incomplete','source resume mismatch')
        cursor=old['completed_projectors'];require(0<=cursor<=7,'source cursor')
        v=CV.reopen(old['vector'])
        # Replay the already paid prefix modulo 7 independently.
        mv=V(*label)
        for w,k in plan[:cursor]:
            g=MM(w);mv=mv+pow(2,-k%3,7)*(mv*g)+pow(2,-2*k%3,7)*(mv*(g**2))
        require(np.array_equal(v.residue(),np.asarray(mv['E'],dtype=np.int64)%7),'resumed projector residue')
    while cursor<7:
        if monotonic()>=deadline:break
        w,k=plan[cursor]
        try:q=eig_sum(v,MM(w),k,deadline)
        except TimeoutError:break
        v=q;cursor+=1
    complete=cursor==7
    verified=False
    if complete:
        require(np.array_equal(v.residue(),NORM*np.asarray(mod['E'],dtype=np.int64)%7),
                'actual characteristic-zero projector reduction mismatch')
        verified=True
    return dict(status='actual_cyclotomic_seed_lift' if complete else 'bounded_incomplete',
        contract=contract,parent_receipt_sha256=a.resume_sha256,completed_projectors=cursor,
        vector=v.wire(),pivot_values=v.pivots(f['pivot_indices']) if complete else None,
        unnormalized_projector_reduces_to_actual_modular_seed=verified,
        characteristic_zero_seed_membership_from_exact_source_action=complete,
        all_90_seeds_lifted=False,characteristic_zero_12_plus_78_certified=False)


def main():
    p=argparse.ArgumentParser()
    p.add_argument('--local',type=Path,required=True);p.add_argument('--local-sha256',required=True)
    p.add_argument('--frame',type=Path,required=True);p.add_argument('--frame-sha256',required=True)
    p.add_argument('--zeta',type=int,choices=(2,4),required=True);p.add_argument('--seed',type=int,required=True)
    p.add_argument('--resume',type=Path);p.add_argument('--resume-sha256')
    p.add_argument('--seconds',type=float,default=80);p.add_argument('--output',type=Path,required=True)
    a=p.parse_args()
    if a.output.exists():raise FileExistsError(a.output)
    r=run(a);a.output.parent.mkdir(parents=True,exist_ok=True)
    with a.output.open('x') as f:json.dump(r,f,sort_keys=True,separators=(',',':'));f.write('\n')
    print(r['status'],r['completed_projectors'],digest(a.output.read_bytes()))
    if r['status']=='bounded_incomplete':raise SystemExit(2)

if __name__=='__main__':main()
