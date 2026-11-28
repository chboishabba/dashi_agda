"""Exact phase-indexed composition of actual characteristic-zero factors.

Use the existing actual two-phase factors. Weyl column action is
matrix-free; a common-denominator integer matrix represents the
90x90 multiplicity part. The projective scalar is transferred at each
composition, not set to one. Checkpoint only completed word letters.
"""
import argparse
from fractions import Fraction as F
from math import lcm,gcd
from pathlib import Path
from time import monotonic
import json
import numpy as np
from scripts.x369_3b_cyclotomic_rank import Q,ONE,ZERO,PHASE
from scripts.x369_3b_cyclotomic_normalizer import WEIGHTS,reference
from scripts.x369_3b_nonzero_weyl_trace import column_coords,coefficient,nonzero_trace,make_word
from scripts.x369_actual_3b_normalizer_tensor import source_coords
from scripts.monster_3b_mmgroup_checkpointed_weyl import read_pinned
from scripts.monster_3b_mmgroup_weyl_word_alignment import check_words
from scripts.x369_3b_cyclotomic_projector import digest
from scripts.x369_actual_weyl_frame_bidi import require

ROOT=Path(__file__).resolve().parent
OWNERS=('x369_3b_cyclotomic_word_factor.py','x369_3b_cyclotomic_normalizer.py',
        'x369_3b_cyclotomic_rank.py','x369_3b_nonzero_weyl_trace.py')


class Mat:
    """Exact common denominator Q(omega) matrix."""
    def __init__(self,a,b,d):
        require(type(d) is int and d>0 and a.shape==b.shape and a.ndim==2,'matrix scope')
        self.a=a;self.b=b;self.d=d
        g=d
        for x in (*a.flat,*b.flat):
            g=gcd(g,int(x))
            if g==1:break
        if g>1:self.a=a//g;self.b=b//g;self.d=d//g

    @classmethod
    def read(cls,rows):
        q=[[Q.wire(x) for x in row] for row in rows]
        require(bool(q) and all(len(row)==len(q[0]) for row in q),'matrix dimensions')
        d=1
        for row in q:
            for x in row:d=lcm(d,x.a.denominator,x.b.denominator)
        return cls(np.array([[int(v.a*d) for v in row] for row in q],dtype=object),
                   np.array([[int(v.b*d) for v in row] for row in q],dtype=object),d)

    @classmethod
    def identity(cls,n):
        return cls(np.eye(n,dtype=object),np.zeros((n,n),dtype=object),1)

    def mul(self,o):
        a,b,c,d=self.a,self.b,o.a,o.b
        bd=b@d
        return Mat(a@c-bd,a@d+b@c-bd,self.d*o.d)

    def scale(self,q):
        d=lcm(q.a.denominator,q.b.denominator)
        a,b=int(q.a*d),int(q.b*d)
        return Mat(self.a*a-self.b*b,self.a*b+self.b*a-self.b*b,self.d*d)

    def trace(self):
        return Q(F(sum(self.a.diagonal()),self.d),F(sum(self.b.diagonal()),self.d))

    def wire(self):
        return [[Q(F(x,self.d),F(y,self.d)).pack() for x,y in zip(a,b)] for a,b in zip(self.a,self.b)]

    def same(self,o):
        return (self.a.shape==o.a.shape and np.array_equal(self.a*o.d,o.a*self.d)
                and np.array_equal(self.b*o.d,o.b*self.d))


def apply_reference(phi,aa,phase,v,deadline=None):
    require(len(v)==len(phi)==729,'reference size')
    cols=column_coords(aa);out=[ZERO]*729
    for c,g in zip(v,cols):
        if not c:continue
        if deadline is not None and monotonic()>=deadline:raise TimeoutError('Weyl composition budget')
        for i,u in enumerate(WEIGHTS):
            w=coefficient(phi,g,u,phase)
            if w:out[i]=out[i]+c*w
    return out


def normalize(phi,M):
    i=next(i for i,v in enumerate(phi) if v);s=phi[i]
    return [x*s.inv() for x in phi],M.scale(s),s,WEIGHTS[i]


def run(a):
    from mmgroup import MM
    from importlib.metadata import version
    deadline=monotonic()+a.seconds
    local=read_pinned(a.local,a.local_sha256);m=local['actual_local_sources']['ternary_manifest']
    checked=check_words(m)
    z=MM(m['center_word']);A=[MM(w) for w in m['translation_words']];B=[MM(w) for w in m['modulation_words']]
    words={r['name']:MM(r['word']) for r in m['normalizer_lifts']}
    manifest=read_pinned(a.factors,a.factors_sha256)
    require(type(manifest) is list and len(manifest)==2*len(words),'actual all-phase factor manifest')
    factors={};frames={}
    for row in manifest:
        f=read_pinned(a.factors.parent/row['path'],row['sha256'])
        mod=read_pinned(a.factors.parent/row['modular_path'],row['modular_sha256'])
        c=f['scope'];mc=mod['contract'];name=c['lift'];p=c['source_zeta'];q=c['target_zeta']
        require(name in words and p in (2,4) and q in (2,4) and
                f['status']=='actual_cyclotomic_normalizer_factor' and f['all_90_actual_columns_reduced'] is True and
                mod['status']=='actual_MMV7_normalizer_tensor_factor' and mc['lift']==name and
                c['modular_factor_sha256']==row['modular_sha256'] and c['local_sha256']==a.local_sha256 and
                mc['local_sha256']==a.local_sha256 and mc['source_manifest_sha256']==checked['manifest_sha256'] and
                mc['source_zeta']==p and mc['target_zeta']==q and MM(mc['word'])==words[name],
                'actual factor scope')
        for phase,key in ((p,'source_rank_sha256'),(q,'target_rank_sha256')):
            require(phase not in frames or frames[phase]==c[key],'inconsistent exact phase rank frame')
            frames[phase]=c[key]
        h=words[name];aa=[source_coords(h**-1*g*h,z,A,B) for g in A]
        bb=[source_coords(h**-1*g*h,z,A,B) for g in B]
        require(h**-1*z*h==z**(1 if p==q else 2),'actual phase')
        phi=[Q.wire(v) for v in f['reference_phi']]
        require(phi==reference(bb,1 if q==2 else 2,mod['normalization_weight']),
                'exact source reference')
        require([v.mod7() for v in phi]==mod['reference_phi'],'actual reference reduction')
        M=Mat.read(f['multiplicity_matrix'])
        require(M.a.shape==(90,90) and [[Q.wire(v).mod7() for v in r] for r in f['multiplicity_matrix']]==mod['multiplicity_matrix'],
                'actual multiplicity reduction')
        require((name,p) not in factors,'duplicate phase factor')
        factors[name,p]=(q,phi,aa,M)
    require(set(factors)=={(n,p) for n in words for p in (2,4)},'complete source phases')
    seq=a.word.split(',')
    require(bool(seq) and all(n in words for n in seq),'positive literal source word')
    contract=dict(local_sha256=a.local_sha256,factors_sha256=a.factors_sha256,
        start_zeta=a.zeta,word=seq,mmgroup_version=version('mmgroup'),
        owners={n:digest((ROOT/n).read_bytes()) for n in OWNERS})
    phi=[ONE]+[ZERO]*728;M=Mat.identity(90);p=a.zeta;h=MM(1);cursor=0;scalars=[]
    if a.resume:
        r=read_pinned(a.resume,a.resume_sha256)
        require(r['contract']==contract and r['status']=='bounded_incomplete','source resume')
        cursor=r['cursor'];require(0<=cursor<=len(seq),'word cursor')
        for name in seq[:cursor]:h=h*words[name];p=factors[name,p][0]
        require(MM(r['actual_prefix_word'])==h and r['target_zeta']==p,'actual source prefix')
        phi=[Q.wire(x) for x in r['reference_phi']];M=Mat.read(r['multiplicity_matrix']);scalars=r['composition_scalars']
        bb=[source_coords(h**-1*g*h,z,A,B) for g in B]
        require(phi==reference(bb,1 if p==2 else 2,WEIGHTS[next(i for i,x in enumerate(phi) if x)]),
                'resumed reference changed')
    while cursor<len(seq):
        if monotonic()>=deadline:break
        name=seq[cursor];q,base,aa,N=factors[name,p]
        try:w=apply_reference(base,aa,1 if q==2 else 2,phi,deadline)
        except TimeoutError:break
        v,D,s,k=normalize(w,N.mul(M));g=h*words[name]
        bb=[source_coords(g**-1*x*g,z,A,B) for x in B]
        require(v==reference(bb,1 if q==2 else 2,k),'whole source word reference covariance')
        phi,M,p,h=v,D,q,g;cursor+=1;scalars.append(s.pack())
    complete=cursor==len(seq)
    identity_checked=False
    if complete and h==MM(1):
        require(p==a.zeta and phi==[ONE]+[ZERO]*728 and M.same(Mat.identity(90)),
                'actual identity word factor mismatch')
        identity_checked=True
    witness=None
    if complete and p==a.zeta and monotonic()<deadline:
        aa=[source_coords(h**-1*g*h,z,A,B) for g in A]
        try:coord,t,o,n=nonzero_trace(phi,aa,1 if p==2 else 2,deadline)
        except TimeoutError:pass
        else:
            e=make_word(coord,z,A,B);w=h*e;tr=M.trace()
            witness=dict(status='actual_source_nonzero_Weyl_trace_witness',local_sha256=a.local_sha256,
                factor_manifest_sha256=a.factors_sha256,phase=1 if p==2 else 2,zeta=p,word=str(h),
                offset_coordinates=coord,offset_word=str(e),offset_product_word=str(w),center_word=str(z),
                central_shift_words=[str(w*z**i) for i in range(3)],
                ordinary_normalized_Weyl_trace=o.pack(),offset_normalized_Weyl_trace=t.pack(),
                normalized_multiplicity_trace=tr.pack(),normalized_full_phase_trace=(t*tr).pack(),
                modulation_candidates=n,offset_trivial_in_Suzuki_quotient_from_E_word=True,
                source_cover_class_identified=False,characteristic_zero_12_plus_78_certified=False)
    # A phase-closed word can resume just the trace witness if needed.
    finished=complete and (p!=a.zeta or witness is not None)
    return dict(status='actual_cyclotomic_word_factor' if finished else 'bounded_incomplete',
        contract=contract,parent_receipt_sha256=a.resume_sha256,cursor=cursor,target_zeta=p,
        actual_prefix_word=str(h),reference_phi=[x.pack() for x in phi],multiplicity_matrix=M.wire(),
        composition_scalars=scalars,actual_identity_word_checked=identity_checked,
        trace_witness=witness,characteristic_zero_12_plus_78_certified=False)


def main():
    p=argparse.ArgumentParser()
    for n in ('local','factors'):
        p.add_argument('--'+n,type=Path,required=True);p.add_argument('--'+n+'-sha256',required=True)
    p.add_argument('--word',required=True);p.add_argument('--zeta',type=int,choices=(2,4),required=True)
    p.add_argument('--resume',type=Path);p.add_argument('--resume-sha256')
    p.add_argument('--seconds',type=float,default=80);p.add_argument('--output',type=Path,required=True);a=p.parse_args()
    require(0<a.seconds<=90 and bool(a.resume)==bool(a.resume_sha256),'bounded word scope')
    r=run(a);a.output.parent.mkdir(parents=True,exist_ok=True)
    with a.output.open('x') as f:json.dump(r,f,indent=2,sort_keys=True);f.write('\n')
    print(r['status'],r['cursor'],digest(a.output.read_bytes()))
    if r['status']=='bounded_incomplete':raise SystemExit(2)

if __name__=='__main__':main()
