#!/usr/bin/env python3
"""Exact nonvanishing Weil trace and full-sector Fourier deconvolution.

Reuse the original signed kernel and determinant normalization. On the
zero-affine phase-preserving chart conjugation permutes the Weyl basis of
End(H), so |tr K(g)|^2 = |ker(M_g-I)|. No ambient vacuum projector sum.
"""
import argparse,json,hashlib
from pathlib import Path
from fractions import Fraction as F
import numpy as np
from monster3b_exact_weil_covariance import (atlas_chart,labels,covariance,
    canonical_record,mul,power,red,require,ROOTS)
from monster3b_atlas_generation_certificate import inv
from toe_cyclotomic_operator import rank

WORDS={'identity':'','J':'CC','D':'D','E':'CDc','DE':'DCDc','R':'cdcdcddcdd','Q':'CDCDD'}
def add(a,b):return a[0]+b[0],a[1]+b[1]
def pack(a):return [str(x) for x in a]
def norm(a):return a[0]*a[0]-a[0]*a[1]+a[1]*a[1]
def word(w,C,D):
    M=np.eye(len(C),dtype=np.int64);ops={'C':C,'c':inv(C),'D':D,'d':inv(D)}
    for x in w:M=M@ops[x]%3
    require(sum(x in 'Cc' for x in w)%2==0,'outer word has no same-phase trace')
    return M

def weil_trace(M,s):
    Q,r=labels(M,1,s);neg=covariance(Q,M,1,s)
    c=canonical_record(Q,r,neg);scale=tuple(map(F,c['normalized_vacuum_Qzeta3']))
    diag=np.diag(Q);counts=[int(np.count_nonzero(diag==k)) for k in range(3)]
    raw=(counts[0]-counts[2],counts[1]-counts[2]);trace=mul(scale,raw)
    fixed=len(M)-rank((M-np.eye(len(M),dtype=np.int64))%3)
    require(norm(trace)==3**fixed,'Weyl adjoint trace norm residual')
    require(red(trace)!=0,'Weil trace not a local unit at 31')
    return trace,dict(fixed_dimension=fixed,norm_squared=3**fixed,
                      diagonal_root_counts=counts,trace_Qzeta3=pack(trace),trace_mod31=red(trace),normalization=c)

def multiplicity_trace(ambient,s,weil):
    """Ambient entries are FULL W traces of h, z h, z² h in this order."""
    t=(F(0),F(0))
    for k,v in enumerate(ambient):t=add(t,mul((F(v,3),F(0)),ROOTS[(-s*k)%3]))
    return mul(t,power(weil,-1))

def run(root,cover=None):
    if cover:
        c=json.loads(cover.read_text());require(c.get('actual_mmgroup_used') is True,'literal cover required')
        for g,l in (('C',2),('D',1)):
            q=c['canonical_'+g];require(q['central_multiplier_mod3']==l and not any(q['affine_ell_F3']),'literal affine chart residual')
        C,D=(np.asarray(c['canonical_'+g]['matrix_F3'],dtype=np.int64) for g in ('C','D'))
    else:C,D=atlas_chart(root)
    records={}
    for name,w in WORDS.items():
        M=word(w,C,D)
        for s in (1,2):
            t,r=weil_trace(M,s);records[f'{name}:{s}']=r
            if name=='J':require(t==(1,0),'canonical parity trace not one')
            if name=='identity':require(t==(729,0),'canonical identity trace')
    # Exact forward/reverse Fourier controls, retaining the phase-zero trace.
    z0=(F(11),F(0));x=(F(2),F(3));y=(F(-1),F(4))
    t=(F(1),F(2));u=mul(t,x);v=mul(t,y)
    # The synthetic full ambient trace need not be integer, so separately
    # choose a rational character-shaped conjugate pair for this control.
    a=(F(5),F(2));b=(a[0]-a[1],-a[1]);u=mul(t,a);v=(u[0]-u[1],-u[1]);ambient=[]
    for k in range(3):
        q=add(z0,add(mul(ROOTS[k],u),mul(ROOTS[(-k)%3],v)))
        require(q[1]==0,'rational synthetic trace');ambient.append(q[0])
    require(multiplicity_trace(ambient,1,t)==a and multiplicity_trace(ambient,2,(t[0]-t[1],-t[1]))==b,'Fourier inverse residual')
    return dict(status='EXACT_WEIL_TRACE_NORM_SOURCE_REPLAY',source_chart='literal cover matrices' if cover else 'pinned ATLAS chart',
                cover_sha256=hashlib.sha256(cover.read_bytes()).hexdigest() if cover else None,
                records=records,exact_nonzero_norm_checks=len(records),actual_ambient_character_replayed=False)

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--root',type=Path,default=Path(__file__).resolve().parents[1]);p.add_argument('--cover',type=Path);p.add_argument('--out',type=Path);a=p.parse_args()
    r=run(a.root,a.cover)
    if a.out:a.out.parent.mkdir(parents=True,exist_ok=True);a.out.write_text(json.dumps(r,indent=2)+'\n')
    print(json.dumps(r,indent=2))
if __name__=='__main__':main()
