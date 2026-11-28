"""Constructive actual Griess generating-family evaluator from 2A axes.

Reuse Conway/Seysen 196884 basis and the short-vector Q_x0 axis formula.
For a short lattice vector L (integer squared norm 32), the A component
is L L^T / 16, with the two signed short elements giving opposite
short-coordinate components of magnitude 2. Hence their difference
opens the actual short basis vector; their mean gives a rank-one
symmetric tensor. The B/C opposite two-point directions span all 300
symmetric coordinates. Triality sends X to Y and Z with known signs.
No rank-196884 dense Gaussian elimination and no fictitious FLM basis.

Source: Conway 1985, Appendix 6; Seysen arXiv:2002.10921v3,
mmgroup guide section "The Griess algebra product of a vector and an axis",
API MMSpace.index_to_short(_mod2), MMV Axis constructor, triality tables.
The actual coordinate convention is checked at each requested axis.
The rational atom lift is used for translated axes; independent modular
checks are performed on the original mmgroup source.
"""
from fractions import Fraction as F
from functools import lru_cache
from dataclasses import dataclass
import argparse
import hashlib
import json
from pathlib import Path
from time import monotonic
import numpy as np
from scripts.x369_monster_dyadic_source_action import (
    DIM,MODULI,Dyadic,action,require,unit)


@dataclass(frozen=True)
class AxisTerm:
    coefficient: F
    q: int
    triality: int=0


def plus(*terms):
    out={}
    for row in terms:
        for t in row:
            k=t.q,t.triality
            out[k]=out.get(k,F(0))+t.coefficient
    return tuple(AxisTerm(v,*k) for k,v in sorted(out.items()) if v)


def scale(a,terms):
    return tuple(AxisTerm(F(a)*t.coefficient,t.q,t.triality) for t in terms if a*t.coefficient)


def shift(e,terms):
    return tuple(AxisTerm(t.coefficient,t.q,(t.triality+e)%3) for t in terms)


@lru_cache(maxsize=128)
def short_pair(index):
    from mmgroup import MMSpace,MMV,XLeech2
    require(300<=index<98580,'not a short basis coordinate')
    q=XLeech2(MMSpace.index_to_short_mod2('E',index))
    require(int(q.ord)&0xffffff==int(q.ord),'positive short source encoding')
    require(MMSpace.index_to_linear(q)==index,'short source address inverse')
    lam=tuple(map(int,MMSpace.index_to_short('E',index)))
    require(len(lam)==24 and sum(x*x for x in lam)==32,'actual short lattice norm')
    a={}
    for i in range(24):
        for j in range(i+1):
            if lam[i] and lam[j]:
                a[MMSpace.index_to_linear('A',i,j)]=F(lam[i]*lam[j],16)
    # Sign of the named external coordinate is the only convention
    # not fixed by the rank-one tensor formula.
    V=MMV(7);p=V('Axis',q);n=V('Axis',-q)
    k=int(p['E'][index])%7
    require(k in (2,5) and int(n['E'][index])%7==(-k)%7,'actual signed short-axis coefficient')
    signed=2 if k==2 else -2
    for mod in (7,31):
        W=MMV(mod)
        for g,c in ((q,signed),(-q,-signed)):
            expect=np.zeros(DIM,dtype=np.uint8)
            for i,v in a.items():
                expect[i]=(v.numerator*pow(v.denominator,-1,mod))%mod
            expect[index]=c%mod
            require(np.array_equal(np.asarray(W('Axis',g)['E'],dtype=np.uint8)%mod,expect),
                    'actual source axis rank-one formula mismatch')
    return int(q.ord),int((-q).ord),signed,a


def short_terms(index):
    p,n,c,_=short_pair(index)
    return (AxisTerm(F(1,2*c),p),AxisTerm(F(-1,2*c),n))


def short_mean(index):
    p,n,_,_=short_pair(index)
    return (AxisTerm(F(1,2),p),AxisTerm(F(1,2),n))


def symmetric_pair(i,j):
    from mmgroup import MMSpace
    u,v=(i,j) if i>j else (j,i)
    x=MMSpace.index_to_linear('B',u,v);y=MMSpace.index_to_linear('C',u,v)
    _,_,_,a=short_pair(x);_,_,_,b=short_pair(y)
    k=MMSpace.index_to_linear('A',u,v)
    di=MMSpace.index_to_linear('A',i,i);dj=MMSpace.index_to_linear('A',j,j)
    require(a.get(di)==a.get(dj)==b.get(di)==b.get(dj)==1 and
            a.get(k) in (F(-1),F(1)) and b.get(k)==-a[k] and
            set(a)==set(b)=={di,dj,k},'actual two-point short tensor geometry')
    t,m=short_mean(x),short_mean(y)
    return plus(scale(F(1,2),t),scale(F(1,2),m)),plus(scale(F(1,2)/a[k],t),scale(F(-1,2)/a[k],m))


def basis_terms(index):
    from mmgroup import MM,MMV,MMSpace
    require(type(index) is int and 0<=index<DIM,'actual weight-two column')
    tag,i,j=MMSpace.index_to_tuple('E',index)
    if tag=='A':
        if i!=j:return symmetric_pair(i,j)[1]
        j,k=[x for x in range(24) if x!=i][:2]
        return scale(F(1,2),plus(symmetric_pair(i,j)[0],symmetric_pair(i,k)[0],
                                    scale(-1,symmetric_pair(j,k)[0])))
    if tag in ('B','C','T','X'):return short_terms(index)
    require(tag in ('Y','Z'),'unsupported source basis')
    x=MMSpace.index_to_linear('X',i,j)
    V=MMV(7)
    for e in (1,2):
        a=np.asarray((V('X',i,j)*MM('t',e))['E'],dtype=np.uint8)%7
        nz=np.flatnonzero(a)
        require(len(nz)==1 and a[nz[0]] in (1,6),'actual X triality not signed monomial')
        if int(nz[0])==index:
            return scale(1 if a[index]==1 else -1,shift(e,short_terms(x)))
    raise ValueError('actual triality did not recover requested Y/Z column')


def exact_axis(q):
    from mmgroup import MMSpace,XLeech2
    g=XLeech2(q);index=MMSpace.index_to_linear(g)
    p,n,c,a=short_pair(index)
    require(q in (p,n),'axis sign')
    entries=dict(a);entries[index]=F(c if q==p else -c)
    # All source coefficients have power-of-two denominators dividing 16.
    out=np.zeros(DIM,dtype=object)
    for i,v in entries.items():
        n=v*16;require(n.denominator==1,'axis dyadic formula')
        out[i]=n.numerator
    return Dyadic(out,4)


def exact_sum(terms,deadline=None):
    from mmgroup import MM
    out=np.zeros(DIM,dtype=object);power=0
    for t in terms:
        if deadline is not None and monotonic()>=deadline:raise TimeoutError('axis evaluator budget')
        a=exact_axis(t.q)
        if t.triality:a=action(a,MM('t',t.triality),deadline)
        den=t.coefficient.denominator
        require(den&(den-1)==0,'dyadic generating expression')
        p=a.power+den.bit_length()-1
        new=max(power,p)
        out=out*(1<<(new-power))+a.numerator*t.coefficient.numerator*(1<<(new-p))
        power=new
    return Dyadic(out,power)


def modular_sum(terms,p):
    from mmgroup import MM,MMV,XLeech2
    V=MMV(p);v=V(0)
    for t in terms:
        x=V('Axis',XLeech2(t.q))
        if t.triality:x=x*MM('t',t.triality)
        v=v+(t.coefficient.numerator*pow(t.coefficient.denominator,-1,p)%p)*x
    return v


def check_column(index,deadline):
    terms=basis_terms(index)
    require(exact_sum(terms,deadline).same(unit(index)),'actual Griess generating expression fails')
    from mmgroup import MMV,MMSpace
    tag,i,j=MMSpace.index_to_tuple('E',index)
    for p in (7,31):
        require(modular_sum(terms,p)==MMV(p)(tag,i,j),'independent actual axis expansion fails')
    return dict(column=index,source_label=[tag,i,j],
                terms=[dict(coefficient=str(t.coefficient),q=t.q,triality=t.triality) for t in terms])


def run(indices,seconds):
    from importlib.metadata import version
    require(0<seconds<=90,'bounded Griess generating-family scope')
    deadline=monotonic()+seconds;rows=[]
    for i in indices:
        try:rows.append(check_column(i,deadline))
        except TimeoutError:break
    return dict(status='actual_griess_axis_basis_expansion' if len(rows)==len(indices) else 'bounded_incomplete',
        mmgroup_version=version('mmgroup'),columns_requested=len(indices),columns_verified=len(rows),
        rows=rows,source_dimension=DIM,source_generating_family='signed short axes and X triality images',
        all_basis_columns_explicitly_verified=len(rows)==DIM,
        spanning_construction_uses_source_axis_formula=True,
        original_JMD_FLm_basis_alignment_certified=False)


def main():
    p=argparse.ArgumentParser();p.add_argument('--seconds',type=float,default=90)
    p.add_argument('--start',type=int);p.add_argument('--count',type=int)
    p.add_argument('--output',type=Path)
    a=p.parse_args()
    if a.start is None:
        require(a.count is None,'start required for range')
        indices=[0,23,24,299,300,575,576,851,852,49427,49428,98579,98580,147731,147732,196883]
    else:
        require(a.count is not None and 0<=a.start<DIM and 0<a.count<=DIM-a.start,'source column range')
        indices=list(range(a.start,a.start+a.count))
    r=run(indices,a.seconds)
    s=json.dumps(r,indent=2,sort_keys=True)+'\n'
    if a.output:
        a.output.parent.mkdir(parents=True,exist_ok=True)
        with a.output.open('x') as f:f.write(s)
    print(s,end='')
    if r['status']=='bounded_incomplete':raise SystemExit(2)


if __name__=='__main__':main()
