#!/usr/bin/env python3
"""Original side-four six-plane Wilson n=3/native Q8 exact source regression.

Checks original signed 4-step plaquettes, independent explicit positive-link
formula, original spatial xyz C3, link orientation/time mirror, gauge action.
No Agda, continuous SU(N) Haar, OS or mass-gap claim.
"""
from itertools import product, combinations
from random import Random
import sympy as sp
from sympy.combinatorics import Permutation

L = 4
site_list = tuple(product(range(L), repeat=4))
axes = range(4)
planes = tuple(combinations(axes, 2))
bond_list = tuple((*s, a) for s in site_list for a in axes)
pos = {k:i for i,k in enumerate(bond_list)}
assert len(site_list) == 256 and len(planes) == 6 and len(bond_list) == 1024
Q = tuple((s, a) for s in (1,-1) for a in range(4))
# i*j=k, j*i=-k; exact quaternion signed multiplication
T = (((1,0),(1,1),(1,2),(1,3)),
     ((1,1),(-1,0),(1,3),(-1,2)),
     ((1,2),(-1,3),(-1,0),(1,1)),
     ((1,3),(1,2),(-1,1),(-1,0)))
def qmul(a,b):
    s,k=T[a[1]][b[1]]
    return (a[0]*b[0]*s,k)
def qinv(a): return a if a[1]==0 else (-a[0],a[1])
def re_trace(a): return sp.Integer(a[0] if a[1] == 0 else 0)
def shift(site,axis,delta=1):
    s=list(site);s[axis]=(s[axis]+delta)%L;return tuple(s)
def rotate_site(s): t,x,y,z=s; return (t,z,x,y)
def rotate_axis(a):return (0,2,3,1)[a]
def rotate_bond(b):return (*rotate_site(b[:4]),rotate_axis(b[4]))
def mirror_site(s):return ((-s[0])%L,*s[1:])
def mirror_bond(b):
    s,a=b[:4],b[4]
    reflected=mirror_site(s)
    return ((*shift(reflected,0,-1),a),-1) if a==0 else ((*reflected,a),1)
def transform(field, sigma): return {b:field[sigma(b)] for b in bond_list}
def rotate_field(field):return transform(field,rotate_bond)
def mirror_field(field):
    result={}
    for b in bond_list:
        src,sgn=mirror_bond(b)
        result[b] = qinv(field[src]) if sgn < 0 else field[src]
    return result

def path_plaquette(field,s,a,b):
    # Original Balaban path: +a,+b,-a,-b. Native signed orientation on
    # negative steps uses inverse of positive link at shifted start.
    steps=((a,1),(b,1),(a,-1),(b,-1))
    cur=s
    val=(1,0)
    for axis,sgn in steps:
        if sgn>0:
            q=field[(*cur,axis)]
            cur=shift(cur,axis)
        else:
            cur=shift(cur,axis,-1)
            q=qinv(field[(*cur,axis)])
        val=qmul(val,q)
    assert cur==s
    return val

def explicit_plaquette(field,s,a,b):
    # Independent four-factor formula; no path recursion.
    return qmul(qmul(qmul(field[(*s,a)],field[(*shift(s,a),b)]),
                     qinv(field[(*shift(s,b),a)])),qinv(field[(*s,b)]))

def variable_site(field,s):
    # n=3 variable source: six original owned plaquettes.
    return sum((sp.Integer(1)-re_trace(path_plaquette(field,s,a,b))
                 for a,b in planes), sp.Integer(0))
def native_site(field,s):
    return sum((sp.Integer(1)-re_trace(explicit_plaquette(field,s,a,b))
                 for a,b in planes), sp.Integer(0))
def variable_deficit(field):
    return sum((variable_site(field,s) for s in site_list),sp.Integer(0))
def native_deficit(field):
    # Native sumSitesReal: four nested C4 sums.
    return sum((sum((sum((sum((native_site(field,(t,x,y,z))
                    for z in axes),sp.Integer(0)) for y in axes),sp.Integer(0))
                    for x in axes),sp.Integer(0)) for t in axes),sp.Integer(0))
def gauge_field(field,gauge):
    return {(*s,a):qmul(qmul(gauge[s],field[(*s,a)]),
                     qinv(gauge[shift(s,a)])) for s in site_list for a in axes}
def plane_weighted(field,weight):
    return sum((sp.Integer(weight[a,b]) *
        (1-re_trace(path_plaquette(field,s,a,b)))
        for s in site_list for a,b in planes),sp.Integer(0))

def check():
    counts={}
    def ok(label,predicate):
        assert predicate,label
        counts[label]=counts.get(label,0)+1
    assert sp.__version__ == "1.14.0"
    for q in Q: ok('Q8 inverses',qmul(q,qinv(q))==(1,0))
    ok('Q8 noncommutativity',qmul((1,1),(1,2)) != qmul((1,2),(1,1)))
    br=Permutation([pos[rotate_bond(b)] for b in bond_list])
    bm=Permutation([pos[mirror_bond(b)[0]] for b in bond_list])
    ok('C3 bond permutation order',br.order()==3)
    ok('mirror bond permutation order',bm.order()==2)
    ok('bond index commutator',br*bm==bm*br)
    for b in bond_list:
        ok('C3^3 on native bonds',rotate_bond(rotate_bond(rotate_bond(b)))==b)
        m,sgn=mirror_bond(b); m2,sgn2=mirror_bond(m)
        ok('mirror^2 on oriented bonds',m2==b and sgn*sgn2==1)
        m,sgn=mirror_bond(b)
        n,sgn2=mirror_bond(rotate_bond(b))
        ok('S theta bond+inverse commutator',rotate_bond(m)==n and sgn==sgn2)
    rng=Random(20261122)
    fields=[]
    # One highly noncommutative non-uniform random field per deterministic seed.
    for trial in range(8):
        field={b:Q[rng.randrange(8)] for b in bond_list}
        fields.append(field)
        rf=rotate_field(field);mf=mirror_field(field)
        ok('field rotation-mirror commute',mirror_field(rf)==rotate_field(mf))
        ok('field S^3',rotate_field(rotate_field(rf))==field)
        ok('field theta^2',mirror_field(mf)==field)
        # Independent native product and original signed plaquette at ALL 6*256 faces.
        for s in site_list:
            ok('same original site six-deficit',variable_site(field,s)==native_site(field,s))
            for a,b in planes:
                ok('same original signed vs explicit plaquette',
                   path_plaquette(field,s,a,b)==explicit_plaquette(field,s,a,b))
                ok('Wilson C3 plaquette real trace',
                   re_trace(path_plaquette(rf,s,a,b))==
                   re_trace(path_plaquette(field,rotate_site(s),rotate_axis(a),rotate_axis(b))))
        av=variable_deficit(field);an=native_deficit(field)
        ok('n=3 original variable/native full action',av==an)
        ok('native Wilson C3 action',av==variable_deficit(rf))
        ok('original Wilson theta action',av==variable_deficit(mf))
        gauge={s:Q[rng.randrange(8)] for s in site_list}
        ok('native local SU2 gauge action',av==variable_deficit(gauge_field(field,gauge)))
        beta=sp.Rational(5,7)
        ok('n=3 original literal density',sp.exp(-beta*av)==sp.exp(-beta*an))
    # Negative controls: time/space mixing does NOT commute with theta,
    # and anisotropic plane couplings generally violate spatial C3.
    def wrong_swap(b):
        t,x,y,z,a=b
        return (x,t,y,z,(1,0,2,3)[a])
    ok('negative control: time-space swap geometry rejected',
       any((lambda m: wrong_swap(m[0]))(mirror_bond(b)) != mirror_bond(wrong_swap(b))[0]
           for b in bond_list))
    weights={p:(1 if p==(0,1) else 3 if p==(0,2) else 2) for p in planes}
    ok('negative control: anisotropic Wilson C3 rejected',
       any(plane_weighted(f,weights)!=plane_weighted(rotate_field(f),weights) for f in fields))
    return counts

if __name__=='__main__':
    counts=check()
    print('SymPy',sp.__version__)
    print('Original 4^4 sites = 256; positive bonds = 1024; six-plane plaquettes = 1536')
    for k,v in counts.items():print(f'{k}: {v}/{v} PASS')
    print('TOTAL',sum(counts.values()),'/',sum(counts.values()),'PASS')
