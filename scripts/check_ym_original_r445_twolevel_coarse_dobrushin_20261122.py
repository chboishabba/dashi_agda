#!/usr/bin/env python3
"""Exact original Wilson R445 two-level conditional/coarse Dobrushin source check.
Only original full 4D plaquette geometry + SymPy; SU(N) Haar/Dobrushin
mathematics uses classical comparison, not a numerical quadrature/Agda proof.
Weak-coupling CMP119/122 physical W3, continuum mass gap remain OPEN.
"""
from itertools import product,combinations
from collections import Counter,defaultdict
from fractions import Fraction as Q
import sympy as sp

def verify(L):
    assert L>=4 and L%2==0
    pts=list(product(range(L),repeat=4))
    def inc(x,i):
        a=list(x);a[i]=(a[i]+1)%L;return tuple(a)
    original={(x,i) for x in pts for i in range(4)}
    first={(x,i) for x in pts if all(v%2==0 for v in x) for i in range(4)}
    pairs={a:frozenset((a,(inc(a[0],a[1]),a[1]))) for a in first}
    selected=set().union(*pairs.values())
    owner={b:('V',i) for i,ps in pairs.items() for b in ps}
    for b in original-selected:owner[b]=('S',b)
    assert len(owner)==len(original)==4*L**4
    n=defaultdict(Counter);m=defaultdict(Counter);degree=Counter()
    face_first=Counter(); faces=set()
    for x in pts:
        for i,j in combinations(range(4),2):
            p=frozenset(((x,i),(inc(x,i),j),(inc(x,j),i),(x,j)))
            faces.add(p);v={owner[b] for b in p}; assert len(v)==4
            active=p&first; assert len(active)<=2
            face_first[len(active)]+=1
            for a in v:degree[a]+=3
            for a in active:
                for z in v:n[a][z]+=1
                for b in active:
                    if a!=b:m[a][b]+=1
    assert len(faces)==6*L**4
    assert len(pairs)==4*(L//2)**4 and len(selected)==2*len(pairs)
    assert len(degree)==len(original)-len(pairs)
    assert all(degree[a]==(36 if a[0]=='V' else 18) for a in degree)
    assert all(sum(n[i].values())==24 and len(n[i])==19 for i in first)
    assert all(sum(m[i].values())==3 and set(m[i].values())=={1} for i in first)
    overlap={v:sum(n[i][v] for i in first) for v in degree}
    hist=Counter((v[0],k) for v,k in overlap.items())
    assert all(overlap[v]==12 for v in degree if v[0]=='V')
    assert all(overlap[v]<=3 for v in degree if v[0]=='S')
    assert max(overlap.values())==12
    assert sum(degree.values())==18*len(original)
    return len(original),len(faces),len(pairs),len(degree),face_first,hist

a=verify(4);b=verify(6)
assert a[:4]==(1024,1536,64,960)
assert b[:4]==(5184,7776,324,4860)
assert a[4]==Counter({0:1248,1:192,2:96})
assert a[5]==Counter({('S',0):512,('S',1):192,('S',3):192,('V',12):64})
beta=Q(1,72)
qf=36*beta
qc=3*beta+1152*beta**2/(1-qf)
assert qf==Q(1,2) and qc==Q(35,72)<Q(1,2)
assert (4*beta*3+16*beta**2*24*12/(1-qf))/4==qc
assert sp.simplify(sp.tanh(sp.Rational(1,72))-sp.Rational(1,72))<0

# Source log-corner identity: if original faces share TWO changed first
# links, the intrinsic J=H11-H10-H01+H00 MUST be retained.
u,v,lam=sp.symbols('u v lam',real=True)
Z=2*sp.exp(lam*u*v)
assert sp.simplify(sp.diff(sp.log(Z),u,v)-lam)==0
assert sp.simplify(
  sp.log(Z.subs({u:1,v:1}))-sp.log(Z.subs({u:1,v:0}))
  -sp.log(Z.subs({u:0,v:1}))+sp.log(Z.subs({u:0,v:0}))-lam)==0

print('PASS original full Wilson native L4 and even-origin L6:',a,b)
print('PASS exact direct source sum_j m_ij=3 and max_a sum_j n_j(a)=12')
print('PASS original conditional q_f<=36 tanh(beta)<=1/2 for beta<=1/72')
print('PASS induced coarse q_c<=3beta+1152 beta^2/(1-36tanh beta)<=35/72')
print('PASS intrinsic shared-face mixed Hessian negative control (not just Cov)')
print('NOT CLAIMED: original globally-marked coarse W1 contraction, CMP119/122 weak-coupling W3, E1/D2, Agda kernel or CI')
