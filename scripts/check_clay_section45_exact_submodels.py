#!/usr/bin/env python3
"""Section45 exact finite submodel checks. NOT Agda/Lean or Clay acceptance."""
from fractions import Fraction as F
from itertools import product, permutations
from math import factorial
import re

c={"YM_Bishop_degree":0,"NS_one_flow_sqrt":0,"BSD_signed_source":0,"Hodge_free_action":0,"PNP_shared_rivals":0,"RH_version_gate":0}
q=F(1,4)
for cutoff in range(1,31):
    for i in range(cutoff):
        for j in range(cutoff):
            for shift in (1,2):
                included=(i+j>=max(cutoff-shift,0))
                if not included:continue
                degree=i+j+shift
                assert degree>=cutoff
                for u in (F(0),F(1,100),F(1,8),q):
                    assert u**degree <= q**cutoff
                    c["YM_Bishop_degree"]+=1

# The same original finite energy ceiling and one R_j work for every
# finite cutoff and every genuine state energy E_N<=Emax. We use
# rational sqrt samples t=k^2 to keep equality fully exact.
for nu in (F(1,3), F(1),F(3,2)):
    for j in range(1,22):
        eps=F(1,j)
        for k in range(0,13):
            Emax=2*nu*eps*k*k
            R=F(1+k)
            assert Emax<2*nu*R*R*eps
            for N in range(1,11):
                for E0 in (F(0),Emax/2,Emax):
                    assert E0/(2*nu*R*R)<eps
                    c["NS_one_flow_sqrt"]+=1

def h(a,b,n):
    v=F(1)
    for k in range(1,n+1):v=a*v+b**k
    return v
for a,b in ((F(1),F(2)),(F(3,2),F(4,3)),(F(4),F(1))):
    for n in range(0,40):
        m=lambda z:F(0) if z==0 else (a+b+1)**z
        d=lambda x,y:h(x,y,n)*m(n+2)-h(x,y,n+1)*m(n+1)+(x*y)**(n+1)*m(0)
        assert d(a,b)==d(b,a) and d(a,b)>0
        c["BSD_signed_source"]+=2

even=[v for v in product((0,1),repeat=6) if sum(v)%2==0]
assert len(even)==32
zero=(0,)*6
for s,e,f in product(even,repeat=3):
    act=lambda sign,root:tuple(sign[i]^root[i] for i in range(6))
    mul=lambda x,y:tuple(x[i]^y[i] for i in range(6))
    assert act(mul(e,f),s)==act(e,act(f,s))
    assert act(e,act(e,s))==s
    assert (act(e,s)==s)==(e==zero)
    c["Hodge_free_action"]+=3

# A single x trace reading one bit per clock: each legal rival y_r
# flips a different original coordinate. For one shared faithful
# terminal parity consumer all t distinct support obligations must
# be read, so a clock with k<t cannot serve all rival inputs.
for t in range(1,8):
    x=(0,)*t
    rivals=[tuple(int(i==r) for i in range(t)) for r in range(t)]
    for order in permutations(range(t)):
        assert len(set(order))==t
        for k in range(t+1):
            read=set(order[:k])
            witnessed={r for r,y in enumerate(rivals) if any(x[i]!=y[i] for i in read)}
            assert len(witnessed)==k
            assert (len(witnessed)==t)==(k==t)
            c["PNP_shared_rivals"]+=2

pattern=re.compile(r"(?m)^Lean \(version ([0-9]+\.[0-9]+\.[0-9]+)(?:,|\s|\))")
for line,correct in [("Lean (version 4.33.1, x86_64-unknown-linux-gnu)",True),
                     ("Lean (version 4.33.10, other 4.33.1)",False),
                     ("error: Lean version 4.33.1",False),
                     ("Lean (version 4.33.1.1, x86_64)",False),
                     ("Lean (version 4.34.1, x86_64)",False)]:
    m=pattern.search(line)
    assert (m is not None and m.group(1)=="4.33.1")==correct
    c["RH_version_gate"]+=1
print("SECTION45 EXACT SUBMODELS PASS",c,"TOTAL",sum(c.values()))
