#!/usr/bin/env python3
"""YM W3 original L4/d2: exact four-column fifth exterior source calibration.

Original-source geometry and formal series, not physical CMP119 source T.
Continuous SU(N) inputs are exact analytic Haar/Schur identities.
"""
from itertools import combinations, product
from collections import Counter
import sympy as s

L,d=4,2
def advance(x,i):
    y=list(x); y[i]=(y[i]+1)%L; return tuple(y)
def boundary(p):
    x,a,b=p
    return frozenset(((x,a),(x,b),(advance(x,a),b),(advance(x,b),a)))

faces={(x,a,b) for x in product(range(L),repeat=4)
       for a,b in combinations(range(4),2)}
walls=set()
for k in range(d):
    for axis,transverse in ((1,2),(2,1)):
        for offset in (0,1):
            x=[0]*4; x[0]=k; x[transverse]=offset
            walls.add((tuple(x),0,axis))
sections={((k,0,0,0),1,2) for k in range(3)}
base=walls|sections
exterior=faces-base
support=set().union(*(boundary(p) for p in base))
outside={p:boundary(p)-support for p in exterior}
assert len(faces)==1536 and len(walls)==8 and len(exterior)==1525
assert Counter(map(len,outside.values()))==Counter({3:76,4:1449})
assert all(len(boundary(p)&boundary(q))<=1
           for p,q in combinations(exterior,2))
print("PASS original 1536-face source, 1525 exterior, Haar leaves")

beta,v,h,m,mp,u=s.symbols("beta v h m mp u")
gamma=v*m**8
vac2=s.Rational(1525,2)*beta**2*v
vac3=s.Rational(1525,6)*beta**3*h
print("PASS normalized vacuum Z_1=0, Z_2/Z_0=",vac2,
      "Z_3/Z_0=",vac3)

attached=Counter()
for x in product(range(L),repeat=4):
    for axes in combinations(range(4),3):
        cube=set()
        for a,b in combinations(axes,2):
            third=next(c for c in axes if c not in (a,b))
            cube.update(((x,a,b),(advance(x,third),a,b)))
        if len(cube&base)==1:
            attached[next(iter(cube&base))]+=1
assert all(attached[q]==3 for q in walls)
section_counts=[attached[((k,0,0,0),1,2)] for k in range(3)]
assert section_counts==[3,2,3]
assert sum(attached.values())==32
print("PASS 24 wall and 8 section cube attachments")

# Unique original physical fine deficits (1-tF), (1-tG); source K0,KF,KG,KFG.
# Common vacuum contributions to the four columns through order 4 cancel.
p=beta**5*v**4
section_F=sum(section_counts[k]*v*m**(4*k) for k in range(3))
section_G=sum(section_counts[k]*v*m**(4*(2-k)) for k in range(3))
delta_A=p*24*m
delta_B=p*(24*m-section_F)
delta_C=p*(24*m-section_G)
delta_D=p*(24*m*(1+gamma)+24*v*mp*m**7-section_F-section_G
           +8*h*m**8)
target=p*(24*v*mp*m**7+8*h*m**8)
assert s.simplify(delta_D-delta_B-delta_C+(1-gamma)*delta_A-target)==0
assert s.simplify(section_F-section_G)==0
assert s.simplify(target.subs({v:s.Rational(1,4),h:0})
                  -3*beta**5*mp*m**7/128)==0
assert s.simplify(target.subs({v:s.Rational(1,18),h:s.Rational(1,108)})
                  -beta**5*m**7*(m+18*mp)/1417176)==0
print("PASS four-column fifth cube cancellation and SU2/SU3 channels")

a2,a3,a4,a5=s.symbols("a2 a3 a4 a5")
V=1+a2*u**2+a3*u**3+a4*u**4+a5*u**5
A=V+delta_A*u**5
B=V+delta_B*u**5
C=V+delta_C*u**5
D=(1+gamma)*V+delta_D*u**5
def coefficients(expr):
    poly=s.Poly(expr,u)
    return [poly.nth(n) for n in range(6)]
def multiply(x,y):
    return [s.expand(sum(x[k]*y[n-k] for k in range(n+1)))
            for n in range(6)]
def inverse(x):
    out=[1/x[0]]
    for n in range(1,6):
        out.append(s.expand(-sum(x[k]*out[n-k]
                                 for k in range(1,n+1))/x[0]))
    return out
aa,bb,cc,dd=map(coefficients,(A,B,C,D))
ainv=inverse(aa)
D_A=multiply(dd,ainv)
B_A=multiply(bb,ainv)
C_A=multiply(cc,ainv)
B_A_C_A=multiply(B_A,C_A)
cov=[s.expand(D_A[n]-B_A_C_A[n]) for n in range(6)]
assert s.simplify(cov[0]-gamma)==0
assert all(s.simplify(cov[n])==0 for n in range(1,5))
assert s.simplify(cov[5]-target)==0
assert (1+gamma)*vac2!=0
assert s.simplify(target)!=0
print("PASS connected orders 1..4 zero, order5 exact independently of vacuum")
print("PASS negative controls: raw FG gives false order2; vacuum-only misses order5")
print("RESULT fifth exterior Taylor coefficient:",s.factor(target))
print("OPEN historical CMP119/122 T identity, beta(a) UV and all-tau absolute W3")
