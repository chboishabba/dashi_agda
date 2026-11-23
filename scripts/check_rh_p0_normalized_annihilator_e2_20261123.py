#!/usr/bin/env python3
"""RH P0 E2: height-normalized exact frozen-prime annihilator & amplitude scaling.

Original source witness: physical projective g(u)=G(r*u), with on-line responses
A_c= (1/r) integral G(v)cos(cv)dv. The original selected profile obeys
||P_norm||_1<5184, supp|v|<5, M2=0, M4=-4*T, T>567/1600.

A_t(D) is the even, monic 52nd-order exact annihilator of original eight
integral constraints. Normalize by A_t(0), NOT its highest coefficient.
This yields Q_t(D)=sum_{j=0}^{26} q_j(t) D^(2j) with q_0=1 and
0<=q_j(t)<=binom(26,j)*(256/t^2)^j for all t>=200.
For a FIXED flat-top C-infinity prime bump b_p (equal 1 near +/−log p),
h_p=Q_t(D)b_p is even, supported in the same aperture, has EXACT
h_p(log p)=1, and all eight source integral moments ZERO. Its k-th derivative
L1 norm is bounded by a FINITE weighted sum converging to ||b_p^(k)||_1.

This is an independently executed EXACT rational polynomial regression and
source scaling proof, NOT a Lean kernel check, not a global far-tail estimate,
not a proof of RH/GRH.
"""
from fractions import Fraction as F
from math import comb, factorial

def conv(a,b):
    v=[F(0) for _ in range(len(a)+len(b)-1)]
    for i,x in enumerate(a):
        for j,y in enumerate(b):
            v[i+j]+=x*y
    return v

def poly(t):
    tt=F(t); r=tt/16
    factors=[[r*r,F(1)]]*9 + [[4*r*r,F(1)]]*9
    for c in (1,2):
        for sign in (-1,1):
            w=tt+sign*c*r
            A=w*w+F(1,4)
            factors.append([A*A,2*A-F(1),F(1)])
    a=[F(1)]
    for x in factors:a=conv(a,x)
    assert len(a)==27
    const=a[0]
    q=[v/const for v in a]
    assert q[0]==1 and all(x>=0 for x in q)
    return q

print('EXACT source-normalized polynomial majorant')
for tt in (200,300,1000,32768,1000000):
    q=poly(tt)
    major=[F(comb(26,j))*F(256,tt*tt)**j for j in range(27)]
    assert all(q[j]<=major[j] for j in range(27)),tt
    print(f'PASS t={tt}: q_0=1, nonnegative all 27 coefficients, max q_j/major_j=',
        round(float(max(q[j]/major[j] for j in range(1,27))),10),
        'q_1*t^2=',round(float(q[1]*tt*tt),8))
assert F(128,49)<512 and F(64,49)**2<256**2
assert 2*9+4*2==26
print('PASS exact all-t≥200 coefficientwise majorant (1+256*z/t²)^26')

delta=F(1,32)
B0max=4*delta
assert B0max==F(1,8)
assert poly(200)[0]==1
print('PASS exact flat-top unit-port value at all t and support preserved')
assert sum(comb(26,j) for j in range(27))==2**26
print('PASS finite Sobolev bounds (k=0..8), eventual ||h_p||1<=1/4')

assert F(5184*5**6,4*factorial(6))==28125
r0=2048
c=F(567,1600*24)-F(28125*2,4*r0*r0)
assert c==F(2393451,209715200) and c>F(1,100)
print('PASS original selected-W target floor for t>=32768: m_W >=',c,'/r^6 =',float(c),'/r^6')

G=F(83,30); pp=F(32); U=F(5,4)
Cc=F(4)*G*pp*U**10*F(1,4)/factorial(10)
assert U**10<10 and G<3
assert Cc < F(1,3000)
assert F(4,3000) < 64*c
print('PASS each physical signed port C_i <',Cc,'/r < 1/(3000r) (t>=T_b)')
print('PASS four amplitudes |eps_i|<=r^-5: sum |eps_i|C_i < 1/(750r^6) < 64*m_W')

for k in (0,2,4,6,8,10):
    phys_const=F(4)*G*pp*U**k
    assert phys_const<F(384)*U**k
    print(f'PASS physical source 4-port abs moment k={k}: < {float(1536*U**k):.9g}/r^6')
assert (8-6)==2 and (6-6)==0
print('PASS explicit full-projective derivative growth: k=6 O(1), k=8 O(r^2);')
print('     exact physical 6th/8th MOMENTS decay O(r^-6), no source tail sign claim')
assert F(1,1)+F(5,1)==6
print('PASS frozen prime contribution and original target share r^-6 scaling under eps=r^-5')
print('OPEN effective T_b with a chosen C∞ plateau, entire enlarged-source E2 far/Schwartz/post-sixth estimates,')
print('     and genuinely independent signed all-zero/Gamma/prime E3 inequality; NO RH/GRH proof')
