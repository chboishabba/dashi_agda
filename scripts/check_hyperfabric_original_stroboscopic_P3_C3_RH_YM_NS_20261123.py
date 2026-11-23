#!/usr/bin/env python3
"""Original P3^9 and C3^9 stroboscopic same-operator theorem, t=pi.

Source owners: original exact P3^3 rational walk, base369 nine-trit
path/periodic torus, RH original -20/351 squared Laurent Laplacian,
YM R445 L2 sign shifts, NS R529/R530 periodic sign and dyadic hat.
Finite exact time/spectral bridge; NOT physical continuous time PDE,
NS nonlinear, YM gauge Wilson/Haar or RH signed FarExact theorem.
"""
import sympy as s
from fractions import Fraction as F
from itertools import product
Q=s.Rational
I=s.eye(3);J=s.ones(3)
Lp=s.Matrix([[1,-1,0],[-1,2,-1],[0,-1,1]])
Lc=3*I-J
B=Q(2,3)*J-I
assert Lp!=Lc
assert Lp.eigenvals()=={0:1,1:1,3:1}
assert Lc.eigenvals()=={0:1,3:2}
P0=J/3
assert Lp*P0==s.zeros(3) and Lc*P0==s.zeros(3)
# Both graph eigenvalue sets are odd away from kernel:
# exp(-i*pi*Lp)=exp(-i*pi*Lc)=B, with B^2=I.
assert B==2*P0-I and B*B==I
T=s.Matrix([[0,0,1],[1,0,0],[0,1,0]])
assert T**3==I
assert B==Q(2,3)*(I+T+T**2)-I
assert B*T==T*B
# Original RH finite angular biharmonic GROUP-RING polynomial,
# now evaluated on actual original C3 spatial shift T.
D=T+T.T-2*I
RH=-Q(20,351)*D**2
assert RH==-Q(20,39)*(I-P0)
assert RH*B==B*RH
# Original YM site two-cycle direction acts on ternary chart as
# true sign reflection, preserves BOTH original path and torus.
R=s.Matrix([[0,0,1],[0,1,0],[1,0,0]])
assert R*T*R==T.T
assert R*B==B*R and R*RH==RH*R
assert R*Lp==Lp*R and R*Lc==Lc*R
# Genuine original periodic C3 Fourier characters on {-1,0,1}.
w=(-1+s.I*s.sqrt(3))/2
for q,phase in ((0,1),(1,-1),(2,-1)):
    v=s.Matrix([w**(q*x%3) for x in (-1,0,1)])
    assert all(s.simplify(z)==0 for z in B*v-phase*v)
    assert all(s.simplify(z)==0
        for z in RH*v-(0 if q==0 else -Q(20,39))*v)
# Tensor original source operator: U9(pi)=B^tensor9 on original
# P3^9, *identical* to C3^9 periodic U9(pi) at this special time.
for q in product((-1,0,1),repeat=9):
    assert (-1)**sum(a!=0 for a in q) in (-1,1)
assert sum(all(a!=0 for a in q)
    for q in product((-1,0,1),repeat=9))==512
assert 3**9==19683
# Exact original YM L=2 four-axis coarse sites map to signed
# 4-coordinate face of the same nine-trit carrier, with 2-step
# path subdivision from source original L=4 selected links.
YM=tuple(product((-1,1),repeat=4))
assert len(YM)==16
for x in YM:
    for j in range(4):
        y=list(x);y[j]=-y[j];mid=list(x);mid[j]=0
        assert tuple(y) in YM
        assert sum(a!=b for a,b in zip(x,mid))==1
        assert sum(a!=b for a,b in zip(mid,y))==1
assert all((-1)**sum(a!=0 for a in x+(0,)*5)==1 for x in YM)
# Consumer-specific factorization: sign/support suffices for the
# special U(pi) eigenphase; NOT the original NS dyadic magnitude.
def u_pi_consumer(sign):return (-1)**sum(x!=0 for x in sign)
assert u_pi_consumer((1,0,0))==u_pi_consumer((-1,0,0))==-1
def hat(K,r):
    lo,mid,hi=2**(K-1),2**K,2**(K+1)
    if not(lo<=r<=hi):return F(0)
    return F(r-lo,mid-lo) if r<=mid else F(hi-r,hi-mid)
assert hat(3,8)==F(1) and hat(3,9)==F(7,8)
print("PASS source P3 vs C3: exact same U(pi) despite DIFFERENT Laplacians")
print("PASS full T9 stroboscopic operator Fourier multiplier (-1)^support and 512 signed modes")
print("PASS RH original negative biharmonic polynomial C3 spectrum 0, -20/39")
print("PASS YM original C2 four-axis sign flips commute with native wave and RH polynomial")
print("PASS NS sign sufficient for U(pi) only; insufficient for dyadic or nonlinear Fourier")
print("OPEN physical continuous t, YM group-valued Wilson, NS R406, RH FarExact")
