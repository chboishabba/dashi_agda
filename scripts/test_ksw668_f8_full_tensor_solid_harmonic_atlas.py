#!/usr/bin/env python3
"""Exact full Cartesian original KSW668 TT tensor spherical-harmonic atlas.

Reuses original source T=PQP-(tr(PQ)/2)P and the F8 yy axisymmetric
projection. Exact polynomial P_l^m conventions (Condon-Shortley).
No assertion of finite-volume tensor commutation or Agda kernel acceptance.
"""
import sympy as s
x,y,z=s.symbols("x y z",real=True)
K=x*x+y*y+z*z
k=s.Matrix([x,y,z])
P=K*s.eye(3)-k*k.T
Q=s.diag(0,1,-1)
T=(P*Q*P-s.Rational(1,2)*P*s.trace(P*Q)).applyfunc(s.expand)
H={
"00":K*K,
"20":K*(3*x*x-K)/2,
"40":(35*x**4-30*K*x*x+3*K*K)/8,
"21c":-3*K*x*y,"21s":-3*K*x*z,
"41c":-s.Rational(5,2)*x*(7*x*x-3*K)*y,
"41s":-s.Rational(5,2)*x*(7*x*x-3*K)*z,
"22c":3*K*(y*y-z*z),
"42c":s.Rational(15,2)*(7*x*x-K)*(y*y-z*z),
"43c":-105*x*(y**3-3*y*z*z),
"43s":-105*x*(3*y*y*z-z**3),
"44c":105*(y**4-6*y*y*z*z+z**4),
"44s":420*y*z*(y*y-z*z)
}
C={
"xx":{"22c":s.Rational(4,21),"42c":s.Rational(1,105)},
"xy":{"21c":s.Rational(2,7),"41c":s.Rational(1,70),"43c":-s.Rational(1,420)},
"xz":{"21s":-s.Rational(2,7),"41s":-s.Rational(1,70),"43s":-s.Rational(1,420)},
"yy":{"00":s.Rational(2,5),"20":s.Rational(4,7),"40":s.Rational(1,35),
"22c":-s.Rational(2,21),"42c":-s.Rational(1,210),"44c":s.Rational(1,840)},
"yz":{"44s":s.Rational(1,840)},
"zz":{"00":-s.Rational(2,5),"20":-s.Rational(4,7),"40":-s.Rational(1,35),
"22c":-s.Rational(2,21),"42c":-s.Rational(1,210),"44c":-s.Rational(1,840)}
}
pairs={"xx":(0,0),"xy":(0,1),"xz":(0,2),"yy":(1,1),"yz":(1,2),"zz":(2,2)}
n=0
for key,(i,j) in pairs.items():
    assert s.expand(T[i,j]-sum((coef*H[h] for h,coef in C[key].items()),s.S.Zero))==0,key
    n+=1
assert (T*k).applyfunc(s.expand)==s.zeros(3,1);n+=1
assert s.expand(s.trace(T))==0;n+=1
assert set(H)=={h for modes in C.values() for h in modes};n+=1
m0=sum((C["yy"][h]*H[h] for h in ("00","20","40")),s.S.Zero)
assert s.expand(m0-(x**4+6*K*x*x+K*K)/8)==0;n+=1
assert s.expand(T[1,1].subs({y:0,z:0})-x**4)==0;n+=1
assert all(s.expand(H[h].subs({y:0,z:0}))==0 for h in H if h not in ("00","20","40"));n+=1
print(f"{n}/{n} independent exact full tensor harmonic and TT checks PASS")
print("Each of six components uses only ell=0,2,4 but total m=0,1,2,3,4.")
