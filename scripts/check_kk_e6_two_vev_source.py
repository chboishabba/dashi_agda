#!/usr/bin/env python3
"""PR #1106 E6 2-VEV spectrum -> PR #1241 KK same-action consumer.
Illustrative mass calibration only. Original 5D Yang-Mills/Higgs EFT
and physical 27-family spectrum are NOT established by these checks.
"""
import sympy as s
from collections import Counter
from mpmath import mp
mp.dps=35
vmass=[s.Rational(1,4)]*4+[s.Rational(1,2)]*7+[s.Rational(5,6)]
hmass=[4]*6+[6]*8+[8]*10
assert len(vmass)==12 and len(hmass)==24
assert Counter(vmass)=={s.Rational(1,4):4,s.Rational(1,2):7,s.Rational(5,6):1}
assert Counter(hmass)=={4:6,6:8,8:10}
assert 16*3+36 == 4*3+12*4+24 == 84
print("PASS E6 two-VEV DOF: 16 massless 5D vector + 36 scalar = 4 massless vector + 12 massive 5D vector + 24 real Higgs = 84")
Z=mp.zeta(5);b=mp.mpf('1e-24')/mp.mpf('0.1973269804e-15')
def f(z):
    if z==0:return mp.mpf(1)
    e=mp.exp(-z)
    return (mp.polylog(5,e)+z*mp.polylog(4,e)+z*z*mp.polylog(3,e)/3)/Z
def fp(z):
    if z==0:return mp.mpf(0)
    e=mp.exp(-z)
    return -z*(mp.polylog(3,e)+z*mp.polylog(2,e))/(3*Z)
def h(z):return f(z)-z*fp(z)/5
qs=[2*mp.pi*mp.mpf(x)*b for x in ('.00216','.00470','.0935','1.273','4.183','172.56')]
qcdD=5*24-60*mp.fsum(h(q) for q in qs)
assert abs(qcdD+240)<mp.mpf('1e-6')
def total_defect(V):
    zv=2*mp.pi*mp.mpf(V)*b
    gauges=60+20*mp.fsum(h(zv*mp.sqrt(mp.mpf(x.numerator)/x.denominator)) for x in vmass)
    higgs=5*mp.fsum(h(zv*mp.sqrt(t)) for t in hmass)
    return qcdD+gauges+higgs
for V in (1000,10000,100000,100000000):
    print("illustrative_VEV_GeV",V,"selected_QCD_plus_E6_defect",mp.nstr(total_defect(V),18))
assert mp.mpf('179.99')<total_defect(10000)<mp.mpf('180.01')
root=mp.findroot(total_defect,(mp.mpf('3e7'),mp.mpf('1e8')))
assert abs(total_defect(root))<mp.mpf('1e-27')
print("one_equation_root_GeV",mp.nstr(root,17),"ratio_to_inverse_radius",mp.nstr(root*b,12))
# If an independent Maxwell B is simply adjoined to the E6
# SU2_L x U1_Y fields, one EW neutral Higgs VEV yields rank 1
# in three neutral generators (B_independent,T3,Y): TWO photons.
v,g2,gY=s.symbols("v g2 gY",positive=True)
q=s.Matrix([0,-g2/2,gY/2]);mass=s.simplify(v*v*q*q.T)
assert mass.rank()==1 and len(mass.nullspace())==2
assert mass*s.Matrix([1,0,0])==s.zeros(3,1)
assert mass*s.Matrix([0,gY,g2])==s.zeros(3,1)
assert (mass+v*v*s.Matrix([1,0,0])*s.Matrix([[1,0,0]])).rank()==2
print("PASS distinct EW residual photon and independent Maxwell B unless extra source/identification is supplied")
# Existing SO3 torque is a different Lie algebra from fibre u1;
# all three so3 basis axes are commutators, which map to zero in u1.
Jx=s.Matrix([[0,0,0],[0,0,-1],[0,1,0]])
Jy=s.Matrix([[0,0,1],[0,0,0],[-1,0,0]])
Jz=s.Matrix([[0,-1,0],[1,0,0],[0,0,0]])
comm=lambda A,B:A*B-B*A
assert comm(Jx,Jy)==Jz and comm(Jy,Jz)==Jx and comm(Jz,Jx)==Jy
print("PASS torque so3 cannot be identified with KK fibre u1 by a nonzero Lie algebra homomorphism")
print("OPEN full E6 27-family 5D action, physical mass source, gauge mixing, gauge fixing, 5D CS/anomaly, all-variable vacuum, quantum loops")
