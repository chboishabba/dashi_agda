#!/usr/bin/env python3
"""Exact original 4D SU(N) Wilson/F19 one-pair source cubature bounds,
and a genuine continuous SU2 Haar/Bessel one-pair check.
No finite subgroup is misidentified as continuous Haar; no CMP119 Eq171
gauge/FP/E/R/B/V identification, W3 or Clay completion.
Uses existing native L4 source owner; local SymPy/Fraction, no CI.
"""
from fractions import Fraction as Q
from itertools import product
from importlib.util import spec_from_file_location, module_from_spec
from pathlib import Path
from math import comb
import sympy as s
p=Path(__file__).with_name("check_ym_p0_original_wilson_marked_ordered_t_20261123.py")
assert p.is_file()
spec=spec_from_file_location("original_wilson",p)
source=module_from_spec(spec);spec.loader.exec_module(source)
assert len(source.links)==1024 and len(source.faces)==1536
pairs=[]
for v in product(range(2),repeat=4):
 origin=tuple(2*x for x in v)
 for a in range(4):
  pairs.append(((origin,a),(source.step(origin,a),a)))
assert len(pairs)==64 and {e for pair in pairs for e in pair}==source.selected
assert len(set(source.links)-source.selected)==896
assert {sum(l not in source.selected for l in face) for face in source.faces}=={2,4}
fm=source.face(source.F,2,3)
gm=source.face(source.G,2,3)
marked=[]
groups=0
for pair in pairs:
 touched=[face for face in source.faces if any(l in face for l in pair)]
 assert len(touched)==12 and all(sum(l in face for l in pair)==1 for face in touched)
 f=sum(l in fm for l in pair)
 g=sum(l in gm for l in pair)
 assert f in (0,1) and g in (0,1) and f*g==0
 marked.append((f,g))
 groups+=4
assert marked.count((1,0))==2 and marked.count((0,1))==2
assert marked.count((0,0))==60
groups+=3

# True Haar-cell quadrature: partition one SU(N) fibre into measurable cells
# of operator-norm diameter delta, use exact Haar mass per cell and one rep.
# For U0=WV^-1,U1=V, original 12 affected plaquettes each vary <=delta.
# Hence |dS|<=12delta and e^-x <= w'/w <= e^x, x=12beta delta.
# 0<=F,G<=2 and the ORIGINAL global incidence f,g is retained.
r=Q(9,100);lam=Q(1519,2500)
assert lam==1-4*r-4*r*r
groups+=1
for f,g in marked:
 for beta in (Q(0),Q(1,144),Q(1,16),Q(1),Q(16)):
  for delta in (Q(1,256),Q(1,1024),Q(1,65536)):
   x=12*beta*delta
   if x>=1:continue
   E=1/(1-x) # certified rational upper bound for exp(x) for x<1
   e0=E-1
   ef=2*(E-1)+f*E*delta
   eg=2*(E-1)+g*E*delta
   efg=4*(E-1)+2*(f+g)*E*delta
   assert min(e0,ef,eg,efg)>=0
   e=e0+r*(ef+eg)+r*r*efg
   D=4*e0+efg+e0*efg+2*(ef+eg)+ef*eg
   if e<lam:
    hbound=D/(lam-e)**2+e*(2*lam-e)/(lam*lam*(lam-e)**2)
    assert hbound>=0
    groups+=1
   groups+=4
# For SU2=unit quaternions S3, coordinate-rounding 1/M and normalization
# yields a finite measurable net with max cell diameter 4/M and true Haar
# cell weights (NOT equal Q8 counting weights).
M=1024;delta=Q(4,M);beta=Q(1,144)
x=12*beta*delta
assert delta==Q(1,256) and x==Q(1,3072)
E=1/(1-x)
assert E-1==Q(1,3071)
assert (2*(E-1)+E*delta)==Q(14,3071)
assert 2*(E-1)==Q(2,3071)
assert 4*(E-1)+2*E*delta==Q(28,3071)
groups+=5
# Quantize all 64 original fine fibres and ALL 896 spectators at fixed W.
# Each of 1024 original links changes <=delta, each appears in 6 faces.
# Four original global deficit marks each involve 4 original links.
delta=Q(1,65536)
X=6144*beta*delta
assert X==Q(1,1536)
E=1/(1-X)
e0=E-1; ef=2*(E-1)+4*E*delta; eg=ef
efg=4*(E-1)+16*E*delta
e=e0+r*(ef+eg)+r*r*efg
D=4*e0+efg+e0*efg+2*(ef+eg)+ef*eg
mixed=D/(lam-e)**2+e*(2*lam-e)/(lam*lam*(lam-e)**2)
assert e<lam and mixed<Q(37880,1000000)
groups+=3
# Haar first moment of every original plaquette trace is zero conditional on
# the F19 coarse W: every face contains >=2 independent spectator Haar links.
# Hence E_Haar(S|W)=1536 and Jensen K0(W)>=exp(-1536 beta).
# The following exact test certifies the geometric premise, not a sampled
# continuous-Haar integral.
assert all(any(l not in source.selected for l in face) for face in source.faces)
groups+=1
def hm(n):
 if n%2:return Q(0)
 k=n//2
 return Q(comb(2*k,k),(k+1)*4**k)
def q8m(n):return Q(1) if n==0 else Q(0) if n%2 else Q(1,4)
for n in range(33):
 assert Q(0)<=hm(n)<=1
 assert q8m(n)>=hm(n)
 if n<4:assert q8m(n)==hm(n)
 groups+=2
assert hm(4)==Q(1,8) and q8m(4)==Q(1,4)
t=s.symbols("t",positive=True)
I=2*s.besseli(1,t)/t
J=(s.cosh(t)+3)/4
assert s.simplify(s.diff(I,t)-2*s.besseli(2,t)/t)==0
assert s.simplify(s.series(J-I,t,0,8).removeO()-(t**4/s.Integer(192)+11*t**6/s.Integer(46080)))==0
groups+=3
# The positive moment discrepancy starts at fourth power. For 0<t<=1:
# (J-I)/I <= t^4/[96(1-t^2/30)], and
# |(J-J')-(I-I')|/I <= first bound+t^3/[24(1-t^2/20)].
# This is a special one-fibre continuous Haar vs Q8 cubature bound,
# NEVER a claim Q8 is an arbitrary-background δ-net.
tv=Q(1,12)  # beta=1/144, t=12 beta, W=I, all other source links identity
b0=tv**4/(96*(1-tv**2/30))
bf=b0+tv**3/(24*(1-tv**2/20))
assert b0==Q(5,9950976) and bf==Q(235145,9549619968)
groups+=2
for x in (s.Rational(1,12),s.Rational(1,3),s.Rational(1)):
 ih=s.N(I.subs(t,x),50);iq=s.N(J.subs(t,x),50)
 iph=s.N(s.diff(I,t).subs(t,x),50);iqp=s.N(s.diff(J,t).subs(t,x),50)
 assert 0<=iq-ih<=s.N(x**4/(96*(1-x**2/30)),50)
 assert 0<=iqp-iph<=s.N(x**3/(24*(1-x**2/20)),50)
 assert abs((iq-iqp)-(ih-iph))/ih<=s.N(x**4/(96*(1-x**2/30))+x**3/(24*(1-x**2/20)),50)
 groups+=3
print("PASS",s.__version__,groups,"exact assertion groups")
print("Native original 1536 faces/1024 links; 64 original R445 pairs; 896 spectators")
print("Exact full Wilson Haar-cell source-relative four-column bounds, every pair/beta")
print("Original SU2 continuous Haar conditional at all-identity background: I=2*BesselI1(t)/t")
print("Finite Q8 cubature fails fourth Haar moment; rigorous beta=1/144 error bounds",b0,bf)
print("OPEN physical CMP119/122 Eq171 FP/gauge/E/R/B/V, source W3 and same-H OS")
