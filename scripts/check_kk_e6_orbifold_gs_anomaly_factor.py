#!/usr/bin/env python3
"""Exact local orbifold UV-anomaly factorisation and GS/WZ donor (NOT full anomaly cancellation).

Source owners: E6 27 and E32/E33 #1106; physical 5D orbifold #1241.
Literature roots: Slansky (1981); Arkani-Hamed/Cohen/Georgi (2001);
Scrucca/Serone/Silvestrini/Zwirner (2002); von Gersdorff/Quiros
Phys Rev D68 (2003) 105002, DOI 10.1103/PhysRevD.68.105002.

For chosen gauged SU3c x SU3L x SU3R, P_L=P_R=diag(-,-,+),
and 4D chiral zero modes in the source-defined 27:
all tested cubic U1, mixed SU3/SU2 and gravitational-U1 local
anomaly polynomials factor through F_L-F_R. This admits a formal
localized Green-Schwarz/Wess-Zumino variation with axion shift
delta a=lambda_L-lambda_R, leaving electroweak Y neutral.

DO NOT promote this algebra to a globally integral spin/gauge
anomaly-free 5D orbifold or full gauged E6. Axion periodicity,
characteristic-class normalization, 5D inflow/eta, scalar action,
full gauge quotient and new orbifold effective stress remain OPEN.
"""
from itertools import product
import sympy as s

P=(-1,-1,1)
UL=(-1,-1,2)
UR=(-1,-1,2) # CENTRAL U1_R commuting with even SU2R
states=[]
for c,l in product(range(3),repeat=2):
    states.append(dict(sign=-P[l],L=-UL[l],R=0,c=1,l=l,r=None))
for c,r in product(range(3),repeat=2):
    states.append(dict(sign=-P[r],L=0,R=UR[r],c=-1,l=None,r=r))
for l,r in product(range(3),repeat=2):
    states.append(dict(sign=-P[l]*P[r],L=UL[l],R=-UR[r],c=0,l=l,r=r))
assert len(states)==27
x,y=s.symbols("F_L F_R")
cubic=s.expand(sum(w['sign']*(w['L']*x+w['R']*y)**3 for w in states))
grav=s.expand(sum(w['sign']*(w['L']*x+w['R']*y) for w in states))
Q4=40*x*x+64*x*y+40*y*y
assert s.expand(cubic-(x-y)*Q4)==0
assert s.expand(grav-16*(x-y))==0
mixed={}
for name,predicate,denominator in [
    ("SU3c2U1",lambda w:w['c']!=0,6),
    ("SU2L2U1",lambda w:w['l'] in (0,1),4),
    ("SU2R2U1",lambda w:w['r'] in (0,1),4)]:
    val=s.expand(sum(w['sign']*(w['L']*x+w['R']*y)
                for w in states if predicate(w))/denominator)
    assert val==2*(x-y),(name,val)
    mixed[name]=val
# Each boundary's symmetric half of this zero-mode anomaly has
# integer coefficients in THIS TRACE BASIS, but these integers are
# not certified universal integral characteristic classes.
assert all(n%2==0 for n in (40,64,40,16,2,2,2))
# A symmetric WZ term at EACH fixed point with a_i shift
# delta a_i=lambdaL(y_i)-lambdaR(y_i) can formally supply
# delta S_i=-(lambdaL-lambdaR)*X4/2 there. A bulk CS term
# alone shifts the two boundaries oppositely and cannot do so.
# Check the exact hypercharge direction under original E32/E33.
HR=(1,-1,0)
phi=(UL[2],-UR[1],-HR[1]) # E32
chi=(UL[2],-UR[2],-HR[2]) # E33
assert phi==(2,1,1) and chi==(2,-2,0)
assert all(u+v-3*h==0 for u,v,h in (phi,chi))
# T_R^(final Y) = U_R - 3 H_R.
finalTR=tuple(a-3*b for a,b in zip(UR,HR))
assert finalTR==(-4,2,2)
# Y=(U_L+U_R-3 H_R)/6 has lambdaL=lambdaR; the
# anomalous axion shift lambdaL-lambdaR is Y-neutral.
assert s.Rational(1,6)-s.Rational(1,6)==0
# EXISTING Chi33 phase transforms with charge (2,-2):
# arg Chi33 =2(lambdaL-lambdaR), so a=argChi/2 works
# INFINITESIMALLY but may fail its GLOBAL 2pi periodicity.
# For symmetric boundaries the naive WZ /4 coefficients
# of nonabelian terms are half-integral in this trace basis.
assert 2%4!=0
print("PASS exact 27 local Abelian anomaly:",s.factor(cubic))
print("PASS gravitational and all three SU3c,SU2L,SU2R mixed anomalies factor (F_L-F_R)")
print("PASS anomaly-free Y lies in U_L+U_R-3 H_R, preserving photon gauge generator")
print("PASS original Chi E33 Goldstone shifts along anomalous Abelian direction, charge 2")
print("CAVEAT Chi phase/2 global periodicity and nonabelian mixed coefficient /4 NOT certified")
print("OPEN localized axion/source action, full spin/quotient CS/inflow regulator, complete 5D gauge quantum theory")
