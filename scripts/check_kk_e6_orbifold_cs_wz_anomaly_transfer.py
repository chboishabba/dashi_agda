#!/usr/bin/env python3
"""Selected 27 UV orbifold anomaly transfer via 5D CS + one brane WZ.

Original mathematics/physics: Slansky 1981 E6 branching; orbifold
inflow and GS: Arkani-Hamed/Cohen/Georgi 2001; von Gersdorff &
Quiros, PRD 68 (2003) 105002. Repo owners first-Tits #1106,
physical KK #1241, old 2+1D CS owners are NOT 5D functional proofs.

Exact source polynomial in the UNNORMALIZED SU3^3 integer-charge
trace basis: I6=(FL-FR)*X4, X4=(40FL²+64FL FR+40FR²)
+16p1+2(c2c+c2L+c2R). Labels p1,c2 stand for placeholder
period generators, NOT actual normalized spin/quotient classes.

Two equal original fixed-point anomalies (I6/2,I6/2) and the
formal 5D bulk-CS boundary transfer (+I6/2,-I6/2) yield (I6,0).
At the first boundary, the *existing* charge-two Chi33 phase
theta->theta+2alpha with WZ coefficient -theta*X4/2 cancels the
LOCAL consistent variation. Every coefficient of X4/2 is integer
in this declared naive lattice, unlike X4/4 at both boundaries.
This REMOVES only a conditional half-phase obstruction; the global
spin/quotient gauge CS lattice, properly normalised anomaly descent,
eta regulator, endpoint distribution, physical source, and real
gauge path integral are NOT paid.
"""
from itertools import product
import sympy as s

P=(-1,-1,1);UL=(-1,-1,2);UR=(-1,-1,2)
rows=[]
for c,l in product(range(3),repeat=2):
    rows.append((-P[l],-UL[l],0,"colour",l,None))
for c,r in product(range(3),repeat=2):
    rows.append((-P[r],0,UR[r],"colour",None,r))
for l,r in product(range(3),repeat=2):
    rows.append((-P[l]*P[r],UL[l],-UR[r],"singlet",l,r))
assert len(rows)==27

x,y=s.symbols("F_L F_R")
cubic=s.expand(sum(hand*(ql*x+qr*y)**3 for hand,ql,qr,_,_,_ in rows))
grav=s.expand(sum(hand*(ql*x+qr*y) for hand,ql,qr,_,_,_ in rows))
Xab=40*x*x+64*x*y+40*y*y
diff=x-y
assert s.expand(cubic-diff*Xab)==0
assert s.expand(grav-16*diff)==0
mixed={}
for key,test,divisor in [
    ("SU3c2",lambda z:z[3]=="colour",6),
    ("SU2L2",lambda z:z[4] in (0,1),4),
    ("SU2R2",lambda z:z[5] in (0,1),4)]:
    mixed[key]=s.simplify(sum(z[0]*(z[1]*x+z[2]*y)
                             for z in rows if test(z))/divisor)
    assert mixed[key]==2*diff

p1,c2c,c2L,c2R=s.symbols("p1 c2c c2L c2R")
X4=s.expand(Xab+16*p1+2*(c2c+c2L+c2R))
I6=s.expand(diff*X4)

# Source half-anomalies + anti-symmetric boundary inflow = one end only.
original=(I6/2,I6/2)
transfer=(I6/2,-I6/2)
remaining=tuple(s.expand(a+b) for a,b in zip(original,transfer))
assert remaining==(I6,0)
theta,alpha=s.symbols("thetaChi alpha")
WZ=-theta*X4/2
assert s.expand(WZ.subs(theta,theta+2*alpha)-WZ)==s.expand(-alpha*X4)
# Full boundary-local consistency for INDEPENDENT allowed even
# gauge parameters at each endpoint, not just constant zero mode:
alpha0,alpha1=s.symbols("alpha0 alphaPi")
fermion_variation=(alpha0+alpha1)*X4/2
bulk_CS_variation=(alpha0-alpha1)*X4/2
local_WZ_variation=-alpha0*X4
assert s.expand(fermion_variation+bulk_CS_variation+
                local_WZ_variation)==0
coeff={str(z):s.expand(X4).coeff(z)
       for z in (x*x,x*y,y*y,p1,c2c,c2L,c2R)}
assert sorted(coeff.values())==sorted([40,64,40,16,2,2,2])
assert all(int(v)%2==0 for v in coeff.values())
assert (X4/4).coeff(c2c)==s.Rational(1,2)
assert (X4/2).coeff(c2c)==1

# The end-0 WZ source uses Chi33 with delta(theta)=2(lambdaL-lambdaR).
# On the declared free integer polynomial lattice it gives
# exp(i deltaS)=1 for theta->theta+2pi; this does NOT say whether the
# true quotient gauge/spin characteristic-class periods agree.
HR=(1,-1,0)
TR=tuple(ur-3*h for ur,h in zip(UR,HR))
assert TR==(-4,2,2) # original E32/E33 Y_R direction
assert (UL[2],-UR[2])==(2,-2)

print("PASS selected 27 anomaly polynomial",s.factor(cubic))
print("PASS 5D CS transfer: (I6/2,I6/2)+(+I6/2,-I6/2)=(I6,0)")
print("PASS local Chi33 WZ cancellation with X4/2, all coefficients integral on naive source trace lattice",coeff)
print("PASS prior symmetric two-boundary WZ has apparent mixed half-unit, transferred one-boundary WZ does not")
print("OPEN normalized spin/(SU3^3 x U1)/Gamma integral characteristic classes, eta/regulator and CS level")
print("OPEN actual source-local quantum action with Chi phase nonzero at fixed plane, chiral masses, 5D gravity and stress")
