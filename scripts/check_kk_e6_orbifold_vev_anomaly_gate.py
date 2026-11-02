#!/usr/bin/env python3
"""Source-specific E6/trinification orbifold physical gate.

DONORS: #1106 first-Tits 27=(3,bar3,1)+(bar3,1,3)+(1,3,bar3),
E32/E33 two VEVs, two complex 3x3 Higgs fields, gauge-selected V6.
ORIGINAL science: Slansky 1981 E6 branch, Arkani-Hamed/Cohen/Georgi
2001 orbifold chiral anomaly, Scrucca et al 2002 fixed-point anomalies.

Candidate orbifold SU3c x SU3L x SU3R (NOT full gauged E6):
P_L=P_R=diag(-1,-1,+1), P_c=1; fermion 27 gamma5*rho(P).
With gamma5 RH + and LH -, parity eigen + selects RH and - LH.
Phi intrinsic parity - and Chi + leave E32 and E33 EVEN,
consistent with #1106's V6 (even under independent Phi/Chi sign).
Tests: surviving 16 LH/11 RH, exactly FOUR EW gauge generators
after VEV, Y=(diag(-1,-1,2),diag(-4,2,2))/6,
4D SM-subgroup anomaly sums zero and SU2 Witten even.
Crucial UV NEGATIVE CONTROL: pre-VEV SU2LxU1LxSU2RxU1R
has NONZERO anomaly coefficients, requiring boundary terms/inflow.
If FULL E6 78 gauge generators are present, 30 EXTRA mixed-sector
generators are orbifold even; can't transplant the 16-L/R gauge
spectrum into fully gauged E6. NO chiral SM/CS source proven.
"""
import sympy as s
from fractions import Fraction as F
from itertools import product
P=(-1,-1,1)
QL=(-1,-1,2)
QR=(-4,2,2)  # R contribution to final hypercharge Y/6
UR=(-1,-1,2) # CENTRAL pre-VEV U1_R commuting with the surviving SU2_R
assert P[0]*P[1]*P[2]==1
rows=[]
for c,l in product(range(3),range(3)):
    rows.append(dict(block="A",colour="3",l=l,r=None,
                     p=P[l],YL=-QL[l],YR=0,Y=-QL[l]))
for c,r in product(range(3),range(3)):
    rows.append(dict(block="B",colour="bar3",l=None,r=r,
                     p=P[r],YL=0,YR=UR[r],Y=QR[r]))
for l,r in product(range(3),range(3)):
    rows.append(dict(block="C",colour="1",l=l,r=r,
                     p=P[l]*P[r],YL=QL[l],YR=-UR[r],
                     Y=QL[l]-QR[r]))
assert len(rows)==27
nleft=sum(v["p"]==-1 for v in rows)
nright=sum(v["p"]==1 for v in rows)
assert (nleft,nright)==(16,11)
assert [(sum(v["p"]==-1 for v in rows if v["block"]==k),
         sum(v["p"]==1 for v in rows if v["block"]==k))
        for k in "ABC"]==[(6,3),(6,3),(4,5)]

def E(i,j):
    a=s.zeros(3);a[i,j]=1;return a
PL=s.diag(-1,-1,1)
PR=PL
phi=E(2,1)  # E32
chi=E(2,2)  # E33
assert -PL*phi*PR==phi and PL*chi*PR==chi
# Original #1106 V6 uses ONLY even powers of Phi and Chi.
def tr(m):return sum(m[i,i] for i in range(m.rows))
def V(a,b):
    na=tr(a.H*a);nb=tr(b.H*b)
    return (na-1)**2+(nb-1)**2+na**2-tr((a.H*a)**2)+ \
      nb**2-tr((b.H*b)**2)+tr(a.H*a*b.H*b)+ \
      na*nb-tr(a*a.H*b*b.H)
u=s.Matrix([[1,0,0],[0,0,1],[1,2,0]])
v=s.Matrix([[0,2,0],[3,0,0],[0,1,1]])
assert s.simplify(V(u,v)-V(-u,v))==0
assert s.simplify(V(u,v)-V(u,-v))==0
assert V(phi,chi)==0
basis=[]
for i in range(3):
  for j in range(i+1,3):
    basis.extend([E(i,j)+E(j,i),s.I*(E(i,j)-E(j,i))])
basis.extend([s.diag(1,-1,0),s.diag(1,1,-2)])
even=[H for H in basis if PL*H*PL==H]
assert len(basis)==8 and len(even)==4
def constraints(L,R):
    entries=[]
    for z in (phi,chi):
        A=L*z-z*R
        entries += [s.re(x) for x in A]
        entries += [s.im(x) for x in A]
    return s.Matrix(entries)
zero=s.zeros(3)
C=s.Matrix.hstack(*( [constraints(H,zero) for H in even] +
                     [constraints(zero,H) for H in even] ))
assert C.cols==8 and C.rank()==4
YL=s.diag(*QL)
YR=s.diag(*QR)
assert constraints(YL,YR)==s.zeros(36,1)
for H in (E(0,1)+E(1,0),s.I*(E(0,1)-E(1,0)),s.diag(1,-1,0)):
    assert constraints(H,zero)==s.zeros(36,1)
assert all(PL*H*PL==H for H in (YL,YR))
# Hypercharge is Y/6. 4D perturbative anomaly normalizations:
# colour cubic: fundamental +1, conjugate -1; state count /3 colours.
A_c=F(sum(-w["p"]*(1 if w["colour"]=="3" else -1)
          for w in rows if w["colour"]!="1"),3)
A_Y3=sum((F(-w["p"]*w["Y"]**3,216) for w in rows),F(0))
A_gY=sum((F(-w["p"]*w["Y"],6) for w in rows),F(0))
A_ccY=sum((F(-w["p"]*w["Y"],36) for w in rows if w["colour"]!="1"),F(0))
A_LL_Y=sum((F(-w["p"]*w["Y"],24) for w in rows
            if w["l"] is not None and w["l"]<2),F(0))
assert (A_c,A_Y3,A_gY,A_ccY,A_LL_Y)==(0,0,0,0,0)
leftdbl=sum(w["p"]==-1 for w in rows if w["l"] in (0,1))//2
rightdbl=sum(w["p"]==1 for w in rows if w["l"] in (0,1))//2
assert leftdbl+rightdbl==6 and (leftdbl+rightdbl)%2==0
# Even scalar Chi contains SU2L doublets with Y=+/-1/2.
even_chi=[(l,r,F(QL[l]-QR[r],6)) for l,r in product(range(3),repeat=2)
          if P[l]*P[r]==1 and l in (0,1)]
assert {y for l,r,y in even_chi}=={F(1,2),F(-1,2)}
# BUT UV orbifold group BEFORE 2-VEV breaking has source anomalies:
UV={}
for tag,fn in (
 ('UL3',lambda w:w["YL"]**3),('UR3',lambda w:w["YR"]**3),
 ('UL2UR',lambda w:w["YL"]**2*w["YR"]),
 ('ULUR2',lambda w:w["YL"]*w["YR"]**2),
 ('gravUL',lambda w:w["YL"]),('gravUR',lambda w:w["YR"])):
    UV[tag]=sum((F(-w["p"]*fn(w)) for w in rows),F(0))
assert UV=={'UL3':40,'UR3':-40,'UL2UR':8,'ULUR2':-8,'gravUL':16,'gravUR':-16}
for key,q in (('ccUL','YL'),('ccUR','YR')):
    UV[key]=sum((F(-w["p"]*w[q],6) for w in rows if w["colour"]!="1"),F(0))
assert UV["ccUL"]==2 and UV["ccUR"]==-2
for factor,index in (('SU2L','l'),('SU2R','r')):
    for U in ('YL','YR'):
        val=sum((F(-w["p"]*w[U],4) for w in rows
                 if w[index] is not None and w[index]<2),F(0))
        UV[factor+U]=val
assert all(UV[k] in (2,-2) for k in ('SU2LYL','SU2LYR','SU2RYL','SU2RYR'))
# 78 E6 adjoint: 8+8+8 + (3,3,3)+(bar3,bar3,bar3).
# An inner E6 parity P_L,P_R retains ADDITIONAL 30 even generators.
mixed_even=2*3*(2*2+1*1)
mixed_odd=2*3*(2*1+1*2)
assert mixed_even==30 and mixed_odd==24
assert (8+4+4+mixed_even,78-(8+4+4+mixed_even))==(46,32)
print("PASS original E32/E33 VEVs and sign-even V6 survive selected bifundamental orbifold parities")
print("PASS even SU3L/R gauge generators: 8; post-two-VEV kernel: 4 = SU2L + U1Y")
print("PASS 27 zero modes L/R:",nleft,nright,"Y=1/6*(diag(-1,-1,2),diag(-4,2,2))")
print("PASS tested IR SU3c^3, SU3c²Y, SU2L²Y, Y³, gravitational-Y anomalies all ZERO")
print("PASS SU2L Witten parity (six total Weyl doublets), even Chi candidate Y +/-1/2 doublets")
print("FAIL PRE-VEV orbifold U1L/R and mixed anomalies:",UV)
print("FAIL full-E6 adjoint identity from SU3³ truncation: 30 further E6 gauge generators even")
print("OPEN fixed-point anomaly/inflow, full orbifold bulk action, one physical photon after EW, realistic masses, fresh Casimir/stress")
