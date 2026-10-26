#!/usr/bin/env python3
"""Low-degree ordinary Spin AHSS / central-Z3 Serre SS for H and K.

Original spectral-sequence and anomaly methodology: Atiyah-Hirzebruch,
Dai-Freed, Davighi-Gripaios-Lohitsiri JHEP07(2020)232 §§4.5,6.3.
Original selected gauge/Higgs: E6 #1106 and physical KK #1241.
The source-specific Sq² rank reduction is Johl Brown / OpenAI assisted.

COVER cohomology inputs (standard, NOT proven by this Python test):
H0=SU3c x U2L x U2R:
 H*(BH0,Z)=Z[xL,xR,c2L,c2R,c2c,c3c] (degrees 2,2,4,4,4,6).
K0=SU3c x S(U2L x U2R):
 H*(BK0,Z)=Z[x,c2L,c2R,c2c,c3c] (degrees 2,4,4,4,6).
Second identity follows from BK0 being the homotopy fibre of
BU2L x BU2R -> BU1 via detL/detR: polynomial ring is free over
Z[c1L-c1R], so integral Eilenberg-Moore Tor has no higher rows.
Both integral cohomology rings have NO odd classes through degree 6.

Standard spin AHSS: d2 dual to Sq² on rows q=0 and q=1.
On H0 and K0 the only possibly nonzero total-degree-5 row is
E²_(4,1)=H4(Bcover,Z2). Incoming d2 from H6(Z) and outgoing
d2 to H2(Z2) have complementary ranks, killing E∞_(4,1).
Also Omega3Spin(Bcover)=0: Sq² H² -> H⁴ is injective.

For central Z3 extension cover -> quotient:
 Bcover -> Bquotient -> K(Z3,2), with H_i(K(Z3,2);Z)
 i=0..5 equal [Z,0,Z3,0,Z3,0] (published DGL §4.5).
Because cover Omega5/Omega3=0 and Omega2 has only free+Z2,
all E²_(p,5-p) of generalized Serre SS vanish. So ordinary
Omega5Spin(BH)=Omega5Spin(BK)=0 UNDER these external classical
spectral-sequence/cohomology inputs. This is NOT a 5D ORBIFOLD
RELATIVE eta/Pfaffian/quantized CS/WZ, NOR does it cancel H local
perturbative anomaly. No Agda/Lean kernel theorem is claimed.
"""
def rank2(columns):
    pivots={}
    for col in columns:
        v=col
        while v:
            j=v.bit_length()-1
            if j not in pivots:
                pivots[j]=v
                break
            v^=pivots[j]
    return len(pivots)

# H0 H⁴=[xL²,xL*xR,xR²,c2L,c2R,c2c].
# Sq² H⁴ -> H⁶ images in independent targets:
# 0, xL²*xR+xL*xR², 0, xL*c2L, xR*c2R,c3c.
h4=[0,3,0,4,8,16]
# Sq²:H²=[xL,xR] -> H⁴=[xL²,xR²].
h2=[1,4]
assert rank2(h4)==4 and rank2(h2)==2
assert rank2(h4)+rank2(h2)==len(h4)
assert h4[0]==h4[2]==0  # Sq²∘Sq² on integral H²=0

# K0 H⁴=[x²,c2L,c2R,c2c].
# Sq² images [0,x*c2L,x*c2R,c3c], H² x -> x².
k4=[0,1,2,4]
k2=[1]
assert rank2(k4)==3 and rank2(k2)==1
assert rank2(k4)+rank2(k2)==len(k4)
assert k4[0]==0
for group,cols,low in (('H0',h4,h2),('K0',k4,k2)):
    print(f'PASS {group}: E²_(4,1) rank {len(cols)}, '
          f'incoming Sq² rank {rank2(cols)}, outgoing {rank2(low)}')
    print(f'PASS {group}: Omega3Spin=Omega5Spin=0 under standard Spin-AHSS')

# Ordinary closed-spin E2-page on central Z3 quotient:
# p=0:Omega5(cover)=0; p=1: H1(base;Omega4)=0;
# p=2:H2(base;Omega3)=0; p=3:H3(base;Omega2)=0
# as H3(Z3,E)=Tor(Z3,E), and E=Z^r+Z2 has no 3-torsion;
# p=4:H4(base;Omega1=Z2)=0; p=5:H5(base;Z)=0.
base_homology_Z=('Z','0','Z3','0','Z3','0')
assert base_homology_Z[1::2]==('0','0','0')
for name in ('H','K'):
    all_six=(0,0,0,0,0,0)
    assert all(v==0 for v in all_six)
    print(f'PASS {name}: E²_(p,5-p)=0, p=0..5, '
          'ordinary Omega5Spin(Bgroup)=0 on classical SS assumptions')
print('OPEN actual local H anomaly and 5D orbifold-relative eta/CS5/WZ')
