#!/usr/bin/env python3
"""26D NONFLAT FULL NS-NS low-energy string beta equations: SU2 NS-flux + linear dilaton.

Standard prior physics: SU(2) WZW / three-sphere NS-NS flux and
spacelike linear dilaton. Selected continuum ansatz
M26=R^(1,22) x S3_r, H=(2/r) vol_S3, Phi=x_spatial/r.
Checks Ricci from an actual su2 left-invariant orthonormal frame,
H parallel transport, all metric/B/dilaton beta equations in 26D
at leading two-derivative order. The global B is only a GERBE connection.
Separate 2D exact c_SU2(k)=3k/(k+2) flags finite-k level shift.
No new string theorem, quantum target solution or Clay promotion.
"""
from fractions import Fraction as Q

def eps(i,j,k):
    if len({i,j,k})<3:return Q(0)
    return Q(1 if (i,j,k) in ((0,1,2),(1,2,0),(2,0,1)) else -1)

def check(r):
    inv=Q(1,r)
    gamma=lambda i,j,k:inv*eps(i,j,k)
    struct=lambda i,j,k:2*inv*eps(i,j,k)
    H=lambda i,j,k:2*inv*eps(i,j,k)
    # Levi-Civita of the bi-invariant SU2 round S3.
    for i in range(3):
        for j in range(3):
            for k in range(3):
                assert gamma(i,j,k)-gamma(j,i,k)==struct(i,j,k)
                assert gamma(i,j,k)+gamma(i,k,j)==0
                for l in range(3):
                    covH=sum((gamma(i,j,m)*H(m,k,l)+gamma(i,k,m)*H(j,m,l)+gamma(i,l,m)*H(j,k,m) for m in range(3)),Q(0))
                    assert covH==0
    def curvature(i,j,k,l):
        return sum((gamma(j,k,m)*gamma(i,m,l)-gamma(i,k,m)*gamma(j,m,l)-struct(i,j,m)*gamma(m,k,l) for m in range(3)),Q(0))
    ricci=lambda j,k:sum((curvature(i,j,k,i) for i in range(3)),Q(0))
    for j in range(3):
        for k in range(3):
            ric=ricci(j,k)
            assert ric==Q(2,r*r)*(j==k)
            contraction=sum((H(j,a,b)*H(k,a,b) for a in range(3) for b in range(3)),Q(0))
            assert contraction==Q(8,r*r)*(j==k)
            assert ric-Q(1,4)*contraction==0
    Hsq=sum((H(i,j,k)**2 for i in range(3) for j in range(3) for k in range(3)),Q(0))
    scalar=sum((ricci(j,j) for j in range(3)),Q(0))
    gradPhiSq=Q(1,r*r)  # chosen FLAT SPACELIKE gradient
    assert scalar==Q(6,r*r) and Hsq==Q(24,r*r)
    assert scalar-4*gradPhiSq-Hsq/12==0
    # Flat metric block: Ricci=0, HessPhi=0 and no H legs.
    # B EOM: H is parallel on S3; dPhi is orthogonal to S3.
    # Bianchi: H is a closed top-degree volume 3-form on S3.
    return scalar,Hsq,gradPhiSq

for r in (Q(1,3),Q(1),Q(3,2),Q(2),Q(5,3),Q(7)):
    R,H2,grad=check(r)
    print(f'PASS SU2 coupled 26D leading NSNS: radius {r}, scalarR={R}, H2={H2}, |dPhi|²={grad}')

# Standard independent worldsheet prior art: Sugawara for SU2 at level k.
# 23 free noncompact bosons (including the background-charged one) plus
# c-difference 6*alphaPrime*V² from the spacelike linear dilaton.
for i in range(1,31):
    k=Q(i)
    cWZW=3*k/(k+2)
    classicalSlope=Q(1,k)      # alphaPrime*V² from classical R²=k alphaPrime
    quantumSlope=Q(1,k+2)      # central-charge-corrected worldsheet input
    assert 23+6*classicalSlope+cWZW-26==Q(12,k*(k+2))>0
    assert 23+6*quantumSlope+cWZW==26
    assert 23+6*quantumSlope+cWZW-26==0  # add standard bc c=-26
print('PASS 30 exact SU2_k/linear-dilaton Sugawara c identities')
print('NO-GO using the unshifted classical slope at finite level: delta c=12/[k(k+2)]')
print('PASS critical worldsheet charge requires alphaPrime*V²=1/(k+2) at finite k')
print('BOUNDARY globally H flux is not dB for one global B; flux quantization/gerbe and target higher-loop corrections')
print('BOUNDARY leading NSNS equations + algebraic c=26 is not a kernel-certified all-orders string background')
