#!/usr/bin/env python3
"""Original L4 2-time Wilson 8-wall restricted-coupling exact character-channel audit.

This is a source-specific 2D sphere of ten ORIGINAL 4D plaquettes, not
homogeneous 4D YM or CMP119/122 T. Exact all-beta formulas rely on
standard SU(N) Haar character orthogonality on the isolated sphere.
"""
from itertools import combinations, product
from collections import Counter
import sympy as S
L=4
sites=tuple(product(range(L),repeat=4))
def step(x,axis,sgn=1):
    y=list(x);y[axis]=(y[axis]+sgn)%L;return tuple(y)
def face(x,a,b):
    return ((x,a,1),(step(x,a),b,1),(step(x,b),a,-1),(x,b,-1))
faces={(x,a,b):face(x,a,b) for x in sites for a,b in combinations(range(4),2)}
assert len(faces)==1536
F=((0,0,0,0),1,2);G=((2,0,0,0),1,2)
def tube(d):
    return tuple(((t,dy,dz,0),0,a) for t in range(d) for a in (1,2)
                  for dy,dz in ([(0,0),(0,1)] if a==1 else [(0,0),(1,0)]))
def boundary(surface):
    ct=Counter((x,axis) for p in surface for x,axis,_ in faces[p]);return {e for e,n in ct.items() if n%2}
for d in (1,2):
    side=tube(d);cap1=((d,0,0,0),1,2)
    assert len(side)==4*d and not boundary((F,cap1)+side)
    assert all(boundary((F,cap1)+tuple(x for j,x in enumerate(side) if mask>>j&1))
               for mask in range((1<<len(side))-1))
    allfaces=(F,cap1)+side
    ct=Counter((x,axis) for p in allfaces for x,axis,_ in faces[p])
    assert len(ct)==8*d+4 and all(n==2 for n in ct.values())
    V=4*(d+1);E=len(ct);Nf=len(allfaces)
    assert V-E+Nf==2
    for N in (2,3,4,5):
        v=S.Rational(1,4) if N==2 else S.Rational(1,2*N*N)
        expected=v**(4*d+1)
        source=(S.Integer(N)**(V-E-Nf)
                * (S.Integer(1) if N==2 else S.Rational(1,2**(Nf-1))))
        assert expected==source
print('PASS original full 4D L4 surface, two caps, 4d walls, all missing-wall Haar obstructions')
print('PASS exact sphere first mixed derivatives SU2/3/4/5 for d=1,2')

# SU2 normalized Haar: t=ReTr(U)/2=cos(theta), E[t^(2n)]=Catalan(n)/4^n.
b=S.symbols('b',real=True)
Z=sum(S.catalan(n)*b**(2*n)/(4**n*S.factorial(2*n)) for n in range(9))
m=S.series(S.diff(Z,b)/Z,b,0,9).removeO().expand()
assert S.expand(m-(b/4-b**3/96+b**5/1536-b**7/23040))==0
# The single-wall character moment is exactly z'/z, not z itself.
assert S.expand(S.series(m**4/4,b,0,7).removeO()-
                (b**4/1024-b**6/6144))==0
assert S.expand(S.series(m**8/4,b,0,11).removeO()-
                (b**8/262144-b**10/12288/64))==0
print('PASS SU2 exact one-face m(beta)=beta/4-beta^3/96+beta^5/1536-beta^7/23040+...')
print('PASS SU2 restricted 4d-wall response leading d=2 beta^8/262144, and d=1 beta^4/1024')
print('Finite-coupling theorem: Cov_T(F,G) = v_N * product_q E_Haar[t_q exp(beta_q*t_q)]/E_Haar[exp(beta_q*t_q)]')
print('For equal finite beta>0 and 4d walls: Cov_d=v_N*m_N(beta)^(4d), strictly geometric in d for RESTRICTED wall action')
print('OPEN unrestricted 1536-coupling Wilson covariance, CMP119 RG, absolute W3 shell, cutoff-uniform physical rate')
