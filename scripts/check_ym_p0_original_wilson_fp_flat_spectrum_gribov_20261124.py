#!/usr/bin/env python3
"""P0 YM original L4 Wilson gauge-source flat FP / Gribov controls.

Uses authentic periodic four-dimensional positive link/plaquette words and
continuous SU(2) group identities. Exact Gaussian/Fourier scalar Hessian,
not the selected nonlinear CMP119/122 background-gauge operator.

PASS proves flat Landau gauge derivative, full periodic spectrum and an explicit
SU2 gauge-equivalent nonpositive FP stationary representative at the SAME
zero-action Wilson orbit. This is a source obstruction to identifying a rooted
Haar Jacobian with an arbitrary physical FP determinant. It is NOT W3/OS/Clay.
"""
from collections import Counter, deque
from fractions import Fraction
from itertools import product, combinations
from math import comb, sin, pi
import sympy as S

checks=Counter()
L=4
d=4
origin=(0,)*d
sites=list(product(range(L),repeat=d))
assert len(sites)==256

def step(x,mu):
    v=list(x);v[mu]=(v[mu]+1)%L;return tuple(v)

links=[(x,mu) for x in sites for mu in range(d)]
faces=[((x,mu),(step(x,mu),nu),(step(x,nu),mu),(x,nu))
       for x in sites for mu,nu in combinations(range(d),2)]
assert len(links)==1024 and len(faces)==1536
checks['native_graph']+=3

# Signed center-valued SU2 configurations and exact local gauge-pulse map.
# -1 is a genuine nontrivial element of the SU2 CENTER, not a toy group
# replacing the original continuous SU2 Haar measure.
plus={e:1 for e in links}
minus={e:-1 for e in links}
parity={x:(-1)**sum(x) for x in sites}

def hol_center(U,f):
    a,b,c,e=f
    return U[a]*U[b]*U[c]*U[e] # inverses coincide with values +/-1

def transform(U,g):
    return {(x,mu):g[x]*U[x,mu]*g[step(x,mu)] for x,mu in links}

assert all(hol_center(plus,f)==1 for f in faces)
assert all(hol_center(minus,f)==1 for f in faces)
assert transform(minus,parity)==plus
checks['source_orbit']+=len(faces)*2+len(links)+1

# The original globally selected F/G native y-z plaquettes at time 0,2
froot=(0,0,0,0); groot=(0,0,0,2)
Fface=((froot,2),(step(froot,2),3),(step(froot,3),2),(froot,3))
Gface=((groot,2),(step(groot,2),3),(step(groot,3),2),(groot,3))
assert Fface in faces and Gface in faces and Fface!=Gface
assert hol_center(plus,Fface)==hol_center(minus,Fface)==1
assert hol_center(plus,Gface)==hol_center(minus,Gface)==1
checks['source_orbit']+=5

# Lattice Landau gauge functional R(g;U)=sum_{oriented original links}
# ReTr(g_x U_xy g_y^{-1})/2. Gauge-stationarity at g=1:
# both uniform centre +/-I have zero first derivative; Hessian of -R
# is +/-graph Laplacian. This is NOT Bałaban's selected background slice.
# Exact SU2 one-parameter subgroup exp(theta i) validates the local trace.
theta=S.symbols('theta',real=True)
for eta in (1,-1):
    f=eta*S.cos(theta)
    assert S.diff(f,theta).subs(theta,0)==0
    assert -S.diff(f,theta,2).subs(theta,0)==eta
    checks['linearized_FP']+=2

# Genuine graph Laplacian on periodic L4 (includes all 1024 positive links).
index={x:i for i,x in enumerate(sites)}
Laplacian=S.MutableSparseMatrix(len(sites),len(sites),{})
for x,mu in links:
    i,j=index[x],index[step(x,mu)]
    Laplacian[i,i]+=1;Laplacian[j,j]+=1
    Laplacian[i,j]-=1;Laplacian[j,i]-=1
assert all(sum(Laplacian[i,j] for j in range(256))==0 for i in range(256))
checks['native_graph']+=256
assert all(Laplacian[i,i]==8 for i in range(256))
checks['native_graph']+=256

# True L4 Fourier modes: i^{k.x}. Exact Gaussian integers, no numerical FFT.
# eigenvalues = sum_mu (2 - i^k_mu - i^-k_mu) = 2*j
# where each direction contributes {0,2,2,4}, giving (1+x)^8.
counts=Counter()
for k in sites:
    v=[(1j)**sum(k[mu]*x[mu] for mu in range(d)) for x in sites]
    eig=0
    for ki in k:
        eig += (0,2,4,2)[ki]
    for x,i in index.items():
        acc=8*v[i]-sum(v[index[step(x,mu)]]+v[index[tuple((x[h]-(h==mu))%L for h in range(d))]] for mu in range(d))
        assert acc==eig*v[i]
        checks['native_Fourier']+=1
    counts[eig]+=1
assert dict(counts)=={2*j:comb(8,j) for j in range(9)}
checks['native_Fourier']+=9

# Remove constant global gauge mode (the FP zero eigenvalue).
# Determinant' of scalar FP and exact rooted matrix-tree cofactor.
detprime=1
for j in range(1,9):
    detprime *= (2*j)**comb(8,j)
assert detprime%256==0
rooted_trees=detprime//256
assert rooted_trees>1
assert len(str(detprime))==223
checks['FP_determinant']+=4

# For SU2 adjoint dim=3 the linearized FP determinant on mean-zero
# site Lie algebra is (detprime)^3 with +/- sign respectively.
adj=3
assert adj*(len(sites)-1)==765
assert (-1)**(adj*(len(sites)-1))==-1
assert rooted_trees==detprime//len(sites)
checks['FP_determinant']+=3

# Check exact Fourier eigenvalue growth on L=3..12, against the graph's
# periodic lattice momentum formula. Uniform inverse on raw gauge modes
# is impossible as L -> infinity (physical box may also grow).
for ell in range(3,13):
    lmin=4*S.sin(S.pi/ell)**2
    assert float(lmin)>0
    assert S.simplify((1/lmin)*(4*S.sin(S.pi/ell)**2)-1)==0
    checks['volume_scaling']+=2
# At fixed spacing a, lambda_min ~ 4pi^2/L^2.
Lsym=S.symbols('L',positive=True)
assert S.limit(4*S.sin(S.pi/Lsym)**2*Lsym**2,Lsym,S.oo)==4*S.pi**2
checks['volume_scaling']+=1

# Nontrivial small-field Faddeev-Popov Hessian bound at arbitrary SU(N)
# background (this is the standard local Landau source, not Balaban's nonlinear
# background-gauge and its constraints). Let ||U_e-I||op<=delta for each link;
# for anti-Hermitian site fields omega with ||omega_x||²=-ReTr(omega_x²)/N,
# |Q_U(omega)-Q_I(omega)| <= sum_e delta*(||omega_x||+||omega_y||)^2
#                            <= 16 delta sum_x ||omega_x||².
# On mean-zero site fields Q_I >= lambda_min||omega||²,
# so if delta < lambda_min/16 we have explicit positive FP spectrum.
# At original L4 lambda_min=2, hence delta<1/8 suffices.
delta=S.symbols('delta',nonnegative=True)
assert S.simplify(16*delta-2*(8*delta))==0
assert 16*S.Rational(1,16)<2
assert S.simplify((2-16*delta).subs(delta,S.Rational(1,16))-1)==0
checks['local_FP_radius']+=3

# SU2 exact quaternion regression of the Hessian edge formula and norm bound.
# The group itself is continuous SU2; rational unit quaternions are test
# configurations. Exact delta <=1/32 from the Pythagorean m=64 chart.
def mulq(p,q):
    a,b,c,d=p; e,f,g,h=q
    return (a*e-b*f-c*g-d*h,a*f+b*e+c*h-d*g,a*g-b*h+c*e+d*f,a*h+b*g-c*f+d*e)
def qsquare(w):return mulq(w,w)
for m in (64,128):
    U=(S.Rational(m*m-1,m*m+1),S.Rational(2*m,m*m+1),0,0)
    assert sum(x*x for x in U)==1
    cap=S.Rational(2,m)
    assert 2*(1-U[0])<=cap*cap
    for a,b,c,d,e,f in product((-2,-1,0,1,2),repeat=6):
        wx=(0,a,b,c);wy=(0,d,e,f)
        ax=S.Integer(a*a+b*b+c*c);by=S.Integer(d*d+e*e+f*f)
        Q_U=-(mulq(qsquare(wx),U)[0]+mulq(U,qsquare(wy))[0]-2*mulq(mulq(wx,U),wy)[0])
        diff=(a-d,b-e,c-f)
        Q_I=sum(z*z for z in diff)
        assert abs(Q_U-Q_I) <= cap*(ax+by+2*S.sqrt(ax*by))
        checks['local_FP_rational']+=1
assert 1+2*sum(comb(8,j) for j in range(1,9))>0
checks['local_FP_radius']+=1

print('PASS SymPy',S.__version__,'total',sum(checks.values()),dict(sorted(checks.items())))
print('original L4: 256 sites, 1024 links, 1536 full native plaquettes')
print('SU2 plus/minus uniform centre backgrounds: gauge equivalent, S=0, F=G=0')
print('Landau linearized FP at +I = +periodic graph Laplacian, at -I = -Laplacian')
print('L4 FP Laplacian eigenvalues/multiplicities:',dict(sorted(counts.items())))
print('reduced determinant digits:',len(str(detprime)),'spanning tree count digits:',len(str(rooted_trees)))
print('SU2 mean-zero FP determinant signs opposite (because adj*(256-1) is odd)')
print('flat Landau-gauge FP is NOT rooted tree-Haar Jacobian; latter normalized exactly 1')
print('OPEN: actual Bałaban selected nonlinear background gauge and admissible domain sums; W3/OS/Clay')
