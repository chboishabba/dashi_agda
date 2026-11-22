#!/usr/bin/env python3
"""Exact finite C3-sector faithfulness regression downstream of ORIGINAL Wilson Q8 Gram.

Donor: scripts/check_ym_eisenstein_c3_original_wilson_gram_20261122.py
(4096 Q8 4-link Wilson Gibbs configurations, not SU2 Haar).

Only the centered three-observable finite Wilson covariance is source-derived.
A vacuum, a formal Gram-null fibre, and sectorwise transfer energies are
EXPLICIT COUNTERMODELS, not an original YM OS reflection form/Hamiltonian.
No artificial model is promoted to an interacting continuum mass gap.
"""
from sympy import Matrix, eye, zeros, diag, Rational, I, sqrt, simplify, S

checks = 0

def equal(a,b):
    if isinstance(a,Matrix):
        return a.shape==b.shape and all(simplify(v)==0 for v in a-b)
    return simplify(a-b)==0

def check(ok,desc):
    global checks
    assert ok,desc
    checks+=1

# The EXACT finite covariance measured from the original Q8/Wilson Gibbs
# reference (not a reflection-positive *time-dependent* OS Gram).
mu=Rational(13684,15451)
G0=Matrix(3,3,lambda i,j: (1 if i==j else Rational(12541,15451))-mu**2)
lam0=Rational(64519815,238733401)
lam12=Rational(2910,15451)
R=Matrix([[0,0,1],[1,0,0],[0,1,0]])
omega=(-1+sqrt(3)*I)/2
check(equal(R**3,eye(3)),"C3 order")
check(equal(1+omega+omega**2,0),"root cancellation is not scalar phase zero")
check(equal(R.T*G0*R,G0),"source Q8 centered Gram C3 invariance")

# Projectors at eigencharacters 1, omega, omega^2.
chars=(S.One,omega,omega**2)
P=[(eye(3)+c**(-1)*R+c**(-2)*R**2)/3 for c in chars]
for i in range(3):
    check(equal(P[i]*P[i],P[i]),f"P{i} idempotence")
    check(equal(R*P[i],chars[i]*P[i]),f"P{i} character eigenaction")
    check(equal(P[i].conjugate().T,P[i]),f"P{i} Hermitian")
    check(equal(P[i].trace(),1),f"P{i} rank 1")
    for j in range(i):
        check(equal(P[i]*P[j],zeros(3)),f"P{i}P{j} orthogonality")
check(equal(sum(P,zeros(3)),eye(3)),"three character sectors exhaustive")
check(equal(G0,lam0*P[0]+lam12*(P[1]+P[2])),"source Gram exact Fourier resolution")
check(lam0>0 and lam12>0,"positive source Gram on all 3 sectors")

# Explicit source-Gram finite isometry to FOUR quotient-like coordinates:
# vacuum (new), one C3-invariant Wilson and two conjugate C3 Wilson sectors.
# Add ONE FORMAL pre-quotient null coordinate. This is NOT an actual OS null.
V=Matrix.hstack(*[Matrix([1, c**(-1), c**(-2)])/sqrt(3) for c in chars])
check(equal(V.conjugate().T*V,eye(3)),"unitary Fourier basis")
check(equal(R*V,V*diag(*chars)),"Fourier basis intertwines C3")
D=diag(*[sqrt(lam0),sqrt(lam12),sqrt(lam12)])
U=zeros(4,5)
U[0,0]=1
U[1:4,1:4]=D*V.conjugate().T
G5=diag(1,1,1,1,0)
G5[1:4,1:4]=G0
R5=diag(1,1,1,1,1)
R5[1:4,1:4]=R
check(equal(U.conjugate().T*U,G5),"finite isometry / formal null quotient")
check(equal(R5.conjugate().T*G5*R5,G5),"C3 preserves formal Gram-null")
check(equal(U*R5,diag(1,*chars)*U),"C3 descends across null quotient")
check(equal(U*Matrix([0,0,0,0,1]),zeros(4,1)),"formal null maps to zero")
check(not equal(U*Matrix([1,0,0,0,0]),zeros(4,1)),"vacuum not quotient-null")
check(not equal(U*Matrix([0,1,omega**2,omega,0]),zeros(4,1)),"Fourier cancelling nonempty vector survives")

# Countermodel: for each n a positive finite-dimensional gap 1/n exists,
# but ALL n share no positive uniform gap. An invariant-only Wilson test
# sees e^-2t and misses two slow (omega/omega^2) modes.
for n in (2,3,7,31,127):
    Hq=diag(0,2,Rational(1,n),Rational(1,n))
    Hpre=diag(0,1,1,1,0)
    Hpre[1:4,1:4]=2*P[0]+Rational(1,n)*(P[1]+P[2])
    check(equal(U*Hpre,Hq*U),f"same model prequotient/quotient operator at n={n}")
    check(equal(Hpre*R5,R5*Hpre),f"C3 and H commute at n={n}")
    check(equal(Hpre.conjugate().T*G5,G5*Hpre),f"quotient selfadjoint at n={n}")
    check(Hq[1,1]==2 and Hq[2,2]==Rational(1,n),f"hidden slow sector at n={n}")
    check(Hq[1,1]>Hq[2,2]>0, f"strict positive mode no uniform bound at n={n}")

# For any m>0 and n>1/m, the two nontrivial character eigenenergies 1/n<m.
# This symbolic Archimedean consequence is the exact source-independent
# obstruction; the finite loop above merely exercises the explicit matrices.
print(f"PASS {checks}/{checks} exact symbolic C3 / Wilson-covariance / null / spectral-countermodel checks")
print("Original finite Wilson Q8 Gram character eigenvalues:",lam0,lam12,lam12)
print("Finite isometry rank:",U.rank(),"prequotient Gram rank:",G5.rank())
print("Witness: invariant-only mode energy 2; two missed C3 modes energy 1/n")
print("OPEN: original full-SU(N) Wilson Gibbs C3 invariance, complex OS RP Gram, E1 quotient, physical semigroup, source decay and actual D2 gap.")
