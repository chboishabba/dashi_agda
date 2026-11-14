"""Attributed negative control for a stated unconditional 2026 flux estimate.

Original source: Luca Eliseo Pavesi, "Global Regularity for the
Three-Dimensional Incompressible Navier–Stokes Equations via
Geometric Frustration and Helical Quasi-Trapping", Zenodo 21194906,
2026-07-04 v3. The abstract states a universal |Pi(K)| <=
C sqrt(E_>K)*sqrt(E)/K for an absolute C.

This independently checks the conventional NS spectral flux on a
real smooth transverse triad. The cubic/energy-quadratic mismatch
rules out that UNCONDITIONAL, amplitude-independent inequality for
that definition. It does not disprove separately conditional
helicity-dominance estimates or settle the paper's full argument.
"""
import sympy as s
I=s.I
P=(1,0,0); Q=(0,1,2); K=(1,1,2)
U={P:s.Matrix([0,1,1]), Q:s.Matrix([1,0,0]),
   K:I*s.Matrix([1,-1,0])}
U.update({tuple(-x for x in m):s.conjugate(v)
          for m,v in list(U.items())})

def norm2(k): return sum(x*x for x in k)
def nonlinear(k,u):
    kvec=s.Matrix(k)
    source=s.zeros(3,1)
    for p,up in u.items():
        q=tuple(k[j]-p[j] for j in range(3))
        if q in u: source+=s.Matrix(q).dot(up)*u[q]
    return -I*(source-kvec*kvec.dot(source)/norm2(k))
def flux(cut,u):
    return s.simplify(-2*sum(
        s.re((s.conjugate(v).T*nonlinear(k,u))[0])
        for k,v in u.items() if norm2(k)<=cut*cut))
def energies(cut,u):
    E=sum((s.conjugate(v).T*v)[0] for v in u.values())
    tail=sum((s.conjugate(v).T*v)[0] for k,v in u.items()
             if norm2(k)>cut*cut)
    return s.simplify(E),s.simplify(tail)

def test_conventional_flux_nonzero_and_absolute_constant_scaling_no_go():
    assert all(s.Matrix(k).dot(v)==0 for k,v in U.items())
    assert flux(1,U)==4
    assert energies(1,U)==(10,6)
    for a in (1,2,10):
        scaled={k:a*v for k,v in U.items()}
        assert flux(1,scaled)==4*a**3
        assert energies(1,scaled)==(10*a*a,6*a*a)
    a,C=s.symbols("a C",positive=True)
    # Flux/claimed RHS *C^-1 = (4/sqrt(60))*a, unbounded.
    ratio=s.simplify(4*a**3/(s.sqrt(10*a*a)*s.sqrt(6*a*a)))
    assert s.simplify(ratio-4*a/s.sqrt(60))==0
