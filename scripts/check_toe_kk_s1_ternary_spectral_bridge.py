#!/usr/bin/env python3
"""TOE hyperfabric -> KK S1: operator-level spectral and holonomy BIDI.

Compare three distinct 27-site objects: spatial P3^3 (source #1249),
periodic C3^3, and C27 discretising ONE compact KK circle.
Construct genuine ternary N=3^k C_N finite-difference KK spectra,
gauge-covariant U1 links and fixed-band heat trace with an O(N^-2)
error bound. No full renormalised Casimir or physical SM is claimed.

Prior mathematics: cycle Fourier diagonalisation, (De)Constructing
Dimensions, Arkani-Hamed, Cohen, Georgi, PRL 86 (2001) 4757,
DOI 10.1103/PhysRevLett.86.4757. Authors own deconstruction idea.
"""
from collections import Counter
from itertools import product
from math import sin, pi, exp, cos
import cmath

def path_spectrum_27():
    # One P3 graph Laplacian: {0,1,3}; Cartesian product has sums.
    return Counter(sum(t) for t in product((0,1,3),repeat=3))

def periodic_torus_spectrum_27():
    # One C3 laplacian: {0,3,3}.
    return Counter(sum(t) for t in product((0,3,3),repeat=3))

def cycle_eigen_dimless(N,n,alpha):
    # b^2 times the physical finite-difference eigenvalue, L=2*pi*b.
    return (N/pi)**2*sin(pi*(n+alpha)/N)**2

def continuum_eigen_dimless(n,alpha):
    return (n+alpha)**2

def check_27_mismatch():
    path=path_spectrum_27()
    torus=periodic_torus_spectrum_27()
    assert path == Counter({0:1,1:3,2:3,3:4,4:6,5:3,6:3,7:3,9:1})
    assert torus == Counter({0:1,3:6,6:12,9:8})
    # P3^3 has 54 edges (degrees 3..6), C3^3 has 81 edges
    # (degree 6), C27 has 27 edges (degree 2).
    assert (3*3**3*2//3,3*3**3,27)==(54,81,27)
    assert len(path)==9 and len(torus)==4
    assert sum(path.values())==sum(torus.values())==27
    # #1249's P3^3 -> P3^6 -> P3^9 increases the NUMBER OF AXES,
    # not the spatial resolution of one fixed S1 dimension.
    # Every P3 axis has first excited eigenvalue 1. Thus the P3^d
    # spectral gap has multiplicity d, vs 2 for smooth periodic S1.
    for d in (3,6,9):
        assert sum(1 for t in product((0,1,3),repeat=d) if sum(t)==1)==d
        assert d!=2
        print(f"PASS P3^{d}: site count={3**d}, first gap degeneracy={d}, smooth S1 degeneracy=2")
    print("PASS 27-site inequivalent operators: P3^3, C3^3, C27")
    print(" path 27 spectrum",dict(sorted(path.items())))
    print(" torus 27 spectrum",dict(sorted(torus.items())))

def check_modes_and_heat():
    K=3
    t=.23
    for alpha in (0.,.17,.5):
        previous=None
        for N in (9,27,81,243,729):
            assert N>2*(K+abs(alpha))
            err=0.
            bound=0.
            heat=0.
            for n in range(-K,K+1):
                k=n+alpha
                theta=pi*k/N
                assert abs(theta)<1
                lattice=cycle_eigen_dimless(N,n,alpha)
                smooth=continuum_eigen_dimless(n,alpha)
                delta=smooth-lattice
                # Exact analytic inequality: 0 <= 1-sinc(z)^2 <= z^2/3
                # (for |z|<=1, follows from sin(z)>=z-z^3/6).
                per_mode=pi*pi*k**4/(3*N*N)
                assert -1e-12<=delta<=per_mode+1e-12
                err=max(err,abs(delta))
                heat += exp(-t*lattice)-exp(-t*smooth)
                bound += t*per_mode
            assert -1e-12<=heat<=bound+1e-12
            if previous is not None:
                assert err<previous
            previous=err
            print(f"PASS alpha={alpha:.2f} N={N:>3} "
                  f"max eigen err={err:.9g} "
                  f"fixed-band heat err={heat:.9g} "
                  f"certified bound={bound:.9g}")
    # Finite-mode alias: n and n+N sample to same C_N Fourier
    # character, but smooth KK eigenvalues differ by N^2 at theta=0.
    for N in (3,9,27,729):
        assert abs(cycle_eigen_dimless(N,0,0)-cycle_eigen_dimless(N,N,0))<1e-18
        assert continuum_eigen_dimless(0,0)!=continuum_eigen_dimless(N,0)
    print("PASS spectral non-descent: sampled n and n+N indistinguishable on C_N, physically different on S1")

def check_u1_parallel_transport():
    for N in (3,9,27,81):
        for total_theta in (0.,.4,pi):
            links=[cmath.exp(1j*total_theta/N) for _ in range(N)]
            hol=1+0j
            for x in links: hol*=x
            assert abs(hol-cmath.exp(1j*total_theta))<1e-12
            n=1
            f=[cmath.exp(2j*pi*n*j/N) for j in range(N)]
            lam=4*sin((2*pi*n+total_theta)/(2*N))**2
            for j in range(N):
                lf=(2*f[j]-links[j]*f[(j+1)%N]
                    -links[(j-1)%N].conjugate()*f[(j-1)%N])
                assert abs(lf-lam*f[j])<1e-12
            # A nontrivial local U1 site gauge preserves the spectrum.
            g=[cmath.exp(1j*(.1*j*j+.04*j)) for j in range(N)]
            Lg=[g[j]*links[j]*g[(j+1)%N].conjugate() for j in range(N)]
            fg=[g[j]*f[j] for j in range(N)]
            holg=1+0j
            for x in Lg: holg*=x
            assert abs(holg-hol)<1e-12
            for j in range(N):
                lg=(2*fg[j]-Lg[j]*fg[(j+1)%N]
                    -Lg[(j-1)%N].conjugate()*fg[(j-1)%N])
                assert abs(lg-lam*fg[j])<1e-12
    print("PASS gauge-covariant U1 circle spectrum, Wilson product, local gauge intertwiner")

if __name__=="__main__":
    check_27_mismatch()
    check_modes_and_heat()
    check_u1_parallel_transport()
    print("LIMIT: fixed-band eigen/heat consumer only; no full KK Casimir determinant, continuum local gauge action, or physical TOE.")
