#!/usr/bin/env python3
"""MG06 observer-indexed smooth S1 spectral control without altering native P3^3.

The finite C_N operator is an explicitly separate compact-fibre model.
Its holonomy and radius are INPUTS; neither comes from 5D field equations.
"""
from itertools import product
from math import pi, sin, sqrt
import numpy as np
import sympy as sp


def native_cube():
    points=list(product((-1,0,1), repeat=3))
    edges=[(i,j) for i,p in enumerate(points) for j,q in enumerate(points)
           if i<j and sum(abs(a-b) for a,b in zip(p,q))==1]
    B=sp.zeros(len(edges),len(points))
    for e,(i,j) in enumerate(edges):
        B[e,i]=-1; B[e,j]=1
    return B.T*B,len(edges)


def twisted_cycle(n,radius,theta):
    """Directed covariant edges U=e^(i theta/n); theta is Wilson angle."""
    lattice_spacing=2*pi*radius/n
    U=np.exp(1j*theta/n)
    B=np.zeros((n,n),dtype=np.complex128)
    for j in range(n):
        B[j,j]=1
        B[j,(j+1)%n]=-U
    return (B.conj().T@B)/lattice_spacing**2


def lattice_energy(n,k,theta,radius):
    nu=k+theta/(2*pi)
    a=2*pi*radius/n
    return 4*sin(pi*nu/n)**2/a**2


def continuum_energy(k,theta,radius):
    return (k+theta/(2*pi))**2/radius**2


def check():
    native,bonds=native_cube()
    assert native.shape==(27,27) and bonds==54
    assert sp.trace(native)==108 and native*sp.ones(27,1)==sp.zeros(27,1)
    source_fingerprint=(native.shape,bonds,sp.trace(native))
    samples=0; max_ratio=0
    for n,radius,theta,k in product((9,15,27,54),(1.,2.),(0.,pi/2,pi),range(-2,3)):
        nu=k+theta/(2*pi)
        assert 2*abs(nu)<n, (n,k,theta)
        C=twisted_cycle(n,radius,theta)
        v=np.exp(2j*pi*k*np.arange(n)/n)/sqrt(n)
        lam=lattice_energy(n,k,theta,radius)
        err=np.linalg.norm(C@v-lam*v)
        assert err < 2e-10, (n,radius,theta,k,err)
        assert np.allclose(C,C.conj().T,atol=1e-12)
        smooth=continuum_energy(k,theta,radius)
        bound=pi*pi*nu**4/(3*radius*radius*n*n)
        delta=smooth-lam
        assert delta>=-2e-13 and delta<=bound+2e-13, (n,k,theta,delta,bound)
        if bound: max_ratio=max(max_ratio,delta/bound)
        samples+=1
    assert samples==120
    for theta in (0.,pi/2,pi):
        n=27; k=1
        v=np.exp(2j*pi*k*np.arange(n)/n)
        v_alias=np.exp(2j*pi*(k+n)*np.arange(n)/n)
        assert np.max(np.abs(v-v_alias)) < 5e-14
        assert continuum_energy(k+n,theta,1.)!=continuum_energy(k,theta,1.)
    for radius in (1.,2.):
        for theta in (0.,pi/2,pi):
            k=1
            e9=continuum_energy(k,theta,radius)-lattice_energy(9,k,theta,radius)
            e54=continuum_energy(k,theta,radius)-lattice_energy(54,k,theta,radius)
            assert 0<e54<e9
    assert (native.shape,bonds,sp.trace(native))==source_fingerprint
    print('PASS 120/120 Fourier mode eigenvalue predictions and analytic O(N^-2) error bounds')
    print('PASS 3/3 Fourier alias witnesses, 6/6 mesh refinement comparisons')
    print('PASS native P3^3 unchanged: 27 vertices, 54 bonds, trace 108')
    print(f'Max observed error/bound ratio = {max_ratio:.8f}')
    print('OPEN physical 5D KK action/observer, Wilson angle, electron, atomic Hamiltonian, Agda kernel')


if __name__=='__main__':
    check()
