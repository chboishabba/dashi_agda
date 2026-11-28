#!/usr/bin/env python3
"""Endpoint-first exact consequences of original G3/G4 and Cartan sources.
These are algebraic lemmas used in the terminal estimates, not existence receipts.
"""
import sympy as s
Q=s.Rational

def g3():
    # P0T actual radial conformal equation psi''+2 psi'/r=-V psi.
    # Complex radial disk |r|<=R<1, normalized central value u'(0)=1.
    R,e=s.symbols('R e',positive=True)
    V=Q(16,3)*e**2/(1-R**2)**4
    # Volterra operator on f=u/r: f=1-integral_0^1 (1-t)t r^2 V(rt) f(rt) dt.
    t=s.symbols('t',positive=True)
    k=R**2*V*s.integrate((1-t)*t,(t,0,1))
    assert s.simplify(k-Q(8,9)*e**2*R**2/(1-R**2)**4)==0
    k0=k.subs({R:Q(1,2),e:Q(1,4)})
    assert k0==Q(32,729) and k0<Q(1,2)
    # f-1 <= k/(1-k), positive complex modulus lower bound.
    assert 1-k0/(1-k0)==Q(665,697)
    print('G3 radial analytic contraction k=',k0,'normalized modulus lower bound',1-k0/(1-k0))
    print('PASS BR189 original radial conformal analytic disk bound')

def g4():
    # Original P0H stiff EOS primitive inversion with j^2.
    S,C,J=s.symbols('S C J',real=True)
    d=s.symbols('d',positive=True)
    E=(C+d)/2; P=E-C
    # d^2=(2S-C)^2-4J. w=e+p=d, gamma^2=(S+p)/d.
    assert s.expand(4*((S+P)*(S-E)-J)-((2*S-C)**2-d*d-4*J))==0
    # On physical branch S+P>0, w>0: v^2=J/(S+P)^2.
    assert s.factor((S+P)**2-(S+P)*(S-E))==s.factor(d*(S+P))
    # Exact differential of the primitive root.
    D=(2*S-C)**2-4*J
    assert s.diff(D,S)==4*(2*S-C)
    assert s.diff(D,J)==-4
    print('PASS BR190 actual P0H primitive root, timelike margin and discriminant differential')

def cartan():
    # BR142 ambient commutator energy using positive Frobenius norm:
    # E_t=-C-[Omega,E]. Verify algebraic transpose pairing for arbitrary matrices.
    O=s.Matrix(3,3,s.symbols('o:9')); E=s.Matrix(3,3,s.symbols('e:9')); C=s.Matrix(3,3,s.symbols('c:9'))
    Et=-C-O*E+E*O
    sym=(O+O.T)/2
    assert s.expand(s.trace(E.T*Et)+s.trace(E.T*C)+s.trace(E.T*sym*E)-s.trace(E.T*E*sym))==0
    print('PASS BR191 surface Cartan positive norm commutator work, no derivative of E')

if __name__=='__main__':
    import argparse
    p=argparse.ArgumentParser();p.add_argument('--part',required=True,choices=['g3','g4','cartan'])
    globals()[p.parse_args().part]()
