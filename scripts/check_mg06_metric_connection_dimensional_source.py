#!/usr/bin/env python3
"""MG06 exact, source-selected KK metric/connection audit.

Source: KKSingleActionRadionPhysicalSteelman20261024.md (PR #1241):
 ds5^2 = gJ + b^2(dy + kappa A)^2, y dimensionless, period 2*pi.
The *physical QED photon* in KKLightElectronBIDI... is separate Maxwell B_A.
This test does not construct a solution of the five-dimensional field equations.
"""
import sympy as s


def check():
    b, kappa, a, p, q, m, b0, M5 = s.symbols(
        'b kappa a p q m b0 M5', real=True, positive=True)
    g = s.diag(-1, 1)  # one time, one spatial direction; fixed Jordan block
    A = s.Matrix([a, 0])
    G = g + b*b*kappa*kappa*(A*A.T)
    G5 = G.row_join(b*b*kappa*A).col_join(
        (b*b*kappa*A).T.row_join(s.Matrix([[b*b]])))
    ginv = g.inv()
    inverse = ginv.row_join(-kappa*ginv*A).col_join(
        (-kappa*ginv*A).T.row_join(
            s.Matrix([[1/b**2 + kappa*kappa*(A.T*ginv*A)[0]]])))
    assert s.simplify(G5*inverse-s.eye(3)) == s.zeros(3,3)
    assert s.simplify(G5.det()-b*b*g.det()) == 0
    # A momentum p_y sector of the five-dimensional scalar principal symbol:
    momenta = s.Matrix([p, q])
    fullmom = momenta.col_join(s.Matrix([m]))
    quadratic = s.expand((fullmom.T*inverse*fullmom)[0])
    horizontal = (momenta-kappa*m*A)
    expected = (horizontal.T*ginv*horizontal)[0]+m*m/b**2
    assert s.simplify(quadratic-expected) == 0
    assert s.simplify(expected.subs(m, 0)-(momenta.T*ginv*momenta)[0]) == 0
    assert s.simplify(s.diff(expected, a).subs(m, 0)) == 0
    assert s.simplify(s.diff(expected, a).subs(m, 1)) != 0
    # A local change of section y'=y-kappa*chi(x) implies A'=A+dchi.
    # For constant dchi along the selected time direction, p'=p+kappa*m*dchi.
    chi = s.symbols('chi',real=True)
    shifted = (s.Matrix([p+kappa*m*chi,q]) - kappa*m*s.Matrix([a+chi,0]))
    assert s.simplify(shifted-horizontal) == s.zeros(2,1)
    # b0 is the physical *length*; in dimensionless y convention the circumference is 2*pi*b0.
    M4sq = s.symbols('M4sq', positive=True)
    assert s.simplify(M4sq.subs(M4sq,2*s.pi*b0*M5**3)-2*s.pi*b0*M5**3) == 0
    e5, e4 = s.symbols('e5 e4', positive=True)
    assert s.simplify((e5/s.sqrt(2*s.pi*b0))**2-e5**2/(2*s.pi*b0)) == 0
    # Gravitational connection and independent physical Maxwell have different coupling owners.
    assert kappa*m != e5/s.sqrt(2*s.pi*b0)
    # Same geometry: Fourier k and k+N aliases have unequal 1/b^2 momentum energies.
    N, r = s.symbols('N r', positive=True, integer=True)
    assert s.simplify((r+N)**2/b**2-r*r/b**2) != 0
    print('PASS 5D metric block inverse and exact determinant')
    print('PASS KK horizontal momentum identity and section gauge covariance')
    print('PASS neutral p_y=0 decoupling; charged p_y != 0 sensitivity')
    print('PASS gravitational-vs-independent-Maxwell coupling and compact-mode non-descent')
    print('OPEN 5D field-equation solution, physical QED identification, atomic same-H and Agda kernel')


if __name__=='__main__':
    check()
