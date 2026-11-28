#!/usr/bin/env python3
"""Exact symmetric jet section, minimal slope repair, and quartic scalar."""
from sympy import Matrix, Rational, Poly, expand, rem, symbols, factor


def main():
    x, y = symbols('x y')
    u, v = x+y, x*y
    for n in range(2, 21):
        m = n//2
        basis = [u**(n-2*j)*v**j for j in range(m+1)]
        slopes = list(range(m+1))
        q = [Rational(k, (1+k)**2) for k in slopes]
        assert len(set(q)) == m+1
        obs = Matrix([[f.subs({x: 1, y: k}) for f in basis] for k in slopes])
        assert obs.det() != 0
        assert obs[:2, :].rank() == 2
        S, P = symbols('S P')
        section = S*u**n+(P-2**n*S)*u**(n-2)*v/2**(n-2)
        assert expand(section.subs(y, 0)-S*x**n) == 0
        assert expand(section.subs(y, x)-P*x**n) == 0
    print('19 canonical sections and minimal slope interpolation ranks PASS')
    b,t,L,C,S2,S3,H,S4,U,V = symbols('b t L C S2 S3 H S4 U V')
    delta = L*(b*b-b)
    gamma = C*(b**3-b)+2*L**2*(b-b*b)
    E = S2*((2*b-t)*gamma+delta**2)+delta*(3*S3*b*b+H*(1+2*b)) \
        +S4*(1+b**4)+U*(b+b**3)+V*b*b
    residue = rem(expand(E*(t-b)**2), b*b-t*b+1, b)
    residue = expand(residue.subs(H,L*(2-t)*S2-(t-1)*S3))
    scalar = (t*t-4)*(S2*C+L*S3)-L**2*S2*(t-2)*(t+1) \
        +(t*t-2)*S4+t*U+V
    assert expand(residue-scalar) == 0
    lam = symbols('lam')
    assert expand(scalar.subs({U:U+lam,V:V-2*lam})-scalar-lam*(t-2)) == 0
    assert factor(-lam*(t-2)/(S2*(t*t-4))+lam/(S2*(t+2))) == 0
    print('quartic orientation-independent scalar and perturbation shift PASS')


if __name__ == '__main__':
    main()
