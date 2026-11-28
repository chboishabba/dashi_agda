#!/usr/bin/env python3
"""Exact two-slice kernel and signed branch negative controls (SymPy)."""
from sympy import Matrix, Poly, expand, simplify, symbols


def main():
    x, y = symbols('x y')
    kernel = x*y*(x-y)**2
    tests = 0
    for n in range(2, 21):
        basis = [x**(n-i)*y**i + (x**i*y**(n-i) if 2*i != n else 0)
                 for i in range(n//2+1)]
        obs = Matrix([[expand(f.subs(y, 0)).coeff(x, n) for f in basis],
                      [expand(f.subs(y, x)).coeff(x, n) for f in basis]])
        assert len(obs.nullspace()) == max(0, n//2-1)
        for v in obs.nullspace():
            f = sum(c*b for c, b in zip(v, basis))
            _, r = Poly(f, x, y).div(Poly(kernel, x, y))
            assert r.is_zero
            tests += 1
    print('19 graded ranks and', tests, 'kernel basis divisibilities PASS')
    A, B, C, beta, S2, lam, gamma = symbols('A B C beta S2 lam gamma', nonzero=True)
    u = x/A-B*x**2/A**3+(2*B**2/A**5-C/A**4)*x**3
    F = expand(A*beta*u+B*beta**2*u**2+C*beta**3*u**3).series(x, 0, 4).removeO()
    assert simplify(F.coeff(x, 3).diff(C)-(beta**3-beta)/A**3) == 0
    Q = S2*(x*x-(beta+1/beta)*x*y+y*y)
    perturb = lam*kernel
    assert simplify(perturb.subs(y, 0)) == simplify(perturb.subs(y, x)) == 0
    assert simplify(expand((Q+perturb).subs(y, beta*x+gamma*x**3)).coeff(x, 4)
                    -S2*(beta-1/beta)*gamma-lam*beta*(1-beta)**2) == 0
    print('branch cubic / normalized disk third coefficient perturbation PASS')
    N, M, p, s, R, T, D = symbols('N M p s R T D')
    hp, ha, hT = M*D-x*x*p, N*R-x*x*s, D-R-x*T
    goal = (N*p-M*s)*x*x-N*M*x*T
    assert expand(-N*hp+M*ha+N*M*hT-goal) == 0
    assert expand(N*hp-M*ha+N*M*hT-goal) != 0
    print('literal source orientation and wrong-sign negative control PASS')
    # Literal selected Hecke indices under the original S/T permutations.
    P = 41
    S = lambda i: 0 if i == P else P if i == 0 else (-pow(i, -1, P)) % P
    Tperm = lambda i: P if i == P else (i+1) % P
    assert {S(i) for i in (0, 1)} == {40, 41}
    assert {Tperm(i) for i in (0, 1)} == {1, 2}
    assert all(S(S(i)) == i for i in range(P+1))
    assert all(Tperm(i) == i if i == P else (Tperm(i)-1) % P == i for i in range(P+1))
    print('selected-mask covariance and all 42 inverse coordinates PASS')


if __name__ == '__main__':
    main()
