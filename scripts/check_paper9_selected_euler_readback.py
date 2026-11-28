#!/usr/bin/env python3
"""Independent exact finite diagnostics; not a kernel or convergence receipt."""
from fractions import Fraction
import sympy as s


def main():
    N = 64
    z = s.symbols('z')
    q, t = s.Integer(0), s.Integer(0)
    for n in range(N + 1):
        assert s.expand(z*q - n*z**n) == 0, ('first wing', n)
        assert s.expand(z*q + 2*z*z*t - n*n*z**n) == 0, ('second wing', n)
        q, t = s.expand(z**n + z*q), s.expand(q + z*t)
    print(f'PASS: {N+1} first and {N+1} second diagonal wings')
    def mul(a, b):
        return [sum(a[k]*b[n-k] for k in range(n+1)) for n in range(N+2)]
    def sub(a, b):
        return [x-y for x,y in zip(a,b)]
    def add(a, b):
        return [x+y for x,y in zip(a,b)]
    def der(a):
        return [n*x for n,x in enumerate(a)]
    def sigma(n, k):
        return sum(d**k for d in s.divisors(n))
    X = [1]+[240*sigma(n,3) for n in range(1,N+2)]
    Y = [1]+[-504*sigma(n,5) for n in range(1,N+2)]
    E = [1]+[-24*sigma(n,1) for n in range(1,N+2)]
    X3 = mul(mul(X,X),X)
    disc = sub(X3,mul(Y,Y))
    assert disc[0] == 0
    U = [Fraction(int(v),1728) for v in disc[1:]]+[0]
    assert U[0] == 1
    inv = [Fraction(1)]
    for n in range(1,N+2):
        inv.append(-sum(U[k]*inv[n-k] for k in range(1,n+1)))
    J = mul(X3,inv)
    J1,J2 = der(J),der(der(J))
    L1,L2 = sub(J1,J),add(sub(J2,add(J1,J1)),J)
    first = add(mul(X,L1),mul(Y,J))
    second = add(add(mul(X,L2),mul(add(der(X),Y),L1)),mul(der(Y),J))
    flow = sub(J1,sub(J,mul(mul(mul(X,X),Y),inv)))
    for name, row in [('normalized flow',flow),('cleared first',first),('cleared second',second)]:
        assert row[:N+1] == [0]*(N+1), name
        print(f'PASS: {N+1} coefficients {name}')
    # Independent scalar quotient chain-rule algebra, with the original q*j relation.
    q,j,j1,j2 = s.symbols('q j j1 j2', nonzero=True)
    Jv=q*j; Jp=j+q*j1; Jpp=j1+q*j2
    e1=q*j1; e2=q*j1/2+q*q*j2
    assert s.expand(q*e1-(q*Jp-Jv)) == 0
    assert s.expand(2*q*e2-(q*Jp+2*q*q*Jpp-2*q*Jp+Jv)) == 0
    print('PASS: 2 scalar quotient-chain identities')
    print('327/327 exact checks PASS (finite diagnostic only)')


if __name__ == '__main__':
    main()
