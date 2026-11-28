#!/usr/bin/env python3
"""Section32 original CMP102 odd/even Fin row exact generic coefficients.

No factorial assumptions: every a_j and b_j is an independent SymPy
symbol. This checks the actual ORIGINAL oddPart/evenPart singleton and
shifted Cauchy formulas, native SeriesOf count 1..16, both Fin row
identities, and the final original five-term G-to-wings source.
This is NOT an Agda kernel run and not a proof by sample enumeration.
"""
import sympy as sp

X = sp.Symbol("X")
checks = 0
for count in range(1, 17):
    a = sp.symbols(f"a0:{count}")
    b = sp.symbols(f"b0:{count}")
    A = sum((a[k]*X**k for k in range(count)), sp.Integer(0))
    B = sum((b[k]*X**k for k in range(count)), sp.Integer(0))

    def coefficient(v, k):
        return sum((v[i]*v[k-i] for i in range(k+1)
                    if i<count and k-i<count), sp.Integer(0))

    odd = sum(
        (1 if k == 0 else
         2*b[k-1]+(coefficient(b,k-2) if k>=2 else 0))*X**k
        for k in range(count))
    even = sum(
        (2*a[k]+(coefficient(a,k-1) if k>=1 else 0))*X**k
        for k in range(count))
    TA = sum((coefficient(a,k)*X**k for k in range(count-1)),
             sp.Integer(0))
    TB = sum((coefficient(b,k)*X**k
              for k in range(max(count-2,0))), sp.Integer(0))
    assert sp.expand(even-2*A-X*TA) == 0
    checks += 1
    assert sp.expand(odd-1-2*X*(B-b[count-1]*X**(count-1))
                     -X**2*TB) == 0
    checks += 1
    G = 1-2*A-X*A*A+2*X*B+X*X*B*B
    wing = -X*(A*A-TA)+2*X*b[count-1]*X**(count-1)+X*X*(B*B-TB)
    assert sp.expand(G-(odd-even+wing)) == 0
    checks += 1

assert checks == 48
print("CMP102 ORIGINAL ODD/EVEN FIN ROW GENERIC: 48/48 PASS")
print("arbitrary symbols, all count-indexed endpoints c=1..16")
