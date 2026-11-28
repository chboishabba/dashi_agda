"""Exact reference for the original signed defect and both Euler streams."""
from fractions import Fraction
from hashlib import sha1
from pathlib import Path
import sympy as sp

A, B, C, M = 13591409, 545140134, 640320**3, 2**41
k, w, m, a, v = sp.symbols('k w m a v')
assert sp.expand(a*(k*w*m)-(a*k)*w*m) == 0
assert sp.expand(v*w*m-m*(w*v)) == 0
assert B >= A > 0 and M > 1
P = Q = 1
H = J = S = Fraction(0)
terms = []
for n in range(257):
    if n:
        P *= -(6*n-5)*(2*n-1)*(6*n-1)*24
        Q *= C*n**3
    weight = A+B*n
    u = Fraction(P,Q)
    assert M**n*abs(P)*weight <= A*Q
    for k in (0, 1, n, weight//A):
        assert A*k <= weight
        assert k*abs(P)*M**n <= Q
        assert abs(k*u) <= Fraction(1,M**n)
    # The original recurrence is retained, including its sign and zero mode.
    assert (u > 0) == (n % 2 == 0)
    H += u
    J += n*u
    S += weight*u
    assert S == A*H+B*J
    terms.append((u,n*u))
    if n:
        assert S != A*H-B*J
# Quantitative finite-tail envelope for either stream, not a proof of convergence.
for start in range(33):
    for stop in range(start,65):
        bound = Fraction(M,M-1)*Fraction(1,M**start)
        for d in (0,1):
            assert abs(sum((terms[n][d] for n in range(start,stop)),Fraction(0))) <= bound
# A multiplier outside the admissible region need not satisfy the bound.
assert A*2 > A and abs(2*terms[0][0]) > 1
assert terms[0] == (1,0)
b = Path(__file__).read_bytes()
print('PASS: 2 symbolic rearrangements; 257 original defects; 1028 multiplier cases; 257 weighted splits; 256 sign controls; 3234 finite-tail checks; 2 boundary controls')
print('git blob',sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest())
