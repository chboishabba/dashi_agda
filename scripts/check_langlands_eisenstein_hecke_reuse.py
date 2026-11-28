"""Original Langlands lattice: sufficient congruence and Eisenstein decoder.
Source owners: R342 cyclic lattice; Lean EisensteinSixUnitsExact;
Agda EisensteinNineCRTPhaseMaxCutExact. No global signed integral computed.
"""
from itertools import product
import sympy as s

B = s.Matrix([[6, 21], [-7, -15]]) / 9
P = s.Matrix([[0, -3], [1, 3]])
T = s.diag(*[B] * 4) / 3
for i in range(3):
    T[2*i+2:2*i+4, 2*i:2*i+2] = s.eye(2) / 3
b = s.Matrix.hstack(*[T**i * s.eye(8)[:, 0] for i in range(8)])
bi = b.inv()

def v3(x):
    x = s.Rational(x)
    if not x:
        return 999
    a, d, n = abs(int(x.p)), int(x.q), 0
    while a % 3 == 0:
        a //= 3
        n += 1
    while d % 3 == 0:
        d //= 3
        n -= 1
    return n

assert [min(map(v3, b[:, i])) for i in range(8)] == [0,-3,-5,-8,-10,-13,-15,-18]
assert [min(map(v3, bi[i, :])) for i in range(8)] == [-4,-2,2,4,7,9,11,13]
assert v3(b.det()) == -54
assert P**2 - 3*P + 3*s.eye(2) == s.zeros(2)
# Test the additive basis of the full principal congruence, not random samples.
# For h=I+3^25 X the increment is a Z3-linear combination of these 64 matrices.
fail24 = []
for i, j in product(range(8), repeat=2):
    E = s.zeros(8)
    E[i, j] = 1
    W = bi * E * b
    assert min(map(v3, 3**25*W)) >= 3
    assert min(map(v3, (3**25*W)[7, :])) >= 20
    if min(map(v3, (3**24*W)[7, :])) < 20:
        fail24.append((i, j))
        h = s.eye(8) + 3**24*E
        assert v3(h.det()) == 0
        assert min(map(v3, (bi*h*b-s.eye(8))[7, :])) < 20
assert fail24
# Literal ramified relation: pi=1-omega; pi-basis (a,b) -> omega-basis (a+b,-b).
I = s.eye(2)
O = I-P
assert O**2+O+I == s.zeros(2) and P**2 == -3*O
units = [(1,0),(-1,0),(0,1),(0,-1),(-1,-1),(1,1)]
assert all(a*a-a*c+c*c == 1 for a,c in units)
assert len({(a%3,c%3) for a,c in units}) == 6
assert len({(a+c)%3 for a,c in units}) == 2
m = 3**49
for a,c in units:
    # 3^49 = (pi^98) as an ideal; the scaled pair decodes the exact six units.
    assert ((3**48*a)%m//3**48,(3**48*c)%m//3**48) == (a%3,c%3)
print('64 basis inclusions at depth25; depth24 failing pairs (zero based):', fail24)
print('ramified chart and six unit decoder PASS; no signed count evaluated')
