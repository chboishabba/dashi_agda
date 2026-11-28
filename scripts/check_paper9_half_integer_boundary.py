"""Independent exact finite and symbolic diagnostics; not Agda acceptance."""
from fractions import Fraction as F
import sympy as s

counts = dict(half_integer=0, uniform_norm=0, power_majorant=0, parity=0, normalization=0)
for j in range(256):
    a = F(2*j+1, 2)
    b = F(1, (j+1)**2)
    assert a >= F(j+1,2) and F(1,a) == 2*F(1,2*j+1)
    counts['half_integer'] += 2
    for y in (F(0), F(1,64), F(1,16), F(1,4), F(1), F(7,3)):
        d = a*a + y*y
        assert F(1,d) <= 4*b
        counts['uniform_norm'] += 1
        for w in (4,6):
            assert F(1,d**(w//2)) <= 2**w*b
            counts['power_majorant'] += 1
    for w in (4,6):
        assert F(1,(2*j+2)**w) == F(1,2**w)*F(1,(j+1)**w)
        assert 1/a**w + 1/(-a)**w == 2**(w+1)*F(1,(2*j+1)**w)
        counts['parity'] += 2
for w in (4,6):
    for n in (1,2,3,8,16,64,128):
        full = sum(F(1,j**w) for j in range(1,2*n+1))
        odd = sum(F(1,(2*j+1)**w) for j in range(n))
        half = sum(F(1,(j+1)**w) for j in range(n))
        assert full == odd + F(1,2**w)*half
        counts['parity'] += 1
p = s.symbols('p', real=True)
X = -s.Rational(1,4)
for w, row, den, coefficient in ((4,X+6*X**2,90,240),(6,X+30*X**2+120*X**3,945,-504)):
    target = s.expand((2*s.I*p)**w/s.factorial(w-1)*row)
    assert s.expand(target-2*(2**w-1)*p**w/den) == 0
    assert s.expand((2*s.I*p)**w/s.factorial(w-1)-coefficient*p**w/den) == 0
    counts['normalization'] += 2
print(counts, sum(counts.values()), 'PASS')
