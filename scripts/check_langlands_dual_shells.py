"""R388-R390: exact original cyclic chart, Fourier gates and shell mass arithmetic."""
from math import inf
from itertools import product
import sympy as s

p = s.Integer(3)
def val(x):
    x = s.Rational(x)
    if not x:
        return inf
    a, b = abs(int(x.p)), int(x.q)
    k = 0
    while a % 3 == 0:
        a //= 3
        k += 1
    while b % 3 == 0:
        b //= 3
        k -= 1
    return k

def grade(x):
    return min(2*val(x[i])+i%2 for i in range(8))

B = s.Matrix([[6,21],[-7,-15]])/9
P = s.Matrix([[0,-3],[1,3]])
X = s.Matrix.hstack(s.eye(2)[:,0], B[:,0])
q = s.diag(*[B**i*X*s.diag(p**(7-2*i),p**(6-2*i)) for i in range(4)])
pi = s.diag(*[P]*4)
T = s.diag(*[B/3]*4)
for i in range(1,4):
    T[2*i:2*i+2,2*i-2:2*i] = s.eye(2)/3
b = s.Matrix.hstack(*[T**i*s.eye(8)[:,0] for i in range(8)])
bi = b.inv()
assert val(q.det()) == 2 and val(b.det()) == -54
assert grade(q[:,0]) == 14
assert [grade(b[:,i]) for i in range(8)] == [-5*i for i in range(8)]
assert min(grade(b[:,i])-40 for i in range(7)) == -70
assert grade(b[:,7])-2 == -37
unit = pi**2/3
assert all(val(x)>=0 for x in unit) and all(val(x)>=0 for x in unit.inv())
rows = 0
for k in range(-20,91):
    A = bi*pi**(14-k)
    assert min(map(val,A)) == 3-(k+1)//2
    assert min(map(val,A[7,:])) == 20-k//2
    rows += 1
# Integer Ramanujan sums by exact residue counts; primitive characters of 3^d.
z = s.Symbol('z')
checks = 0
for d in range(1,6):
    n = 3**d
    Phi = s.Poly(s.cyclotomic_poly(n,z),z)
    # All possible valuation classes, including zero, and all unit multipliers.
    for a in range(n):
        # Count the exponents by residues; complete geometric series minus multiples of 3.
        c = [0]*n
        for u in range(n):
            if u%3:
                c[(u*a)%n] += 1
        # Phi(z)=z^(2*n/3)+z^(n/3)+1; reduce without floating roots.
        h = n//3
        rem = [c[i]-c[i+2*h] for i in range(h)] + [c[i+h]-c[i+2*h] for i in range(h)]
        expected = n-h if a==0 else -h if a%h==0 else 0
        assert rem == [expected]+[0]*(2*h-1)
        checks += 1
p7 = s.prod(1-p**(-i) for i in range(1,8))
p8 = p7*(1-p**-8)
C = p**-126/p7
V8 = p**-184/p8
mass = 80*V8/C
assert mass == 80*p**-58/(1-p**-8)
Z = p**-160/(1-p**-8)
assert p**-160*mass == Z*p**-54*s.Rational(80,81)
print(dict(shell_chart=rows, ramanujan=checks, tail_max=27, boundary=(28,70), mass=str(mass)))
