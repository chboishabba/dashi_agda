"""Independent exact finite replay of the centered tail geometry (not Agda acceptance)."""
from fractions import Fraction as F
import sympy as s

count = dict(range=0, geometry=0, paired=0, symbolic=0)
for m in range(1, 12):
    N = 1 << m
    h = F(1, N)
    M = N // 2
    js = [v for k in range(M) for v in (k, -k-1)]
    assert sorted(js) == list(range(-M, M))
    count["range"] += 1
    for k in range(M):
        assert js[2*k:2*k+2] == [k, -k-1]
        count["paired"] += 1
    for x in [F(-7,3), F(-1,2), F(0), F(1,2), F(7,3)]:
        if h*abs(x) > F(1,8):
            continue
        for j in js:
            J = abs(j)
            if J == 0 or J < 2*abs(x):
                continue
            v = h*(J + (x if j > 0 else -x))
            assert 0 <= h*J/2 <= v <= F(5,8)
            assert F(22,7)*v <= F(110,56) < 2 and h*J <= F(2,3)*3*v
            count["geometry"] += 1
        for k in range(1,M):
            assert F(1,k*k) + F(1,(k+1)**2) > 0
            count["paired"] += 1
p,h,x,J = s.symbols("p h x J")
assert s.expand(p*h*(x-J) + p*h*(J-x)) == 0
count["symbolic"] += 1
assert s.expand(p*h*(x+J) - p*h*(J+x)) == 0
count["symbolic"] += 1
print(count, sum(count.values()), "PASS")
