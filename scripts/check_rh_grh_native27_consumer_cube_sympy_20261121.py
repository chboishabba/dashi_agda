#!/usr/bin/env python3
"""Local-only exact SymPy checks for geometric 27 and diagrammatic cube.

This does NOT check Agda or prove any analytic RH/GRH statement.
Original spatial carrier: T^3 with 54 Manhattan grid edges.
The residue digits are an invertible chart of those SAME 27 points.
"""
from itertools import product, permutations
from sympy import Matrix

points = list(product((-1, 0, 1), repeat=3))
encode = lambda p: sum((digit + 1) * (3 ** i) for i, digit in enumerate(p))
decode = lambda k: tuple((k // (3 ** i)) % 3 - 1 for i in range(3))

assert len(points) == 27
assert all(decode(encode(p)) == p for p in points)
assert all(encode(decode(i)) == i for i in range(27))
edges = {frozenset((p, q)) for n, p in enumerate(points) for q in points[n + 1:]
         if sum(abs(a - b) for a, b in zip(p, q)) == 1}
assert len(edges) == 54
succ = lambda p: decode((encode(p) + 1) % 27)
assert succ((1, 1, 1)) == (-1, -1, -1)
assert frozenset(((1, 1, 1), (-1, -1, -1))) not in edges

# An actual diagrammatic commuting cube is eight object vertices, twelve
# arrows, six faces. The three axis-zeroing maps furnish an elementary
# finite instance. This is NOT the yet-unpaid zeta/C3 six-face instance.
def proj(p, i):
    return tuple(0 if j == i else p[j] for j in range(3))

comparisons = 0
for point in points:
    for order in permutations((0, 1, 2)):
        state = point
        for axis in order:
            state = proj(state, axis)
        assert state == (0, 0, 0)
        comparisons += 1
assert comparisons == 27 * 6

# Deliberately noncommuting carry/coordinate action; do not erase residual.
witness = next(p for p in points if succ(proj(p, 0)) != proj(succ(p), 0))
assert witness == (-1, -1, -1)

# The full chart preserves any consumer; a further coarse projection need not.
coarse = lambda p: encode(p) % 3
collision = next((p, q) for p in points for q in points
                 if coarse(p) == coarse(q) and p[2] != q[2])
assert collision == ((-1, -1, -1), (-1, -1, 0))

index = {p: i for i, p in enumerate(points)}
Lgeo = Matrix.zeros(27, 27)
for edge in edges:
    p, q = tuple(edge)
    a, b = index[p], index[q]
    Lgeo[a, a] += 1
    Lgeo[b, b] += 1
    Lgeo[a, b] -= 1
    Lgeo[b, a] -= 1

Lcyc = Matrix.zeros(27, 27)
for a in range(27):
    b = (a + 1) % 27
    Lcyc[a, a] += 1
    Lcyc[b, b] += 1
    Lcyc[a, b] -= 1
    Lcyc[b, a] -= 1

assert (Lgeo.trace(), (Lgeo * Lgeo).trace()) == (108, 558)
assert (Lcyc.trace(), (Lcyc * Lcyc).trace()) == (54, 162)
print("PASS: 27/27 full geometric chart, 54 edges, six 27-state cube orders")
print("PASS: explicit noncommutation and consumer-fibre collision")
print("PASS: exact spectral moments native (108,558) != cyclic (54,162)")
