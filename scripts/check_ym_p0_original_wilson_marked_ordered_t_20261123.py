#!/usr/bin/env python3
"""P0.T: full L4 Wilson plaquettes on 10-link SU(2)-centre slice.
Source 1,F,G,FG transported through actual native R445 F19 pair-fibres;
not continuous SU(N) Haar, CMP119's domain T, W3 or Clay completion.
"""
from fractions import Fraction as Q
from itertools import combinations, product

L = 4
sites = list(product(range(L), repeat=4))
links = [(x, mu) for x in sites for mu in range(4)]


def step(x, axis):
    y = list(x)
    y[axis] = (y[axis] + 1) % L
    return tuple(y)


def face(x, a, b):
    return ((x, a), (step(x, a), b), (step(x, b), a), (x, b))


faces = [face(x, a, b) for x in sites for a, b in combinations(range(4), 2)]
assert (len(sites), len(links), len(faces)) == (256, 1024, 1536)
F = (0, 0, 0, 0)
G = (0, 0, 0, 2)
p0 = ((F, 2), (step(F, 2), 2))
p1 = ((G, 2), (step(G, 2), 2))
spectators = tuple(
    [((0, 0, 0, z), 2) for z in (1, 3)] +
    [((0, 0, 1, z), 3) for z in range(4)]
)
active = p0 + p1 + spectators
assert len(active) == len(set(active)) == 10
selected = set()
for c in product(range(2), repeat=4):
    for a in range(4):
        o = tuple(2 * v for v in c)
        selected.update(((o, a), (step(o, a), a)))
assert len(selected) == 128 and len(set(links) - selected) == 896
assert set(p0 + p1) <= selected and set(spectators).isdisjoint(selected)
index = {b: i for i, b in enumerate(active)}


def mask(bonds):
    m = 0
    for bond in bonds:
        if bond in index:
            m ^= 1 << index[bond]
    return m


pm = [mask(p) for p in faces]
fm = mask(face(F, 2, 3))
gm = mask(face(G, 2, 3))
assert fm and gm and fm != gm


def weight_marks(bits):
    bad = sum((bits & m).bit_count() % 2 for m in pm)
    f = 1 - 2 * ((bits & fm).bit_count() % 2)
    g = 1 - 2 * ((bits & gm).bit_count() % 2)
    w = Q(1, 2) ** bad
    return (w, w * f, w * g, w * f * g)


def coarse(bits):
    return ((bits & 1) ^ ((bits >> 1) & 1),
            ((bits >> 2) & 1) ^ ((bits >> 3) & 1))


def from_f19(w0, v0, w1, v1, sp):
    bits = [w0 ^ v0, v0, w1 ^ v1, v1] + list(sp)
    return sum(b << i for i, b in enumerate(bits))


def add(a, b):
    return tuple(x + y for x, y in zip(a, b))


zero = (Q(0),) * 4
by_w = {w: zero for w in product(range(2), repeat=2)}
flat = zero
for bits in range(1024):
    q = weight_marks(bits)
    flat = add(flat, q)
    w = coarse(bits)
    by_w[w] = add(by_w[w], q)

for w0, w1 in by_w:
    total = zero
    for v0 in range(2):
        continuation = zero
        for v1 in range(2):
            for sp in product(range(2), repeat=6):
                continuation = add(
                    continuation,
                    weight_marks(from_f19(w0, v0, w1, v1, sp))
                )
        total = add(total, continuation)
    assert total == by_w[w0, w1]

assert flat == tuple(sum(by_w[k][j] for k in by_w) for j in range(4))
assert all(flat[j] / 1024 == sum(by_w[k][j] / 256 for k in by_w) / 4
           for j in range(4))


def hessian(v):
    a, b, c, d = v
    assert a > 0
    return (a * d - b * c) / a ** 2


covs = {k: hessian(v) for k, v in by_w.items()}
assert all(v != 0 for v in covs.values())
assert min(covs.values()) < 0 < max(covs.values())
Z, ZF, ZG, ZFG = flat
fibre = sum(v[0] / Z * hessian(v) for v in by_w.values())
coarse_cov = sum(
    v[0] / Z * (v[1] / v[0] - ZF / Z) * (v[2] / v[0] - ZG / Z)
    for v in by_w.values()
)
assert hessian(flat) == fibre + coarse_cov
for s, t in product((Q(-9, 100), Q(0), Q(9, 100)), repeat=2):
    for a, b, c, d in (flat, *by_w.values()):
        K = a + s * b + t * c + s * t * d
        assert K > 0
        assert (d * K - (b + t * d) * (c + s * d)) / K ** 2 == (
            (a * d - b * c) / K ** 2
        )

print('PASS 1536 original plaquettes; 64 R445 pairs; 896 spectator slots')
print('PASS 1024 restricted Z2 states; 4/4 W-fibre four-column ordered-T equality')
print('PASS normalized finite Haar; 9 real tilts; exact mixed log determinant')
print('PASS original covariance fibre+between; 4/4 nonzero, mixed signs')
print('Global covariance:', hessian(flat))
print('Conditional covariance:', covs)
print('OPEN continuous SU(N) Haar, physical CMP119/122 T, absolute W3, OS gap')
