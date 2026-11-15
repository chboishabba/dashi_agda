#!/usr/bin/env python3
"""Independent exact-rational finite RG push/pull/reopening reference.

Not an Agda compiler receipt, not measurable compact SU(N) disintegration.
"""
from fractions import Fraction as Q
from random import Random

def check(seed):
    r = Random(seed)
    n = r.randrange(2, 18)
    m = r.randrange(1, n + 1)
    labels = list(range(m))
    projection = list(range(m)) + [r.choice(labels) for _ in range(n-m)]
    r.shuffle(projection)
    masses = [Q(r.randrange(1,18), r.randrange(1,12)) for _ in range(n)]
    total = sum(masses)
    weights = [x / total for x in masses]
    fibre = [sum(weights[i] for i in range(n) if projection[i] == y) for y in labels]
    assert all(v > 0 for v in fibre)
    kernel = [[weights[i] / fibre[y] if projection[i] == y else Q(0)
               for i in range(n)] for y in labels]
    assert all(sum(row) == 1 for row in kernel)
    assert all(sum(fibre[y] * kernel[y][i] for y in labels) == weights[i]
               for i in range(n))
    f = [Q(r.randrange(-30,31), r.randrange(1,25)) for _ in labels]
    pullback = [f[projection[i]] for i in range(n)]
    assert [sum(kernel[y][i] * pullback[i] for i in range(n))
            for y in labels] == f
    assert sum(weights[i] * pullback[i] for i in range(n)) == sum(
        fibre[y] * f[y] for y in labels)
    varying = [Q(r.randrange(-9,10), r.randrange(1,20)) for _ in range(n)]
    reopened = [sum(kernel[y][i] * varying[i] for i in range(n))
                for y in labels]
    assert sum(weights[i] * varying[i] for i in range(n)) == sum(
        fibre[y] * reopened[y] for y in labels)
    return n, m

def main():
    cases = [check(i) for i in range(2400)]
    print("PASS: 2400 exact finite rational partition/reopening tests")
    print("Fine states:", sum(n for n,_ in cases),
          "coarse fibres:", sum(m for _,m in cases))
    print("Checked normalization, disintegration, pullback/reopening, "
          "expectation pairing and variable-fibre reopening")
    print("REFERENCE ONLY: Agda kernel and physical SU(N) still open")

if __name__ == "__main__":
    main()
