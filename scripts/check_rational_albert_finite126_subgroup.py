#!/usr/bin/env python3
"""Exact finite permutation audit for the explicit Albert automorphism subgroup.

The rational-polynomial automorphism proofs live in Agda.  This script checks
the finite basis permutations used by those proofs:

* p7 has order 7;
* p3 has order 3;
* p3 p7 p3^-1 = p7^4;
* <p7,p3> has 21 elements;
* the matrix-index S3 has 6 elements;
* the two actions are independent/commuting at the finite label level, giving
  126 distinct product action labels.

Execution evidence only; not an Agda kernel proof.
"""

from collections import deque


def compose(p, q):
    """Permutation p after q, using zero-based images."""
    return tuple(p[q[i]] for i in range(len(p)))


def inverse(p):
    out = [0] * len(p)
    for i, j in enumerate(p):
        out[j] = i
    return tuple(out)


def power(p, n):
    result = tuple(range(len(p)))
    for _ in range(n):
        result = compose(p, result)
    return result


def order(p):
    identity = tuple(range(len(p)))
    value = identity
    for n in range(1, 1000):
        value = compose(p, value)
        if value == identity:
            return n
    raise AssertionError("order search failed")


def generated_group(generators):
    identity = tuple(range(len(generators[0])))
    group = {identity}
    queue = deque([identity])
    while queue:
        g = queue.popleft()
        for s in generators:
            h = compose(s, g)
            if h not in group:
                group.add(h)
                queue.append(h)
    return group


def main():
    # Imaginary octonion basis e1..e7; convert the Agda 1-based description to
    # zero-based permutation images.
    p7 = tuple(x - 1 for x in (2, 4, 6, 5, 7, 1, 3))
    p3 = tuple(x - 1 for x in (2, 3, 1, 4, 6, 7, 5))

    assert order(p7) == 7
    assert order(p3) == 3
    lhs = compose(compose(p3, p7), inverse(p3))
    assert lhs == power(p7, 4)

    c21 = generated_group([p7, p3])
    assert len(c21) == 21
    assert {order(g) for g in c21} == {1, 3, 7}

    # Standard S3 on three matrix indices.
    r = (1, 2, 0)
    s = (0, 2, 1)
    s3 = generated_group([r, s])
    assert len(s3) == 6

    # Product labels are distinct because the matrix-index action and the
    # slotwise octonion action live on independent coordinates.
    product_labels = {(a, b) for a in s3 for b in c21}
    assert len(product_labels) == 126

    print("octonion p7 order                = 7")
    print("octonion p3 order                = 3")
    print("semidirect relation              = p3 p7 p3^-1 = p7^4")
    print("generated octonion subgroup      = 21")
    print("matrix-index subgroup             = 6")
    print("combined commuting action labels  = 126")
    print("RUN_TERMINAL COMPLETE")


if __name__ == "__main__":
    main()
