from itertools import product

P = 3
POINTS = list(product(range(3), repeat=3))
RADICAL = {(0, 0, 0), (1, 0, 2), (2, 0, 1)}


def q(p):
    x, y, z = p
    return (((x + z) % 3) ** 2 + y * y) % 3


def rho(p):
    return {0: 0, 1: 1, 2: -1}[q(p)]


def add(a, b):
    return tuple((a[i] + b[i]) % 3 for i in range(3))


def cosets():
    unseen = set(POINTS)
    out = []
    while unseen:
        p = next(iter(unseen))
        c = frozenset(add(p, r) for r in RADICAL)
        out.append(c)
        unseen -= c
    return out


def intrinsic_adjacent(p, r):
    d = tuple((r[i] - p[i]) % 3 for i in range(3))
    return p != r and q(d) != 0


def verify():
    cs = cosets()
    assert len(cs) == 9
    assert all(len(c) == 3 for c in cs)
    assert all(len({q(p) for p in c}) == 1 for c in cs)
    qclasses = sorted(next(iter({q(p) for p in c})) for c in cs)
    assert qclasses.count(0) == 1
    assert qclasses.count(1) == 4
    assert qclasses.count(2) == 4

    # Intrinsic graph: no edges inside a radical coset; all edges across cosets.
    for i, ci in enumerate(cs):
        for j, cj in enumerate(cs):
            for p in ci:
                for r in cj:
                    if i == j:
                        assert not intrinsic_adjacent(p, r)
                    else:
                        assert intrinsic_adjacent(p, r)

    # Fiber-constant mean-zero field: L f = 27 f on each coset.
    # Use rho as canonical witness (coset values 0,+1,-1, total weighted sum 0).
    for c in cs:
        p = next(iter(c))
        fp = rho(p)
        lap = 0
        for r in POINTS:
            if intrinsic_adjacent(p, r):
                lap += fp - rho(r)
        assert lap == 27 * fp

    return {
        "radical": sorted(RADICAL),
        "radical_size": 3,
        "quotient_coset_count": 9,
        "quotient_q_classes": (1, 4, 4),
        "intrinsic_graph": "complete 9-partite graph with part size 3",
        "fiber_constant_laplacian": "L = 27 I on mean-zero quotient functions",
        "source_constant_on_radical_fibres": True,
    }


if __name__ == "__main__":
    for k, v in verify().items():
        print(f"{k}: {v}")
