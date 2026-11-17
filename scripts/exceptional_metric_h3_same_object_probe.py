from itertools import product

P = 3
B = (
    (2, 2, 0, 0, 0),
    (2, 2, 2, 0, 2),
    (0, 2, 2, 2, 0),
    (0, 0, 2, 2, 0),
    (0, 2, 0, 0, 2),
)
E = (
    (1, 1, 1),
    (0, 0, 2),
    (0, 1, 2),
    (2, 0, 2),
    (0, 0, 1),
)
TARGET_GRAM = (
    (1, 0, 1),
    (0, 1, 0),
    (1, 0, 1),
)
ZERO5 = (0, 0, 0, 0, 0)


def matvec(m, v):
    return tuple(sum(m[i][j] * v[j] for j in range(len(v))) % P for i in range(len(m)))


def dot_b(u, v):
    return sum(u[i] * B[i][j] * v[j] for i in range(5) for j in range(5)) % P


def q5(v):
    return dot_b(v, v)


def canon(v):
    for a in v:
        if a:
            inv = 1 if a == 1 else 2
            return tuple(inv * x % P for x in v)
    raise ValueError("zero")


def restricted_gram():
    cols = [tuple(E[i][j] for i in range(5)) for j in range(3)]
    return tuple(tuple(dot_b(cols[i], cols[j]) for j in range(3)) for i in range(3))


def all_projective_lines():
    return sorted({canon(v) for v in product(range(3), repeat=5) if any(v)})


def subspace_lines():
    return sorted({canon(matvec(E, u)) for u in product(range(3), repeat=3) if any(u)})


def verify():
    assert restricted_gram() == TARGET_GRAM
    lines = all_projective_lines()
    roots = [v for v in lines if q5(v) == 2]
    nulls = [v for v in lines if q5(v) == 0]
    sub = subspace_lines()
    assert len(sub) == 13
    sub_roots = [v for v in sub if v in roots]
    sub_nulls = [v for v in sub if v in nulls]
    sub_other = [v for v in sub if q5(v) == 1]
    assert (len(sub_nulls), len(sub_roots), len(sub_other)) == (1, 6, 6)

    local_radical = (1, 0, 2)
    radical_line = canon(matvec(E, local_radical))
    assert radical_line == (0, 1, 1, 0, 2)
    assert q5(radical_line) == 0
    assert all(dot_b(radical_line, x) == 0 for x in sub)

    perp_roots = [r for r in roots if all(dot_b(r, x) == 0 for x in sub)]
    assert len(perp_roots) == 3
    a2cube = sorted(set(sub_roots + perp_roots))
    assert len(a2cube) == 9

    return {
        "embedding": E,
        "restricted_gram": TARGET_GRAM,
        "projective_patch_size": 13,
        "patch_signature_null_root_other": (1, 6, 6),
        "radical_line": radical_line,
        "perpendicular_root_lines": tuple(perp_roots),
        "a2_cubed_root_line_count": len(a2cube),
        "a2_cubed_root_lines": tuple(a2cube),
    }


if __name__ == "__main__":
    for k, v in verify().items():
        print(f"{k}: {v}")
