from itertools import product

P = 3
B = (
    (2, 2, 0, 0, 0),
    (2, 2, 2, 0, 2),
    (0, 2, 2, 2, 0),
    (0, 0, 2, 2, 0),
    (0, 2, 0, 0, 2),
)
E_PLUS = (
    (1, 1, 1),
    (0, 0, 2),
    (0, 1, 2),
    (2, 0, 2),
    (0, 0, 1),
)
E_MINUS = (
    (0, 0, 0),
    (0, 0, 0),
    (0, 0, 1),
    (1, 1, 1),
    (1, 2, 2),
)
G_PLUS = ((1, 0, 1), (0, 1, 0), (1, 0, 1))
G_MINUS = ((1, 0, 2), (0, 1, 0), (2, 0, 1))


def dot_b(u, v):
    return sum(u[i] * B[i][j] * v[j] for i in range(5) for j in range(5)) % P


def gram(E):
    cols = [tuple(E[i][j] for i in range(5)) for j in range(3)]
    return tuple(tuple(dot_b(cols[i], cols[j]) for j in range(3)) for i in range(3))


def matvec(E, u):
    return tuple(sum(E[i][j] * u[j] for j in range(3)) % P for i in range(5))


def canon(v):
    for a in v:
        if a:
            inv = 1 if a == 1 else 2
            return tuple(inv * x % P for x in v)
    raise ValueError("zero")


def q5(v):
    return dot_b(v, v)


def projective_patch(E):
    return {canon(matvec(E, u)) for u in product(range(3), repeat=3) if any(u)}


def det3(M):
    return (
        M[0][0] * (M[1][1] * M[2][2] - M[1][2] * M[2][1])
        - M[0][1] * (M[1][0] * M[2][2] - M[1][2] * M[2][0])
        + M[0][2] * (M[1][0] * M[2][1] - M[1][1] * M[2][0])
    ) % 3


def verify():
    assert gram(E_PLUS) == G_PLUS
    assert gram(E_MINUS) == G_MINUS
    aggregate = tuple(
        tuple((G_PLUS[i][j] + G_MINUS[i][j]) % 3 for j in range(3))
        for i in range(3)
    )
    assert aggregate == ((2, 0, 0), (0, 2, 0), (0, 0, 2))
    assert det3(aggregate) != 0

    pplus = projective_patch(E_PLUS)
    pminus = projective_patch(E_MINUS)
    assert pplus != pminus
    assert len(pplus) == len(pminus) == 13
    assert len(pplus & pminus) == 1
    common = next(iter(pplus & pminus))
    assert q5(common) == 2

    rad_plus = canon(matvec(E_PLUS, (1, 0, 2)))
    rad_minus = canon(matvec(E_MINUS, (1, 0, 1)))
    assert rad_plus == (0, 1, 1, 0, 2)
    assert rad_minus == (0, 0, 1, 2, 0)
    assert rad_plus != rad_minus
    assert q5(rad_plus) == q5(rad_minus) == 0

    return {
        "plus_gram": G_PLUS,
        "minus_gram": G_MINUS,
        "aggregate_gram": aggregate,
        "aggregate_rank": 3,
        "plus_radical": rad_plus,
        "minus_radical": rad_minus,
        "patch_intersection_size": 1,
        "common_root_line": common,
        "co_registration_required": True,
    }


if __name__ == "__main__":
    for k, v in verify().items():
        print(f"{k}: {v}")
