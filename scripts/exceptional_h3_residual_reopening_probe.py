from itertools import product

P = 3
R = (1, 0, 2)
ELL = (1, 0, 2)


def dot(a, b):
    return sum(x*y for x, y in zip(a, b)) % 3


def add(a, b):
    return tuple((x+y) % 3 for x, y in zip(a, b))


def scale(t, a):
    return tuple((t*x) % 3 for x in a)


def q(v):
    x, y, z = v
    return ((x+z)*(x+z) + y*y) % 3


def phase(v):
    return dot(ELL, v)


def split(v):
    # ell(R)=2, whose inverse is 2 mod 3.
    t = (2 * phase(v)) % 3
    k = add(v, scale((-t) % 3, R))
    return k, t


def reopen(k, t):
    return add(k, scale(t, R))


def verify():
    points = list(product(range(3), repeat=3))
    kernel = [v for v in points if phase(v) == 0]
    assert len(kernel) == 9
    assert phase(R) == 2

    pairs = set()
    for v in points:
        k, t = split(v)
        assert phase(k) == 0
        assert reopen(k, t) == v
        pairs.add((k, t))
        for s in range(3):
            assert q(add(v, scale(s, R))) == q(v)

    assert len(pairs) == 27
    assert len({q(v) for v in points}) == 3

    return {
        "carrier_states": 27,
        "phase_kernel_states": 9,
        "phase_values": 3,
        "radical_phase_value": phase(R),
        "quadratic_constant_on_all_radical_cosets": True,
        "split_reopen_roundtrip_all_states": True,
        "kernel_times_phase_pairs": len(pairs),
        "phase_is_exact_reopening_residual": True,
        "phase_is_three_h3_patch_fibre": False,
    }


if __name__ == "__main__":
    for k, v in verify().items():
        print(f"{k}: {v}")
