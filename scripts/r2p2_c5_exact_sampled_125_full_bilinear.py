"""Exact 125-sample Q(zeta_5) padded quadratic full-output diagnostic.

Independent arithmetic, not a substitute for the Agda sampled-index bridge.
Historical roots: finite Fourier orthogonality and Patterson/Orszag dealiasing.
Repository sources: original 27/729/125 integer operator and Q(zeta5) owners.
"""
from fractions import Fraction as F
from itertools import product
from random import Random

INPUT = tuple(product((-1, 0, 1), repeat=3))
GRID = tuple(product(range(5), repeat=3))
OUT = tuple(product(range(-2, 3), repeat=3))
ZERO = (F(0), F(0), F(0), F(0))
ONE = (F(1), F(0), F(0), F(0))
ZETA = (F(0), F(1), F(0), F(0))


def add(a, b):
    return tuple(x + y for x, y in zip(a, b))


def mul(a, b):
    s = [F(0)] * 5
    for i in range(4):
        for j in range(4):
            s[(i + j) % 5] += a[i] * b[j]
    return tuple(s[i] - s[4] for i in range(4))


ROOTS = [ONE]
for _ in range(4):
    ROOTS.append(mul(ROOTS[-1], ZETA))
assert mul(ROOTS[-1], ZETA) == ONE


def axis_transform(values, axis, inverse=False):
    result = {}
    for k in GRID:
        s = ZERO
        for j in range(5):
            key = tuple(j if i == axis else k[i] for i in range(3))
            root = ROOTS[((1 if inverse else -1) * j * k[axis]) % 5]
            s = add(s, mul(values[key], root))
        result[k] = tuple(x / 5 for x in s) if inverse else s
    return result


def tensor_transform(values, inverse=False):
    for axis in ((0, 1, 2) if inverse else (2, 1, 0)):
        values = axis_transform(values, axis, inverse)
    return values


def random_field(seed):
    rng = Random(seed)
    return {
        k: tuple(F(rng.randrange(-4, 5), 7) for _ in range(4))
        for k in INPUT
    }


def direct_integer_bilinear(left, right):
    result = {k: ZERO for k in OUT}
    for p in INPUT:
        for q in INPUT:
            k = tuple(x + y for x, y in zip(p, q))
            result[k] = add(result[k], mul(left[p], right[q]))
    return result


def sampled_full_bilinear(left, right):
    def pad(field):
        return {
            k: field.get(tuple((x if x <= 2 else x - 5) for x in k), ZERO)
            for k in GRID
        }

    l = tensor_transform(pad(left), inverse=True)
    r = tensor_transform(pad(right), inverse=True)
    sampled_product = {
        k: mul(tuple(x * 125 for x in l[k]),
               tuple(x * 125 for x in r[k])) for k in GRID
    }
    spectral = tensor_transform(sampled_product)
    return {
        k: tuple(x / 125 for x in spectral[tuple(v % 5 for v in k)])
        for k in OUT
    }


def check():
    for i in range(3):
        left, right = random_field(5100 + i), random_field(5200 + i)
        assert sampled_full_bilinear(left, right) == direct_integer_bilinear(left, right)
    print("PASS: 3 independent arbitrary Q(zeta5) field pairs, 125/125 full outputs")
    print("PASS: exact 27->125 padding, 125 inverse samples, pointwise product and forward analysis")


if __name__ == "__main__":
    check()
