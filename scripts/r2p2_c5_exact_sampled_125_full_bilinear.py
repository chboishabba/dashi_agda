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




def one_axis_transform(coefs, inverse=False):
    """Same sign and normalization as Q(zeta5) Agda forward1/inverse1."""
    output = []
    for k in range(5):
        acc = ZERO
        for j in range(5):
            phase = ROOTS[((1 if inverse else -1) * j * k) % 5]
            acc = add(acc, mul(coefs[j], phase))
        output.append(tuple(v / 5 for v in acc) if inverse else acc)
    return output


def one_axis_sampled_convolution(left, right):
    left_samples = one_axis_transform(left, inverse=True)
    right_samples = one_axis_transform(right, inverse=True)
    spectral = one_axis_transform(
        [mul(x, y) for x, y in zip(left_samples, right_samples)])
    return [tuple(5 * v for v in z) for z in spectral]


def one_axis_indexed_convolution(left, right):
    result = []
    for k in range(5):
        value = ZERO
        for p in range(5):
            value = add(value, mul(left[p], right[(k - p) % 5]))
        result.append(value)
    return result


def check_one_axis_sampled_convolution():
    # Exhaust all 25 monomial coefficient pairs; by exact bilinearity
    # this constitutes a Q(zeta5)-module basis certificate.
    for p in range(5):
        for q in range(5):
            left = [ONE if j == p else ZERO for j in range(5)]
            right = [ONE if j == q else ZERO for j in range(5)]
            assert one_axis_sampled_convolution(left, right) == (
                one_axis_indexed_convolution(left, right))
    # Nontrivial arbitrary field-level check for scalar implementation.
    for seed in range(12):
        rng = Random(5100 + seed)
        left = [tuple(F(rng.randrange(-8, 9), 7) for _ in range(4))
                for _ in range(5)]
        right = [tuple(F(rng.randrange(-8, 9), 11) for _ in range(4))
                 for _ in range(5)]
        assert one_axis_sampled_convolution(left, right) == (
            one_axis_indexed_convolution(left, right))
    print("PASS: C5 all 25 monomial basis pairs and 12 independent dense Q(zeta5) one-axis pairs")


def check_cyclotomic_ring_and_original_729_product_expansion():
    """All 64 basis triples plus three actual 27^2 pair enumerations."""
    basis = [tuple(F(int(j == i)) for j in range(4)) for i in range(4)]
    for a, b, c in product(basis, repeat=3):
        assert mul(mul(a, b), c) == mul(a, mul(b, c))
        assert mul(a, add(b, c)) == add(mul(a, b), mul(a, c))
        assert mul(add(a, b), c) == add(mul(a, c), mul(b, c))
    for seed in range(3):
        f, g = random_field(7100 + seed), random_field(7200 + seed)
        fsum = ZERO
        gsum = ZERO
        for k in INPUT:
            fsum = add(fsum, f[k])
            gsum = add(gsum, g[k])
        ordered_pair_sum = ZERO
        for p in INPUT:
            for q in INPUT:
                ordered_pair_sum = add(ordered_pair_sum, mul(f[p], g[q]))
        assert mul(fsum, gsum) == ordered_pair_sum
    print("PASS: Q(zeta5) 64 ring basis triples and 3 full original 729-term expansions")

def check():
    check_cyclotomic_ring_and_original_729_product_expansion()
    check_one_axis_sampled_convolution()
    for i in range(3):
        left, right = random_field(5100 + i), random_field(5200 + i)
        assert sampled_full_bilinear(left, right) == direct_integer_bilinear(left, right)
    print("PASS: 3 independent arbitrary Q(zeta5) field pairs, 125/125 full outputs")
    print("PASS: exact 27->125 padding, 125 inverse samples, pointwise product and forward analysis")


if __name__ == "__main__":
    check()
