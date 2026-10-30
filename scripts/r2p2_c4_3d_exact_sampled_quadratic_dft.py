"""Exact Q(i) C4^3 sampled quadratic convolution benchmark.

Mathematical provenance: finite-group character orthogonality, historical
pseudo-spectral padding/dealiasing (Orszag/Patterson); no new physics claim.
"""
from fractions import Fraction
from itertools import product
from random import Random

K = tuple(product((-1, 0, 1), repeat=3))
X = tuple(product(range(4), repeat=3))
ZERO = (Fraction(0), Fraction(0))
ONE = (Fraction(1), Fraction(0))
I = (Fraction(0), Fraction(1))


def add(a, b):
    return a[0] + b[0], a[1] + b[1]


def mul(a, b):
    return a[0] * b[0] - a[1] * b[1], a[0] * b[1] + a[1] * b[0]


def mul_frac(a, q):
    return a[0] * q, a[1] * q


def phase(n):
    return (ONE, I, (-ONE[0], ONE[1]), (-I[0], -I[1]))[n % 4]


def chi(k, x):
    return phase(sum(a * b for a, b in zip(k, x)))


def sum_complex(xs):
    v = ZERO
    for x in xs:
        v = add(v, x)
    return v


def samples(f):
    return {x: sum_complex(mul(f[k], chi(k, x)) for k in K) for x in X}


def sampled_product(f, g):
    uf = samples(f)
    vg = samples(g)
    w = {x: mul(uf[x], vg[x]) for x in X}
    return {
        k: mul_frac(
            sum_complex(mul(w[x], chi(tuple(-a for a in k), x)) for x in X),
            Fraction(1, 64),
        )
        for k in K
    }


def direct(f, g):
    return {
        k: sum_complex(
            mul(f[p], g[q])
            for p in K for q in K
            if tuple(a + b for a, b in zip(p, q)) == k
        )
        for k in K
    }




def one_axis_transform(coefs, inverse=False):
    """Same Q(i) sign and 1/4 inverse normalization as Agda forward1/inverse1."""
    out = []
    for k in range(4):
        coeff = sum_complex(
            mul(coefs[j], phase((1 if inverse else -1) * j * k))
            for j in range(4))
        out.append(mul_frac(coeff, Fraction(1, 4)) if inverse else coeff)
    return out


def one_axis_cyclic_convolution(left, right):
    return [
        sum_complex(mul(left[j], right[(k - j) % 4]) for j in range(4))
        for k in range(4)
    ]


def one_axis_sampled_convolution(left, right):
    a = one_axis_transform(left, inverse=True)
    b = one_axis_transform(right, inverse=True)
    sampled = [mul(x, y) for x, y in zip(a, b)]
    return [mul_frac(z, 4) for z in one_axis_transform(sampled)]


def check_one_axis_sampled_convolution():
    # All 16 monomial basis products, every output. This is a bilinear
    # Q(i)-module basis audit, rather than only random-profile testing.
    for p in range(4):
        for q in range(4):
            left = [ONE if j == p else ZERO for j in range(4)]
            right = [ONE if j == q else ZERO for j in range(4)]
            assert one_axis_sampled_convolution(left, right) == (
                one_axis_cyclic_convolution(left, right))
    for seed in range(12):
        rng = Random(27004 + seed)
        left = [(Fraction(rng.randrange(-8, 9), 7),
                 Fraction(rng.randrange(-8, 9), 7)) for _ in range(4)]
        right = [(Fraction(rng.randrange(-8, 9), 11),
                  Fraction(rng.randrange(-8, 9), 11)) for _ in range(4)]
        assert one_axis_sampled_convolution(left, right) == (
            one_axis_cyclic_convolution(left, right))
    print("PASS: C4 all 16 one-axis monomial pairs and 12 arbitrary dense Q(i) input pairs")


def check_gaussian_ring_and_original_729_product_expansion():
    """All eight Gaussian basis triples plus exact original 729 pair sums."""
    basis = [ONE, I]
    for a, b, c in product(basis, repeat=3):
        assert mul(mul(a, b), c) == mul(a, mul(b, c))
        assert mul(a, add(b, c)) == add(mul(a, b), mul(a, c))
        assert mul(add(a, b), c) == add(mul(a, c), mul(b, c))
    for seed in range(3):
        rng = Random(8100 + seed)
        f = {k: (Fraction(rng.randrange(-8, 9), 7),
                 Fraction(rng.randrange(-8, 9), 7)) for k in K}
        g = {k: (Fraction(rng.randrange(-8, 9), 11),
                 Fraction(rng.randrange(-8, 9), 11)) for k in K}
        sum_f, sum_g = ZERO, ZERO
        for k in K:
            sum_f, sum_g = add(sum_f, f[k]), add(sum_g, g[k])
        ordered_sum = ZERO
        for p in K:
            for q in K:
                ordered_sum = add(ordered_sum, mul(f[p], g[q]))
        assert mul(sum_f, sum_g) == ordered_sum
    print("PASS: Q(i) eight ring basis triples and 3 full original 729-term expansions")

def check():
    check_gaussian_ring_and_original_729_product_expansion()
    check_one_axis_sampled_convolution()
    # Exact fourth-root orthogonality on all 64 group characters.
    residues = tuple(product(range(4), repeat=3))
    for delta in residues:
        total = sum_complex(chi(delta, x) for x in X)
        assert total == ((Fraction(64), Fraction(0)) if delta == (0, 0, 0) else ZERO)
    for seed in range(8):
        rng = Random(16000 + seed)
        f = {k: (Fraction(rng.randrange(-5, 6), 5),
                 Fraction(rng.randrange(-5, 6), 7)) for k in K}
        g = {k: (Fraction(rng.randrange(-5, 6), 5),
                 Fraction(rng.randrange(-5, 6), 7)) for k in K}
        assert sampled_product(f, g) == direct(f, g)
    # Three-point folding aliases a +2 quadratic product to retained -1.
    assert (1 + 1) % 3 == (-1) % 3
    # No other signed quadratic sum in [-2,2] aliases to a retained mode modulo 4.
    for k in (-1, 0, 1):
        assert [s for s in range(-2, 3) if (s - k) % 4 == 0] == [k]
    print('PASS: 64 exact Q(i) C4^3 characters, 8 arbitrary complex two-field profiles')
    print('PASS: sampled inverse/product/forward retains all 27 true integer coefficients')
    print('PASS: mod-3 alias witness and mod-4 retained-output uniqueness')


if __name__ == '__main__':
    check()
