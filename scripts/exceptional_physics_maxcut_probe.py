from __future__ import annotations

from fractions import Fraction
from itertools import product
import numpy as np
import sympy as sp

P = 3
INV2 = 2
I3 = np.eye(3, dtype=int) % P


def mod(a):
    return np.asarray(a, dtype=int) % P


def tr(A):
    return int(np.trace(A) % P)


def det3(A):
    a = mod(A)
    return int((
        a[0, 0] * (a[1, 1] * a[2, 2] - a[1, 2] * a[2, 1])
        - a[0, 1] * (a[1, 0] * a[2, 2] - a[1, 2] * a[2, 0])
        + a[0, 2] * (a[1, 0] * a[2, 1] - a[1, 1] * a[2, 0])
    ) % P)


def inv_mat(A):
    A = mod(A)
    n = A.shape[0]
    aug = np.concatenate([A, np.eye(n, dtype=int)], axis=1) % P
    row = 0
    for col in range(n):
        pivot = next((r for r in range(row, n) if aug[r, col] % P), None)
        if pivot is None:
            raise ValueError("singular")
        aug[[row, pivot]] = aug[[pivot, row]]
        aug[row] = aug[row] * pow(int(aug[row, col]), -1, P) % P
        for r in range(n):
            if r != row and aug[r, col]:
                aug[r] = (aug[r] - aug[r, col] * aug[row]) % P
        row += 1
    return aug[:, n:] % P


def bullet(A, B):
    return INV2 * (A @ B + B @ A) % P


def bar(A):
    return INV2 * (tr(A) * I3 - A) % P


def cross(A, B):
    ab = bullet(A, B)
    coeff = (tr(A) * tr(B) - tr(ab)) % P
    return (
        ab
        - INV2 * tr(A) * B
        - INV2 * tr(B) * A
        + INV2 * coeff * I3
    ) % P


def jprod(x, y):
    A, B, C = x
    D, E, F = y
    return (
        (bullet(A, D) + bar(B @ F) + bar(E @ C)) % P,
        (bar(A) @ E + bar(D) @ B + INV2 * cross(C, F)) % P,
        (F @ bar(A) + C @ bar(D) + INV2 * cross(B, E)) % P,
    )


def same(x, y):
    return all(np.array_equal(mod(a), mod(b)) for a, b in zip(x, y))


def basis_element(s, i, j):
    out = [np.zeros((3, 3), dtype=int) for _ in range(3)]
    out[s][i, j] = 1
    return tuple(out)


BASIS = [
    basis_element(s, i, j)
    for s in range(3)
    for i in range(3)
    for j in range(3)
]
UNIT = (I3.copy(), np.zeros((3, 3), dtype=int), np.zeros((3, 3), dtype=int))


def square(x):
    return jprod(x, x)


def jordan_identity(x, y):
    return same(
        jprod(jprod(square(x), y), x),
        jprod(square(x), jprod(y, x)),
    )


def tits_norm(x):
    A, B, C = x
    return (det3(A) + det3(B) + det3(C) - tr(A @ B @ C)) % P


def random_x(rng):
    return tuple(rng.integers(0, 3, size=(3, 3), dtype=int) for _ in range(3))


def random_sl3(rng):
    while True:
        A = rng.integers(0, 3, size=(3, 3), dtype=int)
        d = det3(A)
        if d:
            A = A.copy()
            A[0, :] = A[0, :] * pow(d, -1, 3) % 3
            assert det3(A) == 1
            return A


def tri_action(g, x):
    A, B, C = g
    X, Y, Z = x
    return (
        A @ X @ inv_mat(B) % P,
        B @ Y @ inv_mat(C) % P,
        C @ Z @ inv_mat(A) % P,
    )


def product_support_counts():
    counts = {0: 0, 1: 0, 2: 0, "other": 0}
    for a in BASIS:
        for b in BASIS:
            z = jprod(a, b)
            nonzero = sum(int(v != 0) for block in z for v in block.flat)
            counts[nonzero if nonzero in (0, 1, 2) else "other"] += 1
    return counts


# E6 simple-root Cartan in the determinant-three labelling used by the finite
# quotient diagnostics.  Mod 3 its radical is one-dimensional; the first five
# simple coordinates form the selected complement.
E6_CARTAN = np.array([
    [2, 0, -1, 0, 0, 0],
    [0, 2, 0, -1, 0, 0],
    [-1, 0, 2, -1, 0, 0],
    [0, -1, -1, 2, -1, 0],
    [0, 0, 0, -1, 2, -1],
    [0, 0, 0, 0, -1, 2],
], dtype=int)
G5 = E6_CARTAN[:5, :5] % 3


def q5(x):
    x = np.array(x, dtype=int) % 3
    return int((INV2 * (x @ G5 @ x)) % 3)


NODES = list(product(range(3), repeat=3))
NODE_INDEX = {x: i for i, x in enumerate(NODES)}


def e6_chart_source():
    out = []
    for a, b, c in NODES:
        q = q5([a, b, c, 0, 0])
        out.append({0: 0, 1: 1, 2: -1}[q])
    return out


def torus_laplacian():
    n = len(NODES)
    L = sp.zeros(n, n)
    for x in NODES:
        i = NODE_INDEX[x]
        L[i, i] = 6
        for axis in range(3):
            for delta in (-1, 1):
                y = list(x)
                y[axis] = (y[axis] + delta) % 3
                L[i, NODE_INDEX[tuple(y)]] -= 1
    return L


def poisson_potential():
    rho = e6_chart_source()
    L = torus_laplacian()
    # Poisson plus mean-zero gauge fixing.
    M = L.col_join(sp.ones(1, 27))
    rhs = sp.Matrix(rho).col_join(sp.Matrix([0]))
    sol = list(sp.linsolve((M, rhs)))[0]
    return tuple(sp.Rational(v) for v in sol)


def lagrange3(coord, value):
    x = coord
    if value == -1:
        return x * (x - 1) / 2
    if value == 0:
        return 1 - x * x
    if value == 1:
        return x * (x + 1) / 2
    raise ValueError(value)


def continuum_phi():
    X, Y, Z = sp.symbols("x y z", real=True)
    sol = poisson_potential()
    expr = 0
    residue_to_balanced = {0: 0, 1: 1, 2: -1}
    for idx, (a, b, c) in enumerate(NODES):
        aa, bb, cc = residue_to_balanced[a], residue_to_balanced[b], residue_to_balanced[c]
        expr += (
            sol[idx]
            * lagrange3(X, aa)
            * lagrange3(Y, bb)
            * lagrange3(Z, cc)
        )
    return (X, Y, Z), sp.factor(sp.expand(expr))


def conformal_geometry():
    (x, y, z), phi = continuum_phi()
    coords = sp.symbols("t x y z", real=True)
    _, X, Y, Z = coords
    phi4 = phi.subs({x: X, y: Y, z: Z})
    Omega = 1 + phi4
    eta = sp.diag(-1, 1, 1, 1)
    g = sp.simplify(Omega**2) * eta
    ginv = sp.simplify(Omega**-2) * eta
    dim = 4
    Gamma = [[[
        sp.simplify(sp.Rational(1, 2) * sum(
            ginv[r, s] * (
                sp.diff(g[s, n], coords[m])
                + sp.diff(g[s, m], coords[n])
                - sp.diff(g[m, n], coords[s])
            )
            for s in range(dim)
        ))
        for n in range(dim)] for m in range(dim)] for r in range(dim)]
    Ric = sp.MutableDenseMatrix(dim, dim, [0] * 16)
    for mu in range(dim):
        for nu in range(dim):
            value = 0
            for rho in range(dim):
                value += (
                    sp.diff(Gamma[rho][mu][nu], coords[rho])
                    - sp.diff(Gamma[rho][mu][rho], coords[nu])
                )
                for sigma in range(dim):
                    value += (
                        Gamma[rho][rho][sigma] * Gamma[sigma][mu][nu]
                        - Gamma[rho][nu][sigma] * Gamma[sigma][mu][rho]
                    )
            Ric[mu, nu] = sp.simplify(value)
    Rsc = sp.simplify(sum(
        ginv[i, j] * Ric[i, j]
        for i in range(dim)
        for j in range(dim)
    ))
    Ein = sp.MutableDenseMatrix(dim, dim, [0] * 16)
    for i in range(dim):
        for j in range(dim):
            Ein[i, j] = sp.simplify(Ric[i, j] - sp.Rational(1, 2) * g[i, j] * Rsc)
    return coords, phi4, Omega, Gamma, Ric, Rsc, Ein


def hypercharge_spectrum():
    # Standard trinification 27:
    #   (3,bar3,1) + (bar3,1,3) + (1,3,bar3).
    Xf = [1, 1, -2]
    Xa = [-1, -1, 2]
    T3f = [1, -1, 0]
    T3a = [-1, 1, 0]
    ys = []
    labels = []
    for colour in range(3):
        for left in range(3):
            Y = Fraction(-1, 6) * Xa[left]
            ys.append(Y)
            labels.append(("Q", colour, left))
    for colour in range(3):
        for right in range(3):
            Y = Fraction(-1, 6) * Xf[right] + Fraction(-1, 2) * T3f[right]
            ys.append(Y)
            labels.append(("Qc", colour, right))
    for left in range(3):
        for right in range(3):
            Y = (
                Fraction(-1, 6) * Xf[left]
                + Fraction(-1, 6) * Xa[right]
                + Fraction(-1, 2) * T3a[right]
            )
            ys.append(Y)
            labels.append(("L", left, right))
    return ys, labels


def verify(seed=369):
    rng = np.random.default_rng(seed)

    assert all(same(jprod(UNIT, b), b) and same(jprod(b, UNIT), b) for b in BASIS)
    assert all(same(jprod(a, b), jprod(b, a)) for a in BASIS for b in BASIS)
    assert all(jordan_identity(a, b) for a in BASIS for b in BASIS)
    for _ in range(1000):
        assert jordan_identity(random_x(rng), random_x(rng))

    support = product_support_counts()
    assert support == {0: 414, 1: 291, 2: 24, "other": 0}

    for _ in range(500):
        g = (random_sl3(rng), random_sl3(rng), random_sl3(rng))
        x = random_x(rng)
        assert tits_norm(tri_action(g, x)) == tits_norm(x)

    ys, _ = hypercharge_spectrum()
    assert len(ys) == 27
    assert sum(ys, Fraction(0, 1)) == 0
    assert sum((y**3 for y in ys), Fraction(0, 1)) == 0
    for expected in (
        Fraction(1, 6),
        Fraction(-2, 3),
        Fraction(1, 3),
        Fraction(-1, 2),
        Fraction(1, 1),
    ):
        assert expected in ys

    rho = e6_chart_source()
    assert {v: rho.count(v) for v in (-1, 0, 1)} == {-1: 12, 0: 3, 1: 12}
    assert sum(rho) == 0
    phi = poisson_potential()
    assert sum(phi) == 0
    values = {v: phi.count(v) for v in set(phi)}
    assert values == {
        sp.Rational(-11, 54): 12,
        sp.Rational(2, 27): 6,
        sp.Rational(5, 27): 3,
        sp.Rational(13, 54): 6,
    }
    assert torus_laplacian() * sp.Matrix(phi) == sp.Matrix(rho)

    (x, y, z), pexpr = continuum_phi()
    residue_to_balanced = {0: 0, 1: 1, 2: -1}
    for idx, (a, b, c) in enumerate(NODES):
        subs = {
            x: residue_to_balanced[a],
            y: residue_to_balanced[b],
            z: residue_to_balanced[c],
        }
        assert sp.simplify(pexpr.subs(subs) - phi[idx]) == 0

    coords, _, _, _, _, Rsc, Ein = conformal_geometry()
    origin = {coords[0]: 0, coords[1]: 0, coords[2]: 0, coords[3]: 0}
    Ein0 = sp.Matrix([
        [sp.simplify(Ein[i, j].subs(origin)) for j in range(4)]
        for i in range(4)
    ])
    assert Ein0 != sp.zeros(4, 4)
    x100 = {coords[0]: 0, coords[1]: 1, coords[2]: 0, coords[3]: 0}
    assert sp.simplify(Rsc.subs(x100)) != 0

    # Literal public PhysioNet subject-1 row pair.  Official visualisation code
    # maps row k to k*20/60 minutes.  Row 120 is before LOC, row 487 after ROC.
    loc = 40.4093
    roc = 162.0028
    pre_k = 120
    post_k = 487
    assert pre_k * 20 / 60 < loc
    assert post_k * 20 / 60 > roc
    pre = np.array([
        4.76208579591535,
        4.18793376064776,
        3.90142621690925,
        0.0577025806511029,
        0.0146947577955462,
    ])
    post = np.array([
        1.69885090149667,
        1.51237995747815,
        1.55118912018814,
        0.0333121704836705,
        0.00364258367063108,
    ])
    assert np.all(pre > 0) and np.all(post > 0)
    log_distance = float(np.linalg.norm(np.log(pre) - np.log(post)))
    assert log_distance > 2.0

    return {
        "basis_pair_support": support,
        "poisson_values": values,
        "phi_polynomial": str(pexpr),
        "einstein_origin": Ein0,
        "ricci_scalar_x100": sp.simplify(Rsc.subs(x100)),
        "einstein00_x100": sp.simplify(Ein[0, 0].subs(x100)),
        "hypercharge_sum": sum(ys, Fraction(0, 1)),
        "hypercharge_cube_sum": sum((y**3 for y in ys), Fraction(0, 1)),
        "physionet_subject1_log_distance": log_distance,
    }


if __name__ == "__main__":
    output = verify()
    for key, value in output.items():
        print(f"{key}: {value}")
