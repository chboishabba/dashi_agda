"""Exact grounded Poisson coercivity certificate for original 3x3x3.

ATTRIBUTION: 369 ternary cube is existing DASHI work. This assistant-authored
arithmetic verification uses the classical cell-centred finite-volume
Dirichlet Laplacian; not physiological source evidence or Agda acceptance.
The zero-potential faces here are a chosen synthetic boundary case, not
the original source-selected electrode/reservoir model.
"""
from fractions import Fraction
from itertools import product

POINTS = tuple(product((-1, 0, 1), repeat=3))
INDEX = {p: k for k, p in enumerate(POINTS)}
BONDS = tuple(
    (INDEX[p], INDEX[tuple(p[k] + (k == axis) for k in range(3))])
    for p in POINTS for axis in range(3) if p[axis] < 1
)
FACE_MULTIPLICITIES = tuple(sum(1 for x in p if abs(x) == 1) for p in POINTS)
assert len(POINTS) == 27 and len(BONDS) == 54
assert sum(FACE_MULTIPLICITIES) == 54


def grounded_matrix(h=Fraction(1), epsilon=Fraction(1)):
    """A = epsilon/h^2 * (B B^T + 2 diag(exterior faces))."""
    h, epsilon = Fraction(h), Fraction(epsilon)
    if h <= 0 or epsilon <= 0:
        raise ValueError("positive mesh and permittivity required")
    A = [[Fraction(0) for _ in range(27)] for _ in range(27)]
    for a, b in BONDS:
        A[a][a] += 1
        A[b][b] += 1
        A[a][b] -= 1
        A[b][a] -= 1
    for i, count in enumerate(FACE_MULTIPLICITIES):
        A[i][i] += 2 * count
    return tuple(tuple(x * epsilon / (h * h) for x in row) for row in A)


def quadratic_energy(v, h=Fraction(1), epsilon=Fraction(1)):
    """Exact sum of nonnegative squares: v^T A v."""
    if len(v) != 27:
        raise ValueError("27 cell potentials required")
    v = tuple(Fraction(x) for x in v)
    h, epsilon = Fraction(h), Fraction(epsilon)
    if h <= 0 or epsilon <= 0:
        raise ValueError("positive mesh and permittivity required")
    internal = sum(((v[a] - v[b]) ** 2 for a, b in BONDS), Fraction(0))
    exterior = 2 * sum((m * x * x for m, x in zip(FACE_MULTIPLICITIES, v)),
                       Fraction(0))
    return epsilon * (internal + exterior) / (h * h)


def direct_quadratic(v, A):
    v = tuple(Fraction(x) for x in v)
    if len(v) != 27 or len(A) != 27:
        raise ValueError("dimension mismatch")
    return sum((v[i] * A[i][j] * v[j]
                for i in range(27) for j in range(27)), Fraction(0))


def exact_ldlt_pivots(A):
    """Unpivoted exact LDL decomposition; all positive pivots certify SPD."""
    n = len(A)
    if n != 27 or any(len(row) != n for row in A):
        raise ValueError("expected exact 27x27 matrix")
    L = [[Fraction(0) for _ in range(n)] for _ in range(n)]
    D = []
    for j in range(n):
        d = Fraction(A[j][j]) - sum(
            (L[j][k] ** 2 * D[k] for k in range(j)), Fraction(0))
        if d <= 0:
            raise ValueError(f"nonpositive pivot at {j}")
        D.append(d)
        L[j][j] = Fraction(1)
        for i in range(j + 1, n):
            numerator = Fraction(A[i][j]) - sum(
                (L[i][k] * D[k] * L[j][k] for k in range(j)),
                Fraction(0))
            L[i][j] = numerator / d
    return tuple(D)


def exact_poisson_solve(rho, h=Fraction(1), epsilon=Fraction(1)):
    """Unique rational grounded-Poisson solution for any rational rho."""
    if len(rho) != 27:
        raise ValueError("27 source charges required")
    A = grounded_matrix(h, epsilon)
    n = 27
    augmented = [list(A[i]) + [Fraction(rho[i])] for i in range(n)]
    for j in range(n):
        pivot = next((i for i in range(j, n) if augmented[i][j]), None)
        if pivot is None:
            raise ValueError("singular Poisson matrix")
        augmented[j], augmented[pivot] = augmented[pivot], augmented[j]
        scale = augmented[j][j]
        augmented[j] = [x / scale for x in augmented[j]]
        for i in range(n):
            if i == j:
                continue
            factor = augmented[i][j]
            if factor:
                augmented[i] = [
                    u - factor * v for u, v in zip(augmented[i], augmented[j])
                ]
    solution = tuple(row[n] for row in augmented)
    assert all(
        sum((A[i][j] * solution[j] for j in range(n)), Fraction(0))
        == Fraction(rho[i]) for i in range(n)
    )
    return solution


def certify_grounded_poisson():
    A = grounded_matrix()
    assert all(A[i][j] == A[j][i] for i in range(27) for j in range(27))
    pivots = exact_ldlt_pivots(A)
    assert all(x > 0 for x in pivots)
    assert quadratic_energy([1] * 27) == Fraction(108)
    assert direct_quadratic([1] * 27, A) == Fraction(108)
    return {"points": 27, "bonds": 54, "exterior_faces": 54,
            "strictly_positive_pivots": len(pivots)}


if __name__ == "__main__":
    print(certify_grounded_poisson())
