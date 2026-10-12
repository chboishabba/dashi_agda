from fractions import Fraction as F


def mat_add(a, b):
    return [[a[i][j] + b[i][j] for j in range(4)] for i in range(4)]


def mat_scale(s, a):
    return [[s * a[i][j] for j in range(4)] for i in range(4)]


def verify():
    # Set alpha=1; the general result scales linearly at the stationary origin.
    eta = [
        [F(-1), 0, 0, 0],
        [0, F(1), 0, 0],
        [0, 0, F(1), 0],
        [0, 0, 0, F(1)],
    ]
    G = mat_scale(F(1, 27), [
        [12, 0, 0, 0],
        [0, -8, 0, 1],
        [0, 0, -8, 0],
        [0, 1, 0, -8],
    ])
    radiation = mat_scale(F(1, 27), [
        [3, 0, 0, 0],
        [0, 1, 0, 1],
        [0, 0, 1, 0],
        [0, 1, 0, 1],
    ])
    vacuum = mat_scale(F(-1, 3), eta)
    assert mat_add(radiation, vacuum) == G

    # Two counter-propagating radiation pairs: I_y=1/27 and I_plus=2/27.
    # A pair along unit n contributes I*diag(1, n n^T), with no momentum flux.
    pair_y = mat_scale(F(1, 27), [
        [1, 0, 0, 0],
        [0, 0, 0, 0],
        [0, 0, 1, 0],
        [0, 0, 0, 0],
    ])
    # 2/27 times n+=(x+z)/sqrt(2) gives spatial block (1/27)[[1,1],[1,1]].
    pair_plus = mat_scale(F(1, 27), [
        [2, 0, 0, 0],
        [0, 1, 0, 1],
        [0, 0, 0, 0],
        [0, 1, 0, 1],
    ])
    assert mat_add(pair_y, pair_plus) == radiation

    # Mixed trace of radiation vanishes: -T00 + T11 + T22 + T33 = 0.
    assert -radiation[0][0] + radiation[1][1] + radiation[2][2] + radiation[3][3] == 0

    return {
        "einstein_origin_alpha1": G,
        "vacuum_coefficient": F(1, 3),
        "radiation_origin_alpha1": radiation,
        "radiation_pair_intensities": (F(1, 27), F(2, 27)),
        "radiation_trace_zero": True,
        "exact_decomposition": True,
    }


if __name__ == "__main__":
    for k, v in verify().items():
        print(f"{k}: {v}")
